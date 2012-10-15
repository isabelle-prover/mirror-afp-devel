(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Well-Quasi-Orders *}

theory Well_Quasi_Orders
imports
  "../Abstract-Rewriting/Seq"
  Restricted_Predicates
  "~~/src/HOL/Library/Ramsey"
  Minimal_Bad_Sequences
begin


subsection {* Auxiliary Lemmas *}

lemma funpow_non_decreasing:
  fixes f :: "'a::order \<Rightarrow> 'a"
  assumes "\<forall>i\<ge>n. f i \<ge> i"
  shows "(f ^^ i) n \<ge> n"
  using assms by (induct i) auto

lemma funpow_mono:
  assumes "\<forall>i\<ge>n::nat. f i > i" and "j > i"
  shows "(f ^^ j) n > (f ^^ i) n"
using assms(2)
proof (induct "j - i" arbitrary: i j)
  case 0 thus ?case by simp
next
  case (Suc m)
  then obtain j' where j: "j = Suc j'" by (cases j) auto
  show ?case
  proof (cases "i < j'")
    case True
    with Suc(1) [of j'] and Suc(2) [unfolded j]
      have "(f ^^ j') n > (f ^^ i) n" by simp
    moreover have "(f ^^ j) n > (f ^^ j') n"
    proof -
      have "(f ^^ j) n = f ((f ^^ j') n)" by (simp add: j)
      also have "\<dots> > (f ^^ j') n" using assms and funpow_non_decreasing [of n f j'] by force
      finally show ?thesis .
    qed
    ultimately show ?thesis by auto
  next
    case False
    with Suc have i: "i = j'" unfolding j by (induct i) auto
    show ?thesis unfolding i j using assms and funpow_non_decreasing [of n f j'] by force
  qed
qed


subsection {* Basic Definitions *}

definition almost_full_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "almost_full_on P A \<equiv> \<forall>f. (\<forall>i. f i \<in> A) \<longrightarrow> good P f"

lemma almost_full_on [Pure.intro]:
  "(\<And>f. \<forall>i. f i \<in> A \<Longrightarrow> good P f) \<Longrightarrow> almost_full_on P A"
  unfolding almost_full_on_def by blast

lemma almost_full_on_imp_reflp_on:
  assumes af: "almost_full_on P A"
  shows "reflp_on P A"
proof
  fix x
  assume "x \<in> A"
  let ?f = "\<lambda>i. x"
  have "\<forall>i. ?f i \<in> A" using `x \<in> A` by simp
  with af obtain i j :: nat where "i < j"
    and "P (?f i) (?f j)" by (auto simp: almost_full_on_def good_def)
  thus "P x x" by simp
qed

definition wqo_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "wqo_on P A \<equiv> transp_on P A \<and> almost_full_on P A"

lemma wqo_onI [Pure.intro]:
  "\<lbrakk>transp_on P A; \<And>f. \<forall>i. f i \<in> A \<Longrightarrow> good P f\<rbrakk> \<Longrightarrow> wqo_on P A"
  unfolding wqo_on_def almost_full_on_def by blast

lemma wqo_on_imp_reflp_on:
  "wqo_on P A \<Longrightarrow> reflp_on P A"
  using almost_full_on_imp_reflp_on by (auto simp: wqo_on_def)

lemma wqo_on_imp_transp_on:
  "wqo_on P A \<Longrightarrow> transp_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_good:
  "wqo_on P A \<Longrightarrow> \<forall>i. f i \<in> A \<Longrightarrow> good P f"
  by (auto simp: wqo_on_def almost_full_on_def)

lemma almost_full_on_subset:
  "A \<subseteq> B \<Longrightarrow> almost_full_on P B \<Longrightarrow> almost_full_on P A"
  by (auto simp: almost_full_on_def)

lemma wqo_on_subset:
  "A \<subseteq> B \<Longrightarrow> wqo_on P B \<Longrightarrow> wqo_on P A"
  using almost_full_on_subset [of A B P]
    and transp_on_subset [of A B P]
  unfolding wqo_on_def by blast

abbreviation strict where
  "strict P \<equiv> \<lambda>x y. P x y \<and> \<not> (P y x)"

lemma reflp_on_imp_irreflp_on_strict:
  "reflp_on P A \<Longrightarrow> irreflp_on (strict P) A"
  by (auto simp: reflp_on_def irreflp_on_def)

lemma transp_on_imp_transp_on_strict:
  "transp_on P A \<Longrightarrow> transp_on (strict P) A"
  unfolding transp_on_def by blast

abbreviation chain_on where
  "chain_on P f A \<equiv> \<forall>i. f i \<in> A \<and> P (f i) (f (Suc i))"

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

abbreviation incomparable where
  "incomparable P \<equiv> \<lambda>x y. \<not> P x y \<and> \<not> P y x"

abbreviation antichain_on where
  "antichain_on P f A \<equiv> \<forall>(i::nat) j. f i \<in> A \<and> (i < j \<longrightarrow> incomparable P (f i) (f j))"

text {*Almost full relations do not admit infinite antichains.*}
lemma almost_full_on_imp_not_antichain_on:
  assumes "almost_full_on P A"
  shows "\<not> antichain_on P f A"
proof
  assume *: "antichain_on P f A"
  hence "\<forall>i. f i \<in> A" by simp
  with assms have "good P f" by (auto simp: almost_full_on_def)
  then obtain i j where "i < j" and "P (f i) (f j)"
    unfolding good_def by auto
  moreover with * have "incomparable P (f i) (f j)" by auto
  ultimately show False by blast
qed

lemma wqo_on_imp_wfp_on:
  assumes "wqo_on P A"
  shows "wfp_on (strict P) A"
    (is "wfp_on ?P A")
proof (rule ccontr)
  have "transp_on ?P A" by (rule transp_on_imp_transp_on_strict [OF wqo_on_imp_transp_on [OF assms]])
  hence "transp_on ?P\<inverse>\<inverse> A" by (rule transp_on_converse)
  from reflp_on_imp_irreflp_on_strict [OF wqo_on_imp_reflp_on [OF assms]]
    have "irreflp_on ?P A" .
  assume "\<not> wfp_on ?P A"
  then obtain f where *: "\<forall>i. f i \<in> A"
    and **: "\<forall>i. ?P (f (Suc i)) (f i)" by (auto simp: wfp_on_def)
  from chain_on_transp_on_less [of f A"?P\<inverse>\<inverse>", OF _ `transp_on ?P\<inverse>\<inverse> A`] and * and **
    have "\<forall>i j. i < j \<longrightarrow> ?P (f j) (f i)" by auto
  with `irreflp_on ?P A` have "\<forall>i j. i < j \<longrightarrow> \<not> (P\<^sup>=\<^sup>= (f i) (f j))"
    unfolding irreflp_on_def using * by force
  hence "bad P f" by (auto simp: good_def)
  with * and assms show False unfolding wqo_on_def almost_full_on_def by blast
qed

text {*The homomorphic image of an almost full set is almost full.*}
lemma almost_full_on_hom:
  fixes h :: "'a \<Rightarrow> 'b"
  assumes hom: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q (h x) (h y)"
    and af: "almost_full_on P A"
  shows "almost_full_on Q (h ` A)"
proof
  fix f :: "'b seq"
  assume "\<forall>i. f i \<in> h ` A"
  hence "\<forall>i. \<exists>x. x \<in> A \<and> f i = h x" by (auto simp: image_def)
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
    hence "bad P g" by (auto simp: good_def)
    with af and * show False by (auto simp: good_def almost_full_on_def)
  qed
qed

text {*The homomorphic image of a wqo set is wqo.*}
lemma wqo_on_hom:
  assumes "transp_on Q (h ` A)"
    and "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> Q (h x) (h y)"
    and "wqo_on P A"
  shows "wqo_on Q (h ` A)"
  using assms and almost_full_on_hom unfolding wqo_on_def by blast

text {*The monomorphic preimage of an almost full set is almost full.*}
lemma almost_full_on_mon:
  assumes mon: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longleftrightarrow> Q (h x) (h y)" "bij_betw h A B"
    and af: "almost_full_on Q B"
  shows "almost_full_on P A"
proof
  fix f :: "'a seq"
  assume *: "\<forall>i. f i \<in> A"
  hence **: "\<forall>i. (h \<circ> f) i \<in> B" using mon by (auto simp: bij_betw_def)
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
    hence "bad Q (h \<circ> f)" by (auto simp: good_def)
    with af and ** show False by (auto simp: good_def almost_full_on_def)
  qed
qed

text {*The monomorphic preimage of a wqo set is wqo.*}
lemma wqo_on_mon:
  assumes trans: "transp_on P A"
    and mon: "\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longleftrightarrow> Q (h x) (h y)" "bij_betw h A B"
    and wqo: "wqo_on Q B"
  shows "wqo_on P A"
  using assms and almost_full_on_mon unfolding wqo_on_def by blast


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


subsection {* Adding a Bottom Element to a Wqo Set *}

fun
  option_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "option_le P None y = True" |
  "option_le P (Some x) None = False" |
  "option_le P (Some x) (Some y) = P x y"

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
    hence **: "\<And>i j. i < j \<Longrightarrow> \<not> ?P (f i) (f j)" by (auto simp: good_def)
    let ?f = "\<lambda>i. Option.the (f i)"
    have "\<forall>i j. i < j \<longrightarrow> \<not> P (?f i) (?f j)"
    proof (intro allI impI)
      fix i j :: nat
      assume "i < j"
      from ** [of i] and ** [of j] obtain x y where
        "f i = Some x" and "f j = Some y" by force
      with ** [OF `i < j`] show "\<not> P (?f i) (?f j)" by simp
    qed
    hence "bad P ?f" by (auto simp: good_def)
    moreover have "\<forall>i. ?f i \<in> A"
    proof
      fix i :: nat
      from ** [of i] obtain x where "f i = Some x" by force
      with * [THEN spec, of i] show "?f i \<in> A" by auto
    qed
    ultimately show False using assms by (auto simp: almost_full_on_def)
  qed
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


subsection {* Disjoint Union of Wqo Sets *}

fun
  sum_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
where
  "sum_le P Q (Inl x) (Inl y) = P x y" |
  "sum_le P Q (Inr x) (Inr y) = Q x y" |
  "sum_le P Q x y = False"

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
      hence "INFM i. i \<in> ?J" unfolding INFM_iff_infinite by simp
      then interpret infinitely_many "\<lambda>i. i \<in> ?J" by (unfold_locales) assumption
      let ?f = "\<lambda>i. Sum_Type.Projr (f (index i))"
      have ***: "\<forall>i. \<exists>x\<in>B. f (index i) = Inr x" using index_p by auto
      have B: "\<forall>i. ?f i \<in> B"
      proof
        fix i
        from *** obtain x where "x \<in> B" and "f (index i) = Inr x" by blast
        thus "?f i \<in> B" by simp
      qed
      {
        fix i j :: nat
        assume "i < j"
        hence "index i < index j" using index_ordered_less by auto
        with bad have not: "\<not> ?P (f (index i)) (f (index j))" by (auto simp: good_def)
        have "\<not> Q (?f i) (?f j)"
        proof
          assume "Q (?f i) (?f j)"
          assume "Q (?f i) (?f j)"
          moreover with *** obtain x y where "x \<in> B" and "y \<in> B"
            and "f (index i) = Inr x" and "f (index j) = Inr y" by blast
          ultimately have "?P (f (index i)) (f (index j))" by simp
          thus False using not by simp
        qed
      }
      hence "bad Q ?f" by (auto simp: good_def)
      moreover from `almost_full_on Q B` and B
        have "good Q ?f" by (auto simp: good_def almost_full_on_def)
      ultimately show False by blast
    next
      assume "infinite ?I"
      hence "INFM i. i \<in> ?I" unfolding INFM_iff_infinite by simp
      then interpret infinitely_many "\<lambda>i. i \<in> ?I" by (unfold_locales) assumption
      let ?f = "\<lambda>i. Sum_Type.Projl (f (index i))"
      have ***: "\<forall>i. \<exists>x\<in>A. f (index i) = Inl x" using index_p by auto
      have A: "\<forall>i. ?f i \<in> A"
      proof
        fix i
        from *** obtain x where "x \<in> A" and "f (index i) = Inl x" by blast
        thus "?f i \<in> A" by simp
      qed
      {
        fix i j :: nat
        assume "i < j"
        hence "index i < index j" using index_ordered_less by auto
        with bad have not: "\<not> ?P (f (index i)) (f (index j))" by (auto simp: good_def)
        have "\<not> P (?f i) (?f j)"
        proof
          assume "P (?f i) (?f j)"
          moreover with *** obtain x y where "x \<in> A" and "y \<in> A"
            and "f (index i) = Inl x" and "f (index j) = Inl y" by blast
          ultimately have "?P (f (index i)) (f (index j))" by simp
          thus False using not by simp
        qed
      }
      hence "bad P ?f" by (auto simp: good_def)
      moreover from `almost_full_on P A` and A
        have "good P ?f" by (auto simp: good_def almost_full_on_def)
      ultimately show False by blast
    qed
  qed
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

text {*When two sets are wqo, then their Cartesian product is wqo.*}

definition
  prod_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where
  "prod_le P1 P2 \<equiv> \<lambda>(p1, p2) (q1, q2). P1 p1 q1 \<and> P2 p2 q2"

text {*By Ramsey's Theorem every infinite sequence on which @{term "sup P Q"}
is transitive, contains a (monotone) infinite subsequence on which either
@{term P} is transitive or @{term Q} is transitive.*}
lemma trans_subseq:
  fixes f :: "'a seq"
  assumes *: "\<forall>i j. i < j \<longrightarrow> P (f i) (f j) \<or> Q (f i) (f j)"
  shows "\<exists>g::nat seq. (\<forall>i j. i < j \<longrightarrow> g i < g j) \<and>
    ((\<forall>i j. i < j \<longrightarrow> P (f (g i)) (f (g j))) \<or>
     (\<forall>i j. i < j \<longrightarrow> Q (f (g i)) (f (g j))))"
proof -
  def h \<equiv> "\<lambda>I. if (\<exists>i j. i \<in> I \<and> j \<in> I \<and> i < j \<and> P (f i) (f j)) then 0 else Suc 0"
  have inf: "infinite (UNIV::nat set)" by blast
  have "\<forall>i\<in>UNIV. \<forall>j\<in>UNIV. i \<noteq> j \<longrightarrow> h {i, j} < 2" by (auto simp: h_def)
  from Ramsey2 [OF inf this] obtain I :: "nat set" and n
    where "infinite I" and "n < 2" and **: "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> h {i, j} = n" by blast
  from `infinite I` have "INFM i. i \<in> I" unfolding INFM_iff_infinite by simp
  then interpret infinitely_many "\<lambda>i. i \<in> I" by (unfold_locales) assumption
  def [simp]: g \<equiv> "index"
  let ?f = "f \<circ> g"
  from `n < 2` have "n = 0 \<or> n = 1" by arith
  thus ?thesis
  proof
    assume [simp]: "n = 0"
    have "\<forall>i j. i < j \<longrightarrow> P (?f i) (?f j)"
    proof (intro allI impI)
      fix i j :: nat
      assume "i < j"
      with index_ordered_less have "g i < g j" by auto
      moreover have "g i \<in> I" and "g j \<in> I" using index_p by auto
      ultimately have "h {g i, g j} = 0" using ** by auto
      with `g i < g j` show "P (?f i) (?f j)"
        by (auto simp: h_def) (metis Suc_neq_Zero order_less_not_sym)
    qed
    thus ?thesis using index_ordered_less by auto
  next
    assume [simp]: "n = 1"
    have "\<forall>i j. i < j \<longrightarrow> Q (?f i) (?f j)"
    proof (intro allI impI)
      fix i j :: nat
      assume "i < j"
      with index_ordered_less have "g i < g j" by auto
      moreover have "g i \<in> I" and "g j \<in> I" using index_p by auto
      ultimately have "h {g i, g j} = 1" using ** by auto
      with `g i < g j` show "Q (?f i) (?f j)"
        using * by (auto simp: h_def) (metis Suc_n_not_n)
    qed
    thus ?thesis using index_ordered_less by auto
  qed
qed

lemma almost_full_on_Sigma:
  assumes "almost_full_on P1 A1" and "almost_full_on P2 A2"
  shows "almost_full_on (prod_le P1 P2) (A1 \<times> A2)"
    (is "almost_full_on ?P ?A")
proof (rule ccontr)
  assume "\<not> almost_full_on ?P ?A"
  then obtain f where f: "\<forall>i. f i \<in> ?A"
    and bad: "bad ?P f" by (auto simp: almost_full_on_def)
  let ?W = "\<lambda>x y. \<not> P1 (fst x) (fst y)"
  let ?B = "\<lambda>x y. \<not> P2 (snd x) (snd y)"
  from f have fst: "\<forall>i. fst (f i) \<in> A1" and snd: "\<forall>i. snd (f i) \<in> A2"
    by (metis SigmaE fst_conv, metis SigmaE snd_conv)
  from bad have "\<forall>i j. i < j \<longrightarrow> \<not> ?P (f i) (f j)" by (auto simp: good_def)
  hence "\<forall>i j. i < j \<longrightarrow> ?W (f i) (f j) \<or> ?B (f i) (f j)"
    unfolding prod_le_def by (metis (lifting, mono_tags) prod_case_beta)
  from trans_subseq [of ?W _ ?B, OF this]
    obtain g :: "nat seq" where mono: "\<forall>i j. i < j \<longrightarrow> g i < g j"
      and or: "(\<forall>i j. i < j \<longrightarrow> ?W (f (g i)) (f (g j))) \<or>
               (\<forall>i j. i < j \<longrightarrow> ?B (f (g i)) (f (g j)))"
      by blast
  from or show False
  proof
    assume "\<forall>i j. i < j \<longrightarrow> ?W (f (g i)) (f (g j))"
    hence "bad P1 (fst \<circ> f \<circ> g)" by (auto simp: good_def)
    with fst and assms(1) show False by (auto simp: almost_full_on_def)
  next
    assume "\<forall>i j. i < j \<longrightarrow> ?B (f (g i)) (f (g j))"
    hence "bad P2 (snd \<circ> f \<circ> g)" by (auto simp: good_def)
    with snd and assms(2) show False by (auto simp: almost_full_on_def)
  qed
qed

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

lemma infinite_wo_prefix:
  "infinite {j::nat. j > i}"
proof -
  {
  fix m have "\<exists>n>m. i < n"
  proof (cases "m > i")
    case True thus ?thesis by auto
  next
    case False
    hence "m \<le> i" by auto
    hence "Suc i > m" and "i < Suc i" by auto
    thus ?thesis by blast
  qed
  }
  thus ?thesis unfolding infinite_nat_iff_unbounded by auto
qed

lemma no_bad_of_special_shape_imp_good:
  assumes "\<not> (\<exists>f:: nat seq. (\<forall>i. f 0 \<le> f i) \<and> bad P (B \<circ> f))"
    and refl: "reflp_on P {B i | i. True}"
    and "\<forall>i. f i \<in> {B i | i. True}"
  shows "good P f"
proof (rule ccontr)
  assume "bad P f"
  from assms(3) have "\<forall>i. \<exists>j. f i = B j" by blast
  from choice [OF this] obtain g where "\<And>i. f i = B (g i)" by blast
  with `bad P f` have "bad P (B \<circ> g)" by (auto simp: good_def)
  have "\<forall>i. \<exists>j>i. g j \<ge> g 0"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain i::nat where "\<forall>j>i. \<not> (g j \<ge> g 0)" by auto
    hence *: "\<forall>j>i. g j < g 0" by auto
    let ?I = "{j. j > i}"
    from * have "\<forall>j>i. g j \<in> {..<g 0}" by auto
    hence "\<forall>j\<in>?I. g j \<in> {..<g 0}" by auto
    hence "g ` ?I \<subseteq> {..<g 0}" unfolding image_subset_iff by auto
    moreover have "finite {..<g 0}" by auto
    ultimately have 1: "finite (g ` ?I)" using finite_subset by blast
    have 2: "infinite ?I" by (rule infinite_wo_prefix)
    from pigeonhole_infinite [OF 2 1]
      obtain k where "k > i" and "infinite {j. j > i \<and> g j = g k}" by auto
    then obtain l where "k < l" and "g l = g k"
      unfolding infinite_nat_iff_unbounded by auto
    hence "P (B (g k)) (B (g l))" using refl by (auto simp: reflp_on_def)
    with `k < l` and `bad P (B \<circ> g)` show False by (auto simp: good_def)
  qed
  from choice [OF this] obtain h
    where "\<forall>i. (h i) > i" and *: "\<And>i. g (h i) \<ge> g 0" by blast
  hence "\<forall>i\<ge>0. (h i) > i" by auto
  from funpow_mono [OF this] have **: "\<And>i j. i < j \<Longrightarrow> (h ^^ i) 0 < (h ^^ j) 0" by auto
  let ?i = "\<lambda>i. (h ^^ i) 0"
  let ?f = "\<lambda>i. g (?i i)"
  have "\<forall>i. ?f i \<ge> ?f 0"
  proof
    fix i show "?f i \<ge> ?f 0" using * by (induct i) auto
  qed
  moreover have "bad P (B \<circ> ?f)"
  proof
    assume "good P (B \<circ> ?f)"
    then obtain i j where "i < j" and "P (B (?f i)) (B (?f j))" by (auto simp: good_def)
    hence "P (B (g (?i i))) (B (g (?i j)))" by simp
    moreover from ** [OF `i < j`] have "?i i < ?i j" .
    ultimately show False using `bad P (B \<circ> g)` by (auto simp: good_def)
  qed
  ultimately have "(\<forall>i. ?f i \<ge> ?f 0) \<and> bad P (B \<circ> ?f)" by auto
  hence "\<exists>f. (\<forall>i. f i \<ge> f 0) \<and> bad P (B \<circ> f)" by (rule exI [of _ ?f])
  with assms(1) show False by blast
qed


subsection {* Embedding *}

lemma reflp_on_emb:
  assumes "reflp_on P A"
  shows "reflp_on (emb P) (lists A)"
proof
  fix xs
  assume "xs \<in> lists A"
  with assms show "emb P xs xs"
    by (induct xs) (auto simp: reflp_on_def)
qed

lemma transp_on_emb:
  assumes "transp_on P A"
  shows "transp_on (emb P) (lists A)"
proof
  fix xs ys zs
  assume "emb P xs ys" and "emb P ys zs"
    and "xs \<in> lists A" and "ys \<in> lists A" and "zs \<in> lists A"
  thus "emb P xs zs"
  proof (induction arbitrary: zs)
    case emb_Nil show ?case by blast
  next
    case (emb_Cons xs ys y)
    from emb_ConsD [OF `emb P (y#ys) zs`] obtain us v vs
      where zs: "zs = us @ v # vs" and "P y v" and "emb P ys vs" by blast
    hence "emb P ys (v#vs)" by blast
    hence "emb P ys zs" unfolding zs by (rule emb_append2)
    from emb_Cons.IH [OF this] and emb_Cons.prems show ?case by simp
  next
    case (emb_Cons2 x y xs ys)
    from emb_ConsD [OF `emb P (y#ys) zs`] obtain us v vs
      where zs: "zs = us @ v # vs" and "P y v" and "emb P ys vs" by blast
    with emb_Cons2 have "emb P xs vs" by simp
    moreover have "P x v"
    proof -
      from zs and `zs \<in> lists A` have "v \<in> A" by auto
      moreover have "x \<in> A" and "y \<in> A" using emb_Cons2 by simp_all
      ultimately show ?thesis using `P x y` and `P y v` and assms
        unfolding transp_on_def by blast
    qed
    ultimately have "emb P (x#xs) (v#vs)" by blast
    thus ?case unfolding zs by (rule emb_append2)
  qed
qed

lemma emb_refl:
  assumes "reflp_on P (set xs)"
  shows "emb P xs xs"
  using reflp_on_emb [OF assms] by (auto simp: reflp_on_def)

lemma Nil_imp_good_emb [simp]:
  assumes "f i = []"
  shows "good (emb P) f"
proof (rule ccontr)
  assume "bad (emb P) f"
  moreover have "(emb P) (f i) (f (Suc i))"
    unfolding assms by auto
  ultimately show False
    unfolding good_def by auto
qed

lemma bad_imp_not_Nil:
  "bad (emb P) f \<Longrightarrow> f i \<noteq> []"
  by auto

lemma list_suffix_induct [case_names psuffix]:
  assumes "\<And>xs. (\<And>zs. suffix zs xs \<Longrightarrow> P zs) \<Longrightarrow> P xs"
  shows "P xs"
  using assms [unfolded suffix_def]
  by (induction_schema) (pat_completeness, lexicographic_order)

lemma reflp_on_suffixeq:
  "suffixeq xs ys \<Longrightarrow> reflp_on P (set ys) \<Longrightarrow> reflp_on P (set xs)"
  using reflp_on_subset [OF suffixeq_set_subset] .

lemma wf_suffix:
  "wf {(x, y). suffix x y}"
  unfolding wf_def using list_suffix_induct by auto

lemma wfp_on_suffix:
  "wfp_on suffix (lists A)"
  using wf_suffix [to_pred, unfolded wfp_on_UNIV [symmetric]]
  using wfp_on_subset [of "lists A" UNIV]
  by blast

interpretation list_mbs: mbs emb suffix lists
proof -
  show "mbs emb suffix lists"
    by (unfold_locales) (auto
      simp: emb_suffix wfp_on_suffix suffix_lists
      intro: suffix_trans)
qed


subsection {* Higman's Lemma *}

lemma almost_full_on_lists:
  assumes "almost_full_on P A"
  shows "almost_full_on (emb P) (lists A)"
    (is "almost_full_on ?P ?A")
proof -
  { from reflp_on_emb [OF almost_full_on_imp_reflp_on [OF assms]] have "reflp_on ?P ?A" . }
  note refl = this
  {
    have "\<forall>f. (\<forall>i. f i \<in> ?A) \<longrightarrow> good ?P f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain f where "\<forall>i. f i \<in> lists A" and "bad ?P f" by blast
      from list_mbs.mbs [OF this] obtain m where
        bad: "bad ?P m" and
        mb: "\<And>n. mbs.min_at emb suffix P m n" and
        in_lists: "\<And>i. m i \<in> lists A"
        by blast
      let ?A = m
      have non_empty: "\<forall>i. ?A i \<noteq> []" using bad and bad_imp_not_Nil by auto
      then obtain a as where a: "\<forall>i. hd (?A i) = a i \<and> tl (?A i) = as i" by force
      let ?B = "\<lambda>i. tl (?A i)"
      {
        assume "\<exists>f::nat seq. (\<forall>i. f i \<ge> f 0) \<and> bad ?P (?B \<circ> f)"
        then obtain f :: "nat seq" where ge: "\<forall>i. f i \<ge> f 0"
          and "bad ?P (?B \<circ> f)" by auto
        let ?C = "\<lambda>i. if i < f 0 then ?A i else ?B (f (i - f 0))"
        have [simp]: "\<And>i. i < f 0 \<Longrightarrow> ?C i = ?A i" by auto
        have [simp]: "\<And>i. f 0 \<le> i \<Longrightarrow> ?C i = ?B (f (i - f 0))" by auto
        have "bad ?P ?C"
        proof
          assume "good ?P ?C"
          then obtain i j where "i < j" and *: "?P (?C i) (?C j)" by (auto simp: good_def)
          {
            assume "j < f 0" with `i < j` and * have "?P (?A i) (?A j)" by simp
            with `i < j` and `bad ?P ?A` have False by (auto simp: good_def)
          } moreover {
            assume "f 0 \<le> i" with `i < j` and * have "?P (?B (f (i - f 0))) (?B (f (j - f 0)))" by simp
            moreover with `i < j` and `f 0 \<le> i` have "i - f 0 < j - f 0" by auto
            ultimately have False using `bad ?P (?B \<circ> f)` by (auto simp: good_def)
          } moreover {
            have suffix: "suffixeq (?B (f (j - f 0))) (?A (f (j - f 0)))" by simp
            assume "i < f 0" and "f 0 \<le> j"
            with * have "?P (?A i) (?B (f (j - f 0)))" by auto
            with suffix have "?P (?A i) (?A (f (j - f 0)))" using emb_suffixeq [of P] by blast
            moreover from ge [THEN spec [of _ "j - f 0"]] and `i < f 0` have "i < f (j - f 0)" by auto
            ultimately have False using `bad ?P ?A` by (auto simp: good_def)
          } ultimately show False by arith
        qed
        have "\<forall>i<f 0. ?C i = ?A i" by auto
        moreover have "suffix (?C (f 0)) (?A (f 0))" using non_empty by auto
        moreover have "\<forall>i\<ge>f 0. \<exists>j\<ge>f 0. suffix\<^sup>=\<^sup>= (?C i) (?A j)"
        proof (intro allI impI)
          fix i
          let ?i = "f (i - f 0)"
          assume "f 0 \<le> i"
          with `\<forall>i. f 0 \<le> f i` have "f 0 \<le> ?i" by auto
          from `f 0 \<le> i` have "?C i = ?B ?i" by auto
          with non_empty have "suffix\<^sup>=\<^sup>= (?C i) (?A ?i)" by auto
          thus "\<exists>j\<ge>f 0. suffix\<^sup>=\<^sup>= (?C i) (?A j)" using `f 0 \<le> ?i` by auto
        qed
        ultimately have "good ?P ?C"
          using mb [of "f 0", unfolded list_mbs.min_at_def, rule_format, of ?C] by blast
        with `bad ?P ?C` have False by blast
      }
      hence no_special_bad_seq: "\<not> (\<exists>f. (\<forall>i. f 0 \<le> f i) \<and> bad ?P (?B \<circ> f))" by blast
      let ?B' = "{?B i | i. True}"
      have subset: "?B' \<subseteq> lists A"
      proof
        fix B assume "B \<in> ?B'"
        then obtain i where B: "B = ?B i" by auto
        hence "suffixeq B (?A i)" by simp
        with in_lists [of i] show "B \<in> lists A" by (auto simp: suffixeq_def)
      qed
      have "almost_full_on ?P ?B'"
      proof
        from reflp_on_subset [OF subset refl] have refl: "reflp_on ?P ?B'" .
        fix f :: "'a list seq" assume "\<forall>i. f i \<in> ?B'"
        from no_bad_of_special_shape_imp_good [of ?P ?B f, OF no_special_bad_seq refl this]
          show "good ?P f" .
      qed
      let ?a' = "{a i | i. True}"
      have "?a' \<subseteq> A"
      proof
        fix x assume "x \<in> ?a'"
        then obtain i where x: "x = a i" by auto
        with a and non_empty have "a i \<in> set (?A i)" by (metis hd_in_set)
        with in_lists [of i] show "x \<in> A" unfolding x by auto
      qed
      from almost_full_on_subset [OF this assms]
        have "almost_full_on P ?a'" .
      from almost_full_on_Sigma [OF `almost_full_on P ?a'` `almost_full_on ?P ?B'`]
        have af: "almost_full_on (prod_le P ?P) (?a' \<times> ?B')" .
      let ?aB = "\<lambda>i. (a i, ?B i)"
      let ?P' = "prod_le P ?P"
      have "\<forall>i. ?aB i \<in> (?a' \<times> ?B')" by auto
      with af have "good ?P' ?aB" unfolding almost_full_on_def by auto
      then obtain i j where "i < j" and *: "?P' (?aB i) (?aB j)"
        by (auto simp: good_def almost_full_on_def)
     from hd_Cons_tl and non_empty
        have hd_tl: "hd (?A i) # tl (?A i) = ?A i"
          "hd (?A j) # tl (?A j) = ?A j" by auto
      from * have "P (a i) (a j)" and "?P (?B i) (?B j)"
        unfolding prod_le_def by auto
      from emb_Cons2 [OF this]
        have "?P (?A i) (?A j)" using a and hd_tl by auto
      with `i < j` and `bad ?P ?A` show False by (auto simp: good_def almost_full_on_def)
    qed
  }
  with trans show ?thesis unfolding wqo_on_def almost_full_on_def by blast
qed

lemma wqo_on_lists:
  assumes "wqo_on P A" shows "wqo_on (emb P) (lists A)"
  using assms and almost_full_on_lists and transp_on_emb by (auto simp: wqo_on_def)


subsection {* Special Case: Finite Sets *}

text {*Every reflexive relation on a finite set is almost full.*}
lemma finite_almost_full_on:
  fixes A :: "('a::finite) set"
  assumes refl: "reflp_on P A"
  shows "almost_full_on P A"
proof
  fix f::"'a::finite seq"
  assume *: "\<forall>i. f i \<in> A"
  let ?I = "UNIV::nat set"
  have "f ` ?I \<subseteq> A" using * by auto
  with finite [of A] and finite_subset have 1: "finite (f ` ?I)" by blast
  have "infinite ?I" by auto
  from pigeonhole_infinite [OF this 1]
    obtain k where "infinite {j. f j = f k}" by auto
  then obtain l where "k < l" and "f l = f k"
    unfolding infinite_nat_iff_unbounded by auto
  hence "P (f k) (f l)" using refl and * by (auto simp: reflp_on_def)
  with `k < l` show "good P f" by (auto simp: good_def)
qed

text {*Every reflexive and transitive relation on a finite set is a wqo.*}
lemma finite_wqo_on:
  fixes A :: "('a::finite) set"
  assumes refl: "reflp_on P A" and "transp_on P A"
  shows "wqo_on P A"
  using assms and finite_almost_full_on by (auto simp: wqo_on_def)

lemma finite_eq_wqo_on:
  "wqo_on (op =) (A::('a::finite) set)"
  using finite_wqo_on [of "op =" A]
  by (auto simp: reflp_on_def transp_on_def)

lemma wqo_on_lists_over_finite_sets:
  "wqo_on (emb (op =)) (UNIV::('a::finite) list set)"
  using wqo_on_lists [OF finite_eq_wqo_on [of UNIV]] by simp

end
