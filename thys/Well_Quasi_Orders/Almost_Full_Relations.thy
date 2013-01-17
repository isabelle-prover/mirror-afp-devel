(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Almost-Full Relations *}

theory Almost_Full_Relations
imports
  "~~/src/HOL/Library/Sublist"
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


subsection {* Basic Definitions and Facts *}

definition almost_full_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "almost_full_on P A \<equiv> \<forall>f. (\<forall>i. f i \<in> A) \<longrightarrow> good P f"

lemma almost_full_onD:
  fixes f :: "nat \<Rightarrow> 'a" and A :: "'a set"
  assumes "almost_full_on P A" and "\<And>i. f i \<in> A"
  obtains i j where "i < j" and "P (f i) (f j)"
  using assms unfolding almost_full_on_def good_def by blast

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

lemma almost_full_on_subset:
  "A \<subseteq> B \<Longrightarrow> almost_full_on P B \<Longrightarrow> almost_full_on P A"
  by (auto simp: almost_full_on_def)

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

text {*The homomorphic image of an almost full set is almost full.*}
lemma almost_full_on_hom:
  fixes h :: "'a \<Rightarrow> 'b"
  assumes hom: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; P x y\<rbrakk> \<Longrightarrow> Q (h x) (h y)"
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

text {*The monomorphic preimage of an almost full set is almost full.*}
lemma almost_full_on_mon:
  assumes mon: "\<And>x y. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> P x y = Q (h x) (h y)" "bij_betw h A B"
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

text {*Every total and well-founded relation is almost-full.*}
lemma total_on_and_wfp_on_imp_almost_full_on:
  assumes "total_on P A" and "wfp_on P A"
  shows "almost_full_on P\<^sup>=\<^sup>= A"
proof (rule ccontr)
  assume "\<not> almost_full_on P\<^sup>=\<^sup>= A"
  then obtain f :: "nat \<Rightarrow> 'a" where *: "\<And>i. f i \<in> A"
    and "\<forall>i j. i < j \<longrightarrow> \<not> P\<^sup>=\<^sup>= (f i) (f j)"
    unfolding almost_full_on_def good_def by blast
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


subsection {* Adding a Bottom Element to a Wqo Set *}

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

lemma almost_full_on_reflclp_option_less:
  assumes "almost_full_on (P\<^sup>=\<^sup>=) A"
  shows "almost_full_on ((option_less P)\<^sup>=\<^sup>=) A\<^sub>\<bottom>"
  using almost_full_on_with_bot [OF assms] by simp


subsection {* Disjoint Union of Wqo Sets *}

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

lemma almost_full_on_sum_less:
  assumes "almost_full_on (P\<^sup>=\<^sup>=) A" and "almost_full_on (Q\<^sup>=\<^sup>=) B"
  shows "almost_full_on ((sum_less P Q)\<^sup>=\<^sup>=) (A <+> B)"
  using almost_full_on_Plus [OF assms] by simp


subsection {* Dickson's Lemma *}

text {*When two sets are wqo, then their Cartesian product is wqo.*}

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

lemma almost_full_on_prod_less:
  assumes "almost_full_on (P1\<^sup>=\<^sup>=) A1" and "almost_full_on (P2\<^sup>=\<^sup>=) A2"
  shows "almost_full_on ((prod_less P1 P2)\<^sup>=\<^sup>=) (A1 \<times> A2)"
  using almost_full_on_Sigma [OF assms] by simp


subsection {* Embedding *}

lemma reflp_on_list_hembeq:
  shows "reflp_on (list_hembeq P) (lists A)"
  using list_hembeq_refl
  unfolding reflp_on_def by blast

lemma transp_on_list_hembeq:
  assumes "transp_on P A"
  shows "transp_on (list_hembeq P) (lists A)"
  using assms and list_hembeq_trans [of A P]
    unfolding transp_on_def by metis

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

lemma bad_imp_not_Nil:
  "bad (list_hembeq P) f \<Longrightarrow> f i \<noteq> []"
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


subsection {* Higman's Lemma *}

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

lemma almost_full_on_lists:
  assumes "almost_full_on P A"
  shows "almost_full_on (list_hembeq P) (lists A)"
    (is "almost_full_on ?P ?A")
proof -
  interpret list_mbs: mbs "\<lambda>_. ?P" suffix lists
  proof -
    show "mbs (\<lambda>_. ?P) suffix lists"
      by (unfold_locales) (auto
        simp: list_hembeq_suffix wfp_on_suffix suffix_lists
        intro: suffix_trans)
  qed
  {
    from reflp_on_list_hembeq have "reflp_on ?P ?A" .
  }
  note refl = this
  {
    have "\<forall>f. (\<forall>i. f i \<in> ?A) \<longrightarrow> good ?P f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain f where "\<forall>i. f i \<in> lists A" and "bad ?P f" by blast
      from list_mbs.mbs [OF this] obtain m where
        bad: "bad ?P m" and
        mb: "\<And>n. mbs.min_at (\<lambda>_. ?P) suffix A m n" and
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
            with suffix have "?P (?A i) (?A (f (j - f 0)))" using list_hembeq_suffixeq [of P] by blast
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
      from * have "P\<^sup>=\<^sup>= (a i) (a j)" and "?P (?B i) (?B j)"
        unfolding prod_le_def by auto
      from list_hembeq_Cons2 [OF this]
        have "?P (?A i) (?A j)" using a and hd_tl by auto
      with `i < j` and `bad ?P ?A` show False by (auto simp: good_def almost_full_on_def)
    qed
  }
  with trans show ?thesis unfolding almost_full_on_def by blast
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
  hence "P (f k) (f l)" using refl and * by (auto simp: reflp_on_def)
  with `k < l` show "good P f" by (auto simp: good_def)
qed

lemma eq_almost_full_on_finite_set:
  assumes "finite A"
  shows "almost_full_on (op =) A"
  using finite_almost_full_on [OF assms, of "op ="]
  by (auto simp: reflp_on_def)


subsection {*Natural Numbers*}

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

end

