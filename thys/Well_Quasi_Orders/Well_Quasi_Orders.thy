(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Well-Quasi-Orders *}

theory Well_Quasi_Orders
imports "../Abstract-Rewriting/Seq"
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
    with Suc(1)[of j'] and Suc(2)[unfolded j]
      have "(f ^^ j') n > (f ^^ i) n" by simp
    moreover have "(f ^^ j) n > (f ^^ j') n"
    proof -
      have "(f ^^ j) n = f ((f ^^ j') n)" by (simp add: j)
      also have "\<dots> > (f ^^ j') n" using assms and funpow_non_decreasing[of n f j'] by force
      finally show ?thesis .
    qed
    ultimately show ?thesis by auto
  next
    case False
    with Suc have i: "i = j'" unfolding j by (induct i) auto
    show ?thesis unfolding i j using assms and funpow_non_decreasing[of n f j'] by force
  qed
qed


subsection {* Basic Definitions *}

definition reflp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "reflp_on P A \<equiv> \<forall>a\<in>A. P a a"

lemma reflp_onI [Pure.intro]:
  "(\<And>a. a \<in> A \<Longrightarrow> P a a) \<Longrightarrow> reflp_on P A"
  unfolding reflp_on_def by blast

definition transp_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "transp_on P A \<equiv> \<forall>a\<in>A. \<forall>b\<in>A. \<forall>c\<in>A. P a b \<and> P b c \<longrightarrow> P a c"

lemma transp_onI [Pure.intro]:
  "(\<And>a b c. \<lbrakk>a \<in> A; b \<in> A; c \<in> A; P a b; P b c\<rbrakk> \<Longrightarrow> P a c) \<Longrightarrow> transp_on P A"
  unfolding transp_on_def by blast

definition goodp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a seq \<Rightarrow> bool" where
  "goodp P f \<equiv> \<exists>i j. i < j \<and> P\<^sup>=\<^sup>= (f i) (f j)"

abbreviation bad where "bad P f \<equiv> \<not> goodp P f"

definition wqo_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "wqo_on P A \<equiv> reflp_on P A \<and> transp_on P A \<and> (\<forall>f. (\<forall>i. f i \<in> A) \<longrightarrow> goodp P f)"

lemma wqo_onI [Pure.intro]:
  "\<lbrakk>reflp_on P A; transp_on P A; \<And>f. \<forall>i. f i \<in> A \<Longrightarrow> goodp P f\<rbrakk> \<Longrightarrow> wqo_on P A"
  unfolding wqo_on_def by blast

lemma reflp_on_reflclp [simp]:
  assumes "reflp_on P A" and "a \<in> A" and "b \<in> A"
  shows "P\<^sup>=\<^sup>= a b = P a b"
  using assms by (auto simp: reflp_on_def)

lemma transp_on_tranclp:
  assumes "transp_on P A"
  shows "(\<lambda>x y. x \<in> A \<and> y \<in> A \<and> P x y)\<^sup>+\<^sup>+ a b \<longleftrightarrow> a \<in> A \<and> b \<in> A \<and> P a b"
    (is "?lhs = ?rhs")
  by (rule iffI, induction rule: tranclp.induct)
     (insert assms, auto simp: transp_on_def)

lemma wqo_on_imp_reflp_on:
  "wqo_on P A \<Longrightarrow> reflp_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_transp_on:
  "wqo_on P A \<Longrightarrow> transp_on P A"
  by (auto simp: wqo_on_def)

lemma wqo_on_imp_goodp:
  "wqo_on P A \<Longrightarrow> \<forall>i. f i \<in> A \<Longrightarrow> goodp P f"
  by (auto simp: wqo_on_def)

lemma reflp_on_converse:
  "reflp_on P A \<Longrightarrow> reflp_on P\<inverse>\<inverse> A"
  unfolding reflp_on_def by blast

lemma transp_on_converse:
  "transp_on P A \<Longrightarrow> transp_on P\<inverse>\<inverse> A"
  unfolding transp_on_def by blast


subsection {* Dickson's Lemma *}

text {*When two sets are wqo, then their Cartesian product is wqo.*}

definition
  prod_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where
  "prod_le P1 P2 \<equiv> \<lambda>(p1, p2) (q1, q2). P1 p1 q1 \<and> P2 p2 q2"

lemma wqo_on_Sigma:
  fixes A1 :: "'a set" and A2 :: "'b set"
  assumes "wqo_on P1 A1" and "wqo_on P2 A2"
  shows "wqo_on (prod_le P1 P2) (A1 \<times> A2)"
    (is "wqo_on ?P ?A")
proof
  show "reflp_on ?P ?A"
    using assms by (auto simp: wqo_on_def reflp_on_def prod_le_def)
next
  from assms have "transp_on P1 A1" and "transp_on P2 A2" by (auto simp: wqo_on_def)
  thus "transp_on ?P ?A" unfolding transp_on_def prod_le_def by blast
next
  fix g :: "('a \<times> 'b) seq"
  let ?p = "\<lambda>i. fst (g i)"
  let ?q = "\<lambda>i. snd (g i)"
  assume g: "\<forall>i. g i \<in> ?A"
  have p: "\<forall>i. ?p i \<in> A1"
  proof
    fix i
    from g have "g i \<in> ?A" by simp
    thus "?p i \<in> A1" by auto
  qed
  have q: "\<forall>i. ?q i \<in> A2"
  proof
    fix i
    from g have "g i \<in> ?A" by simp
    thus "?q i \<in> A2" by auto
  qed
  let ?T = "{m. \<forall>n>m. \<not> (P1 (?p m) (?p n))}"
  have "finite ?T"
  proof (rule ccontr)
    assume "infinite ?T"
    hence "INFM m. m \<in> ?T" unfolding INFM_iff_infinite by simp
    then interpret infinitely_many "\<lambda>m. m \<in> ?T" by (unfold_locales) assumption
    let ?p' = "\<lambda>i. ?p (index i)"
    have p': "\<forall>i. ?p' i \<in> A1" using p by auto
    have "bad P1 ?p'"
    proof
      assume "goodp P1 ?p'"
      then obtain i j :: nat where "i < j"
        and "P1\<^sup>=\<^sup>= (?p' i) (?p' j)" by (auto simp: goodp_def)
      hence "P1 (?p' i) (?p' j)"
        using p' and reflp_on_reflclp[OF wqo_on_imp_reflp_on[OF assms(1)]] by simp
      moreover from index_ordered_less[OF `i < j`] have "index j > index i" .
      moreover from index_p have "index i \<in> ?T" by simp
      ultimately show False by blast
    qed
    with assms(1) show False using p' by (auto simp: wqo_on_def)
  qed
  then obtain n where "\<forall>r\<ge>n. r \<notin> ?T"
    using infinite_nat_iff_unbounded_le[of "?T"] by auto
  hence "\<forall>i\<in>{n..}. \<exists>j>i. P1 (?p i) (?p j)" by blast
  with p have "\<forall>i\<in>{n..}. \<exists>j>i. ?p j \<in> A1 \<and> ?p i \<in> A1 \<and> P1 (?p i) (?p j)" by auto
  from bchoice[OF this] obtain f :: "nat seq"
    where 1: "\<forall>i\<ge>n. i < f i \<and> ?p i \<in> A1 \<and> ?p (f i) \<in> A1 \<and> P1 (?p i) (?p (f i))" by blast
  from stepfun_imp_chainp[of n f "\<lambda>x y. x \<in> A1 \<and> y \<in> A1 \<and> P1 x y" ?p, OF this]
    have chain: "chainp (\<lambda>x y. x \<in> A1 \<and> y \<in> A1 \<and> P1 x y) (\<lambda>i. ?p ((f^^i) n))" .
  let ?f = "\<lambda>i. (f^^i) n"
  from 1 have inc: "\<forall>i\<ge>n. f i > i" by simp
  from wqo_on_imp_goodp[OF assms(2), of "?q \<circ> ?f"] and q
    obtain i j where "\<And>i. ?q (?f i) \<in> A2" and "j > i" and "P2\<^sup>=\<^sup>= (?q (?f i)) (?q (?f j))"
    by (auto simp: goodp_def)
  hence "P2 (?q (?f i)) (?q (?f j))"
    using reflp_on_reflclp[OF wqo_on_imp_reflp_on[OF assms(2)]] by simp
  moreover from funpow_mono[OF inc `j > i`] have "?f j > ?f i" .
  moreover from chainp_imp_tranclp[of "\<lambda>x y. x \<in> A1 \<and> y \<in> A1 \<and> P1 x y", OF chain `j > i`]
    have "P1 (?p (?f i)) (?p (?f j))"
    unfolding transp_on_tranclp[OF wqo_on_imp_transp_on[OF assms(1)]] by simp
  ultimately have "\<exists>i j. j > i \<and> P1 (?p i) (?p j) \<and> P2 (?q i) (?q j)" by auto
  thus "goodp ?P g" by (auto simp: split_def goodp_def prod_le_def)
qed


subsection {* Higman's Lemma *}

definition set_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "set_le P A B \<equiv> \<exists>f. (\<forall>a\<in>A. f a \<in> B \<and> P a (f a)) \<and> inj_on f A"

lemma reflp_on_set_le_Pow:
  assumes "reflp_on P A"
  shows "reflp_on (set_le P) (Pow A)"
proof
  fix a
  assume "a \<in> Pow A"
  hence "a \<subseteq> A" by auto
  have "inj_on id a" by auto
  moreover from assms have "\<forall>x\<in>a. P (id x) x"
    using `a \<subseteq> A` unfolding id_def reflp_on_def by auto
  ultimately show "set_le P a a" unfolding set_le_def by auto
qed

lemma transp_on_set_le_Pow:
  assumes "transp_on P A"
  shows "transp_on (set_le P) (Pow A)"
    (is "transp_on ?P ?A")
proof
  fix a b c
  assume a: "a \<in> ?A" and b: "b \<in> ?A" and c: "c \<in> ?A"
    and "set_le P a b" and "set_le P b c"
  then obtain f g
    where f: "\<forall>x\<in>a. f x \<in> b \<and> P x (f x)" and inj_f: "inj_on f a"
      and g: "\<forall>x\<in>b. g x \<in> c \<and> P x (g x)" and inj_g: "inj_on g b"
    unfolding set_le_def by auto
  let ?f = "\<lambda>x. g (f x)"
  have"\<forall>x\<in>a. ?f x \<in> c \<and> P x (?f x)"
  proof
    fix x
    assume "x \<in> a"
    with f g have "f x \<in> b" and "?f x \<in> c" and "P x (f x)" and "P (f x) (?f x)" by auto
    moreover with assms and `x \<in> a`
      have "P x (?f x)" using a b c unfolding transp_on_def by blast
    ultimately show "?f x \<in> c \<and> P x (?f x)" by blast
  qed
  moreover have "inj_on ?f a" unfolding inj_on_def
  proof (intro ballI impI)
    fix x y
    assume "x \<in> a" and "y \<in> a" and "?f x = ?f y"
    with f have "f x \<in> b" and "f y \<in> b" by auto
    with inj_g and `?f x = ?f y` have "f x = f y" unfolding inj_on_def by simp
    with inj_f and `x \<in> a` and `y \<in> a` show "x = y" unfolding inj_on_def by simp
  qed
  ultimately show "set_le P a c" unfolding set_le_def by auto
qed

lemma set_finite_conv: "{set xs | xs. True} = {A. finite A}"
  by (auto dest: finite_list)

lemma reflp_on_set_conv:
  "reflp_on P {set xs | xs. True} = reflp_on (\<lambda>x y. P (set x) (set y)) UNIV"
  unfolding reflp_on_def by auto

lemma transp_on_set_conv:
  "transp_on P {set xs | xs. True} = transp_on (\<lambda>x y. P (set x) (set y)) UNIV"
  unfolding transp_on_def by auto

lemma set_le_refl:
  assumes "reflp_on P B"
  shows "set_le P B B"
  unfolding set_le_def
proof (intro exI conjI)
  show "inj_on id B" by auto
next
  show "\<forall>a\<in>B. id a \<in> B \<and> P a (id a)"
    using assms by (simp add: id_def reflp_on_def)
qed

lemma goodp_set_le_set:
  assumes "\<forall>f. (\<forall>i. f i \<in> {set xs | xs. True}) \<longrightarrow> goodp (set_le P) f"
    and "\<forall>i. f i \<in> UNIV"
    and "reflp_on P UNIV"
  shows "goodp (\<lambda>x y. set_le P (set x) (set y)) f"
proof -
  let ?f = "\<lambda>i. set (f i)"
  let ?A = "{set xs | xs. True}"
  let ?P = "\<lambda>x y. set_le P (set x) (set y)"
  from assms(2) have 1: "\<forall>i. ?f i \<in> ?A" by auto
  moreover from assms(1) have "\<forall>f. (\<forall>i. f i \<in> ?A) \<longrightarrow> goodp (set_le P) f" by (auto simp: wqo_on_def)
  ultimately have "goodp (set_le P) ?f" by auto
  then obtain i j where "i < j" and 2: "(set_le P)\<^sup>=\<^sup>= (?f i) (?f j)"
    unfolding goodp_def by auto
  from assms(3) have 3: "reflp_on P (?f j)"
    using 1 unfolding reflp_on_def by auto
  from 2 have "?P\<^sup>=\<^sup>= (f i) (f j)"
    using set_le_refl[OF 3] by auto
  with `i < j` show "goodp ?P f"
    unfolding goodp_def by auto
qed

lemma empty_set_le [intro]:
  "set_le P {} A"
  unfolding set_le_def by auto

lemma set_le_subset:
  "B \<subseteq> C \<Longrightarrow> set_le P A B \<Longrightarrow> set_le P A C"
  unfolding set_le_def by auto

lemma empty_imp_goodp_set_le [simp]:
  assumes "f i = {}"
  shows "goodp (set_le P) f"
proof (rule ccontr)
  assume "bad (set_le P) f"
  moreover have "(set_le P)\<^sup>=\<^sup>= (f i) (f (Suc i))"
    unfolding assms by auto
  ultimately show False
    unfolding goodp_def by auto
qed

lemma bad_imp_not_empty:
  "bad (set_le P) f \<Longrightarrow> f i \<noteq> {}"
  by auto

text {*Replace the elements of an infinite sequence, starting from a given
position, by those of another infinite sequence.*}
definition repl :: "nat \<Rightarrow> 'a seq \<Rightarrow> 'a seq \<Rightarrow> 'a seq" where
  "repl i f g \<equiv> \<lambda>j. if j \<ge> i then g j else f j"

lemma repl_0 [simp]:
  "repl 0 f g = g"
  by (simp add: repl_def)

lemma repl_simps [simp]:
  "j \<ge> i \<Longrightarrow> repl i f g j = g j"
  "j < i \<Longrightarrow> repl i f g j = f j"
  by (auto simp: repl_def)

lemma repl_ident [simp]:
   "repl i f f = f"
   by (auto simp: repl_def)

lemma repl_repl_ident [simp]:
  "repl n f (repl n g h) = repl n f h"
  by (auto simp: repl_def)

lemma repl_repl_ident' [simp]:
  "repl n (repl n f g) h = repl n f h"
  by (auto simp: repl_def)

lemma bad_set_le_repl:
  assumes "bad (set_le P) f"
    and "bad (set_le P) g"
    and "\<forall>i. reflp_on P (f i)"
    and "\<forall>i\<ge>n. \<exists>j\<ge>n. g i \<subseteq> f j"
  shows "bad (set_le P) (repl n f g)" (is "bad ?P ?f")
proof (rule ccontr)
  presume "goodp ?P ?f"
  then obtain i j where "i < j"
    and good: "?P\<^sup>=\<^sup>= (?f i) (?f j)" by (auto simp: goodp_def)
  {
    assume "j < n"
    with `i < j` and good have "?P\<^sup>=\<^sup>= (f i) (f j)" by simp
    with assms(1) have False using `i < j` by (auto simp: goodp_def)
  } moreover {
    assume "n \<le> i"
    with `i < j` and good have "i - n < j - n"
      and "?P \<^sup>=\<^sup>= (g i) (g j)" by auto
    with assms(2) have False by (auto simp: goodp_def)
  } moreover {
    assume "i < n" and "n \<le> j"
    with assms(4) obtain k where "k \<ge> n" and subset: "g j \<subseteq> f k" by blast
    from `i < j` and `i < n` and `n \<le> j` and good
      have "?P\<^sup>=\<^sup>= (f i) (g j)" by auto
    hence "?P\<^sup>=\<^sup>= (f i) (f k)"
    proof
      assume fi: "f i = g j"
      with set_le_refl[OF assms(3)[rule_format]]
        have "?P (f i) (f i)" by blast
      with set_le_subset[OF subset] show "?P\<^sup>=\<^sup>= (f i) (f k)" by (auto simp: fi)
    next
      assume "?P (f i) (g j)"
      with set_le_subset[OF subset] show "?P\<^sup>=\<^sup>= (f i) (f k)" by auto
    qed
    with `i < n` and `n \<le> k` and assms(1) have False by (auto simp: goodp_def)
  } ultimately show False using `i < j` by arith
qed simp

text {*A \emph{minimal bad prefix} of an infinite sequence, is a
prefix of its first @{text n} elements, such that every subsequence (of subsets)
starting with the same @{text n} elements is good, whenever the @{text n}-th
element is replaced by a proper subset of itself.*}
definition mbp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set seq \<Rightarrow> nat \<Rightarrow> bool" where
  "mbp P f n \<equiv>
    \<forall>g. (\<forall>i<n. g i = f i) \<and> g n \<subset> f n \<and> (\<forall>i\<ge>n. \<exists>j\<ge>n. g i \<subseteq> f j)
    \<longrightarrow> goodp (set_le P) g"

lemma reflp_on_subset:
  "A \<subseteq> B \<Longrightarrow> reflp_on P B \<Longrightarrow> reflp_on P A"
  by (auto simp: reflp_on_def)

lemma ex_repl_conv:
  "(\<exists>j\<ge>n. P (repl n f g j)) \<longleftrightarrow> (\<exists>j\<ge>n. P (g j))"
  by auto

lemma minimal_bad_element:
  fixes f :: "'a set seq"
  assumes "\<forall>i. finite (f i)"
    and "mbp P f n"
    and "bad (set_le P) f"
    and "\<forall>i. reflp_on P (f i)"
  shows "\<exists>M.
    (\<forall>i. finite (repl (Suc n) f M i)) \<and>
    (\<forall>i. reflp_on P (repl (Suc n) f M i)) \<and>
    (\<forall>i\<le>n. M i = f i) \<and>
    M (Suc n) \<subseteq> f (Suc n) \<and>
    (\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. (repl (Suc n) f M) i \<subseteq> f j) \<and>
    bad (set_le P) (repl (Suc n) f M) \<and>
    mbp P (repl (Suc n) f M) (Suc n)"
using assms(1)[rule_format, of "Suc n"] and assms
proof (induct "f (Suc n)" arbitrary: f n rule: finite_psubset_induct)
  case (psubset g)
  show ?case
  proof (cases "mbp P g (Suc n)")
    case True
    let ?g = "repl (Suc n) g g"
    have "\<forall>i. finite (?g i)" by (simp add: psubset)
    moreover have "\<forall>i. reflp_on P (?g i)" by (simp add: psubset)
    moreover have "\<forall>i\<le>n. ?g i = g i" by simp
    moreover have "g (Suc n) \<subseteq> g (Suc n)" by simp
    moreover have "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. (repl (Suc n) g g) i \<subseteq> g j" by auto
    moreover from `bad (set_le P) g`
      have "bad (set_le P) (repl (Suc n) g g)" by simp
    moreover from True have "mbp P (repl (Suc n) g g) (Suc n)" by simp
    ultimately show ?thesis by blast
  next
    case False
    then obtain h where less: "\<forall>i<Suc n. h i = g i"
      and subset: "h (Suc n) \<subset> g (Suc n)"
      and greater: "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. h i \<subseteq> g j"
      and bad: "bad (set_le P) h"
      unfolding mbp_def by blast
    let ?g = "repl (Suc n) g h"
    from subset have subset': "?g (Suc n) \<subset> g (Suc n)" by simp
    have mbp: "mbp P ?g n"
    proof (unfold mbp_def, intro allI impI, elim conjE)
      fix e
      assume "\<forall>i<n. e i = ?g i"
      hence 1: "\<forall>i<n. e i = g i" by auto
      assume "e n \<subset> ?g n"
      hence 2: "e n \<subset> g n" by auto
      assume *: "\<forall>i\<ge>n. \<exists>j\<ge>n. e i \<subseteq> ?g j"
      have 3: "\<forall>i\<ge>n. \<exists>j\<ge>n. e i \<subseteq> g j"
      proof (intro allI impI)
        fix i assume "n \<le> i"
        with * obtain j where "j \<ge> n"
          and **: "e i \<subseteq> ?g j" by auto
        show "\<exists>j\<ge>n. e i \<subseteq> g j"
        proof (cases "j \<le> n")
          case True with ** show ?thesis
            using `j \<ge> n` by auto
        next
          case False
          with `j \<ge> n` have "j \<ge> Suc n" by auto
          with ** have "e i \<subseteq> h j" by auto
          with greater obtain k where "k \<ge> Suc n"
            and "h j \<subseteq> g k" using `j \<ge> Suc n` by auto
          with `e i \<subseteq> h j` have "e i \<subseteq> g k" by auto
          moreover from `k \<ge> Suc n` have "k \<ge> n" by auto
          ultimately show ?thesis by blast
        qed
      qed
      from `mbp P g n`[unfolded mbp_def] and 1 and 2 and 3
        show "goodp (set_le P) e" by auto
    qed
    have bad: "bad (set_le P) ?g"
      using bad_set_le_repl[OF `bad (set_le P) g` `bad (set_le P) h`, of "Suc n",
      OF `\<forall>i. reflp_on P (g i)` greater] .
    have refl: "\<forall>i. reflp_on P (?g i)"
    proof
      fix i
      { assume "i < Suc n" hence "reflp_on P (?g i)" by (simp add: psubset) }
      moreover
      { assume "i \<ge> Suc n" hence "reflp_on P (?g i)"
        using psubset(6) and greater and reflp_on_subset by (simp) blast }
      ultimately show "reflp_on P (?g i)" by arith
    qed
    have finite: "\<forall>i. finite (?g i)"
    proof
      fix i
      { assume "i < Suc n" hence "finite (?g i)" by (simp add: psubset) }
      moreover
      { assume "i \<ge> Suc n" hence "finite (?g i)"
        using psubset(3) and greater and finite_subset by (simp) blast }
      ultimately show "finite (?g i)" by arith
    qed
    let ?g' = "repl (Suc n) g"
    from psubset(2)[of ?g n, OF subset' finite mbp bad refl] obtain M
      where "\<forall>i. finite (?g' M i)"
      and "\<forall>i. reflp_on P (?g' M i)"
      and "\<forall>i\<le>n. M i = g i"
      and "M (Suc n) \<subseteq> ?g' h (Suc n)"
      and *: "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. ?g' M i \<subseteq> h j"
      and "bad (set_le P) (?g' M)"
      and "mbp P (?g' M) (Suc n)"
      unfolding ex_repl_conv by auto
    moreover with subset have "M (Suc n) \<subseteq> g (Suc n)" by auto
    moreover have "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. ?g' M i \<subseteq> g j"
    proof (intro allI impI)
      fix i assume "Suc n \<le> i"
      with * obtain j where "j \<ge> Suc n" and "?g' M i \<subseteq> h j" by auto
      hence "j \<ge> Suc n" by auto
      from greater and `j \<ge> Suc n` obtain k where "k \<ge> Suc n"
        and "h j \<subseteq> g k" by auto
      with `?g' M i \<subseteq> h j` show "\<exists>j\<ge>Suc n. ?g' M i \<subseteq> g j" by blast
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma choice2:
  "\<forall>x y. P x y \<longrightarrow> (\<exists>z. Q x y z) \<Longrightarrow> \<exists>f. \<forall>x y. P x y \<longrightarrow> Q x y (f x y)"
  using bchoice[of "{(x, y). P x y}" "\<lambda>(x, y) z. Q x y z"] by force

fun minimal_bad_seq :: "('a seq \<Rightarrow> nat \<Rightarrow> 'a seq) \<Rightarrow> 'a seq \<Rightarrow> nat \<Rightarrow> 'a seq" where
  "minimal_bad_seq A f 0 = A f 0"
| "minimal_bad_seq A f (Suc n) = (
    let g = minimal_bad_seq A f n in
    repl (Suc n) g (A g n))"

lemma bad_imp_mbp:
  assumes "finite (f 0)" and "bad (set_le P) f"
  shows "\<exists>g. (\<forall>i. \<exists>j. g i \<subseteq> f j) \<and> mbp P g 0 \<and> bad (set_le P) g"
using assms
proof (induct "f 0" arbitrary: f rule: finite_psubset_induct)
  case (psubset g)
  show ?case
  proof (cases "mbp P g 0")
    case True with psubset show ?thesis by blast
  next
    case False
    then obtain h where less: "\<forall>i<0. h i = g i"
      and subset: "h 0 \<subset> g 0"
      and greater: "\<forall>i\<ge>0. \<exists>j\<ge>0. h i \<subseteq> g j"
      and bad: "bad (set_le P) h"
      unfolding mbp_def by auto
    from psubset(2)[of h, OF subset bad] obtain e
      where "\<forall>i. \<exists>j. e i \<subseteq> h j" and "mbp P e 0" and "bad (set_le P) e"
      by auto
    moreover with greater have "\<forall>i. \<exists>j. e i \<subseteq> g j" by force
    ultimately show ?thesis by blast
  qed
qed

lemma repl_1 [simp]:
  assumes "f 0 = g 0"
  shows "repl (Suc 0) f g = g"
proof
  fix i show "repl (Suc 0) f g i = g i"
    by (induct i) (simp_all add: assms)
qed

lemma bad_repl:
  assumes "\<forall>i. f i \<ge> f 0" and "\<forall>i j. i > j \<longrightarrow> f i > f j"
    and "bad P (repl (f 0) A B)" (is "bad P ?A")
  shows "bad P (B \<circ> f)"
proof
  assume "goodp P (B \<circ> f)"
  then obtain i j where "i < j" and "P\<^sup>=\<^sup>= (B (f i)) (B (f j))" by (auto simp: goodp_def)
  hence "P\<^sup>=\<^sup>= (?A (f i)) (?A (f j))" using assms by auto
  moreover from `i < j` have "f i < f j" using assms by auto
  ultimately show False using assms(3) by (auto simp: goodp_def)
qed

lemma iterated_subseq:
  assumes "\<forall>n>0::nat. \<forall>i\<ge>n. \<exists>j\<ge>n. g n i \<subseteq> g (n - 1) j"
    and "m \<le> n"
  shows "\<forall>i\<ge>n. \<exists>j\<ge>m. g n i \<subseteq> g m j"
using assms(2)
proof (induct "n - m" arbitrary: n)
  case 0 thus ?case by auto
next
  case (Suc k)
  then obtain n' where n: "n = Suc n'" by (cases n) auto
  with Suc have "k = n' - m" and "m \<le> n'" by auto
  have "n > 0" by (auto simp: n)
  show ?case
  proof (intro allI impI)
    fix i assume "i \<ge> n"
    with assms(1)[rule_format, OF `n > 0`] obtain j where "j \<ge> n"
      and "g (Suc n') i \<subseteq> g n' j" by (auto simp: n)
    with Suc(1)[OF `k = n' - m` `m \<le> n'`, THEN spec[of _ j]]
      obtain k where "k \<ge> m" and "g n' j \<subseteq> g m k" by (auto simp: n)
    with `g (Suc n') i \<subseteq> g n' j` have "g n i \<subseteq> g m k" by (auto simp: n)
    thus "\<exists>j\<ge>m. g n i \<subseteq> g m j" using `k \<ge> m` by blast
  qed
qed

lemma transp_on_subset:
  "A \<subseteq> B \<Longrightarrow> transp_on P B \<Longrightarrow> transp_on P A"
  by (auto simp: transp_on_def)

lemma wqo_on_subset:
  "A \<subseteq> B \<Longrightarrow> wqo_on P B \<Longrightarrow> wqo_on P A"
  using reflp_on_subset[of A B P]
    and transp_on_subset[of A B P]
  unfolding wqo_on_def by blast


lemma no_bad_of_special_shape_imp_goodp:
  assumes "\<not> (\<exists>f:: nat seq. (\<forall>i. f 0 \<le> f i) \<and> bad P (B \<circ> f))"
    and "\<forall>i. f i \<in> {B i | i. True}"
  shows "goodp P f"
proof (rule ccontr)
  assume "bad P f"
  from assms(2) have "\<forall>i. \<exists>j. f i = B j" by blast
  from choice[OF this] obtain g where "\<And>i. f i = B (g i)" by blast
  with `bad P f` have "bad P (B \<circ> g)" by (auto simp: goodp_def)
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
    have 2: "infinite ?I"
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
    from pigeonhole_infinite[OF 2 1]
      obtain k where "k > i" and "infinite {j. j > i \<and> g j = g k}" by auto
    then obtain l where "k < l" and "g l = g k"
      unfolding infinite_nat_iff_unbounded by auto
    hence "P\<^sup>=\<^sup>= (B (g k)) (B (g l))" by auto
    with `k < l` and `bad P (B \<circ> g)` show False by (auto simp: goodp_def)
  qed
  from choice[OF this] obtain h
    where "\<forall>i. (h i) > i" and *: "\<And>i. g (h i) \<ge> g 0" by blast
  hence "\<forall>i\<ge>0. (h i) > i" by auto
  from funpow_mono[OF this] have **: "\<And>i j. i < j \<Longrightarrow> (h ^^ i) 0 < (h ^^ j) 0" by auto
  let ?i = "\<lambda>i. (h ^^ i) 0"
  let ?f = "\<lambda>i. g (?i i)"
  have "\<forall>i. ?f i \<ge> ?f 0"
  proof
    fix i show "?f i \<ge> ?f 0" using * by (induct i) auto
  qed
  moreover have "bad P (B \<circ> ?f)"
  proof
    assume "goodp P (B \<circ> ?f)"
    then obtain i j where "i < j" and "P\<^sup>=\<^sup>= (B (?f i)) (B (?f j))" by (auto simp: goodp_def)
    hence "P\<^sup>=\<^sup>= (B (g (?i i))) (B (g (?i j)))" by simp
    moreover from **[OF `i < j`] have "?i i < ?i j" .
    ultimately show False using `bad P (B \<circ> g)` by (auto simp: goodp_def)
  qed
  ultimately have "(\<forall>i. ?f i \<ge> ?f 0) \<and> bad P (B \<circ> ?f)" by auto
  hence "\<exists>f. (\<forall>i. f i \<ge> f 0) \<and> bad P (B \<circ> f)" by (rule exI[of _ ?f])
  with assms(1) show False by blast
qed

lemma wqo_on_finite_subsets:
  fixes A :: "'a set"
  assumes "wqo_on P A"
  shows "wqo_on (set_le P) {B \<in> Pow A. finite B}"
    (is "wqo_on ?P ?A")
proof -
  {
    from reflp_on_set_le_Pow[OF wqo_on_imp_reflp_on[OF assms]]
      have "reflp_on ?P ?A" unfolding reflp_on_def by auto
  }
  note refl = this
  {
    from transp_on_set_le_Pow[OF wqo_on_imp_transp_on[OF assms]]
      have "transp_on ?P ?A" unfolding transp_on_def by auto
  }
  note trans = this
  {
    have "\<forall>f. (\<forall>i. f i \<in> ?A) \<longrightarrow> goodp ?P f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain f where "\<And>i. finite (f i)"
        and "\<And>i. f i \<subseteq> A" and "bad ?P f" by blast
      from bad_imp_mbp[of f, OF `finite (f 0)` `bad ?P f`] obtain g
        where "\<forall>i. \<exists>j. g i \<subseteq> f j"
        and "mbp P g 0"
        and "bad ?P g"
        by blast
      with `\<And>i. finite (f i)` and `\<And>i. f i \<subseteq> A`
        have "\<forall>i. finite (g i)" and "\<And>i. g i \<subseteq> A" using finite_subset by blast+
      with wqo_on_imp_reflp_on[OF assms]
        have "\<forall>i. reflp_on P (g i)" using reflp_on_subset by blast
      from minimal_bad_element[of _ P]
        have "\<forall>f n.
        (\<forall>i. finite (f i)) \<and>
        mbp P f n \<and>
        bad ?P f \<and>
        (\<forall>i. reflp_on P (f i)) \<longrightarrow>
        (\<exists>M.
          (\<forall>i. finite (repl (Suc n) f M i)) \<and>
          (\<forall>i. reflp_on P (repl (Suc n) f M i)) \<and>
          (\<forall>i\<le>n. M i = f i) \<and>
          M (Suc n) \<subseteq> f (Suc n) \<and>
          (\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. repl (Suc n) f M i \<subseteq> f j) \<and>
          bad ?P (repl (Suc n) f M) \<and>
          mbp P (repl (Suc n) f M) (Suc n))"
        (is "\<forall>f n. ?Q f n \<longrightarrow> (\<exists>M. ?Q' f n M)")
        by blast
      from choice2[OF this] obtain M
        where *[rule_format]: "\<forall>f n. ?Q f n \<longrightarrow> ?Q' f n (M f n)" by force
      let ?g = "minimal_bad_seq M g"
      let ?A = "\<lambda>i. ?g i i"
      have "\<forall>n. (n = 0 \<longrightarrow> (\<forall>i\<ge>n. \<exists>j\<ge>n. ?g n i \<subseteq> g j)) \<and> (n > 0 \<longrightarrow> (\<forall>i\<ge>n. \<exists>j\<ge>n. ?g n i \<subseteq> ?g (n - 1) j)) \<and> (\<forall>i\<le>n. mbp P (?g n) i) \<and> (\<forall>i\<le>n. ?A i = ?g n i) \<and> bad ?P (?g n) \<and> (\<forall>i. finite (?g n i)) \<and> (\<forall>i. reflp_on P (?g n i))"
      proof
        fix n
        show "(n = 0 \<longrightarrow> (\<forall>i\<ge>n. \<exists>j\<ge>n. ?g n i \<subseteq> g j)) \<and> (n > 0 \<longrightarrow> (\<forall>i\<ge>n. \<exists>j\<ge>n. ?g n i \<subseteq> ?g (n - 1) j)) \<and> (\<forall>i\<le>n. mbp P (?g n) i) \<and> (\<forall>i\<le>n. ?A i = ?g n i) \<and> bad ?P (?g n) \<and> (\<forall>i. finite (?g n i)) \<and> (\<forall>i. reflp_on P (?g n i))"
        proof (induction n)
          case 0
          have "\<forall>i. finite (g i)" by fact
          moreover have "mbp P g 0" by fact
          moreover have "bad ?P g" by fact
          moreover have "\<forall>i. reflp_on P (g i)" by fact
          ultimately
            have [simp]: "M g 0 0 = g 0" and "M g 0 (Suc 0) \<subseteq> g (Suc 0)"
            and "bad ?P (M g 0)" and "mbp P (M g 0) (Suc 0)"
            and **: "\<forall>i\<ge>Suc 0. \<exists>j\<ge>Suc 0. M g 0 i \<subseteq> g j"
            using *[of g 0] by auto
          moreover have "mbp P (M g 0) 0"
          proof (unfold mbp_def, intro allI impI, elim conjE)
            fix e :: "'a set seq"
            presume "e 0 \<subset> g 0" and *: "\<forall>i. \<exists>j\<ge>0. e i \<subseteq> M g 0 j"
            have "\<forall>i. \<exists>j\<ge>0::nat. e i \<subseteq> g j"
            proof (intro allI impI)
              fix i
              from * obtain j where "j \<ge> 0" and "e i \<subseteq> M g 0 j" by auto
              show "\<exists>j\<ge>0. e i \<subseteq> g j"
              proof (cases "j = 0")
                case True
                with `e i \<subseteq> M g 0 j` have "e i \<subseteq> g 0" by auto
                thus ?thesis by auto
              next
                case False
                hence "j \<ge> Suc 0" by auto
                with ** obtain k where "k \<ge> Suc 0" and "M g 0 j \<subseteq> g k" by auto
                with `e i \<subseteq> M g 0 j` have "e i \<subseteq> g k" by simp
                moreover with `k \<ge> Suc 0` have "k \<ge> 0" by auto
                ultimately show ?thesis by blast
              qed
            qed
            with `mbp P g 0`[unfolded mbp_def]
            show "goodp ?P e" using `e 0 \<subset> g 0` by (simp add: mbp_def)
          qed auto
          moreover have "\<forall>i. finite (M g 0 i)"
          proof
            fix i
            show "finite (M g 0 i)"
            proof (cases "i \<le> Suc 0")
              case False
              hence "i \<ge> Suc 0" by auto
              with ** obtain j where "j \<ge> Suc 0" and "M g 0 i \<subseteq> g j" by auto
              with `\<forall>i. finite (g i)` and finite_subset show ?thesis by blast
            next
              case True
              hence "i = 0 \<or> i = Suc 0" by auto
              thus ?thesis
              proof
                assume "i = 0" with `\<forall>i. finite (g i)` show ?thesis by auto
              next
                assume "i = Suc 0" with `M g 0 (Suc 0) \<subseteq> g (Suc 0)` and `\<forall>i. finite (g i)`
                  and finite_subset show ?thesis by auto
              qed
            qed
          qed
          moreover have "\<forall>i. reflp_on P (M g 0 i)"
          proof
            fix i
            show "reflp_on P (M g 0 i)"
            proof (cases "i \<le> Suc 0")
              case False
              hence "i \<ge> Suc 0" by auto
              with ** obtain j where "j \<ge> Suc 0" and "M g 0 i \<subseteq> g j" by auto
              with `\<forall>i. reflp_on P (g i)` and reflp_on_subset show ?thesis by blast
            next
              case True
              hence "i = 0 \<or> i = Suc 0" by auto
              thus ?thesis
              proof
                assume "i = 0" with `\<forall>i. reflp_on P (g i)` show ?thesis by auto
              next
                assume "i = Suc 0" with `\<forall>i. reflp_on P (g i)` and `M g 0 (Suc 0) \<subseteq> g (Suc 0)`
                  and reflp_on_subset show ?thesis by blast
              qed
            qed
          qed
          moreover have "\<forall>i\<ge>0. \<exists>j\<ge>0. ?g 0 i \<subseteq> g j"
          proof (intro allI impI)
            fix i::nat
            assume "i \<ge> 0"
            hence "i = 0 \<or> i \<ge> Suc 0" by auto
            thus "\<exists>j\<ge>0. ?g 0 i \<subseteq> g j"
            proof
              assume "i \<ge> Suc 0"
              with ** obtain j where "j \<ge> Suc 0" and "?g 0 i \<subseteq> g j" by auto
              moreover from this have "j \<ge> 0" by auto
              ultimately show "?thesis" by auto
            next
              assume "i = 0"
              hence "?g 0 i \<subseteq> g 0" by auto
              thus ?thesis by blast
            qed
          qed
          ultimately show ?case by simp
        next
          case (Suc n)
          with *[of "?g n" n]
            have "\<forall>i. finite (?g (Suc n) i)"
            and "\<forall>i. reflp_on P (?g (Suc n) i)"
            and eq: "\<forall>i\<le>n. ?A i = ?g n i"
            and subset: "?g (Suc n) (Suc n) \<subseteq> ?g n (Suc n)"
            and subseq: "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. ?g (Suc n) i \<subseteq> ?g n j"
            and "bad ?P (?g (Suc n))"
            and mbp: "mbp P (?g (Suc n)) (Suc n)"
            by (simp_all add: Let_def)
          moreover have *: "\<forall>i\<le>Suc n. ?A i = ?g (Suc n) i"
          proof (intro allI impI)
            fix i assume "i \<le> Suc n"
            show "?A i = ?g (Suc n) i"
            proof (cases "i = Suc n")
              assume "i = Suc n"
              thus ?thesis by simp
            next
              assume "i \<noteq> Suc n"
              with `i \<le> Suc n` have "i < Suc n" by auto
              thus ?thesis by (simp add: Let_def eq)
            qed
          qed
          moreover have "\<forall>i\<le>Suc n. mbp P (?g (Suc n)) i"
          proof (intro allI impI)
            fix i assume "i \<le> Suc n"
            show "mbp P (?g (Suc n)) i"
            proof (cases "i = Suc n")
              case True with mbp show ?thesis by simp
            next
              case False with `i \<le> Suc n` have le: "i \<le> Suc n" "i \<le> n" by auto
              show ?thesis
              proof (unfold mbp_def, intro allI impI, elim conjE)
                fix e
                note * = *[rule_format, symmetric] eq[rule_format, symmetric]
                assume "\<forall>i'<i. e i' = ?g (Suc n) i'"
                hence 1: "\<forall>i'<i. e i' = ?g n i'" using * and le by auto
                assume "e i \<subset> ?g (Suc n) i"
                hence 2: "e i \<subset> ?g n i" using * and le by simp
                assume **: "\<forall>j\<ge>i. \<exists>k\<ge>i. e j \<subseteq> ?g (Suc n) k"
                have 3: "\<forall>j\<ge>i. \<exists>k\<ge>i. e j \<subseteq> ?g n k"
                proof (intro allI impI)
                  fix j assume "i \<le> j"
                  with ** obtain k where "k \<ge> i" and "e j \<subseteq> ?g (Suc n) k" by blast
                  show "\<exists>k\<ge>i. e j \<subseteq> ?g n k"
                  proof (cases "k \<le> n")
                    case True with `e j \<subseteq> ?g (Suc n) k`
                      have "e j \<subseteq> ?g n k" using * by auto
                    thus ?thesis using `k \<ge> i` by auto
                  next
                    case False hence "k \<ge> Suc n" by auto
                    with subseq obtain l where "l \<ge> Suc n"
                      and "?g (Suc n) k \<subseteq> ?g n l" by blast
                    with `e j \<subseteq> ?g (Suc n) k` have "e j \<subseteq> ?g n l" by auto
                    moreover from `i \<le> Suc n` and `l \<ge> Suc n` have "l \<ge> i" by auto
                    ultimately show ?thesis by blast
                  qed
                qed
                from 1 2 3 and Suc[THEN conjunct2, THEN conjunct2] and `i \<le> n`
                show "goodp ?P e" unfolding mbp_def by blast
              qed
            qed
          qed
          ultimately show ?case by simp
        qed
      qed
      hence 1: "\<forall>n. \<forall>i\<le>n. mbp P (?g n) i"
        and 2: "\<forall>n. \<forall>i\<le>n. ?A i = ?g n i"
        and 3: "\<forall>n. bad ?P (?g n)"
        and 4: "\<forall>n. \<forall>i. finite (?g n i)"
        and 5: "\<forall>n. \<forall>i. reflp_on P (?g n i)"
        and 6: "\<forall>i\<ge>0. \<exists>j\<ge>0. ?g 0 i \<subseteq> g j"
        and 7: "\<forall>n>0. \<forall>i\<ge>n. \<exists>j\<ge>n. ?g n i \<subseteq> ?g (n - 1) j"
        by auto
      have ex_subset: "\<forall>n. \<forall>i. \<exists>j. ?g n i \<subseteq> g j"
      proof
        fix n show "\<forall>i. \<exists>j. ?g n i \<subseteq> g j"
        proof (induct n)
          case 0 with 6 show ?case by simp
        next
          case (Suc n)
          show ?case
          proof
            fix i
            have "i < Suc n \<or> i \<ge> Suc n" by auto
            thus "\<exists>j. ?g (Suc n) i \<subseteq> g j"
            proof
              assume "i < Suc n" hence "i \<le> Suc n" and "i \<le> n" by auto
              from `i \<le> Suc n` have "?g (Suc n) i = ?g i i" using 2 by auto
              moreover from `i \<le> n` have "?g n i = ?g i i" using 2 by auto
              ultimately have "?g (Suc n) i = ?g n i" by auto
              with Suc show ?thesis by blast
            next
              assume "i \<ge> Suc n"
              with 7[THEN spec[of _ "Suc n"]]
                obtain j where "j \<ge> Suc n" and "?g (Suc n) i \<subseteq> ?g n j" by auto
              moreover from Suc obtain k where "?g n j \<subseteq> g k" by blast
              ultimately show ?thesis by blast
            qed
          qed
        qed
      qed
      have bad: "bad ?P ?A"
      proof
        assume "goodp ?P ?A"
        then obtain i j :: nat where "i < j"
          and "?P\<^sup>=\<^sup>= (?g i i) (?g j j)" unfolding goodp_def by auto
        moreover with 2[rule_format, of i j]
          have "?P\<^sup>=\<^sup>= (?g j i) (?g j j)" by auto
        ultimately have "goodp ?P (?g j)" unfolding goodp_def by blast
        with 3 show False by auto
      qed
      have "\<forall>i. \<exists>a. a \<in> ?A i" using bad and bad_imp_not_empty[of P ?A] by auto
      from choice[OF this] obtain a where a: "\<forall>i. a i \<in> ?A i" by auto
      let ?B = "\<lambda>i. ?A i - {a i}"
      {
        assume "\<exists>f::nat seq. (\<forall>i. f i \<ge> f 0) \<and> bad ?P (?B \<circ> f)"
        then obtain f :: "nat seq" where ge: "\<forall>i. f i \<ge> f 0"
          and "bad ?P (?B \<circ> f)" by auto
        let ?C = "\<lambda>i. if i < f 0 then ?A i else ?B (f (i - f 0))"
        have [simp]: "\<And>i. i < f 0 \<Longrightarrow> ?C i = ?A i" by auto
        have [simp]: "\<And>i. f 0 \<le> i \<Longrightarrow> ?C i = ?B (f (i - f 0))" by auto
        have "bad ?P ?C"
        proof
          assume "goodp ?P ?C"
          then obtain i j where "i < j" and *: "?P\<^sup>=\<^sup>= (?C i) (?C j)" by (auto simp: goodp_def)
          {
            assume "j < f 0" with `i < j` and * have "?P\<^sup>=\<^sup>= (?A i) (?A j)" by simp
            with `i < j` and `bad ?P ?A` have False by (auto simp: goodp_def)
          } moreover {
            assume "f 0 \<le> i" with `i < j` and * have "?P\<^sup>=\<^sup>= (?B (f (i - f 0))) (?B (f (j - f 0)))" by simp
            moreover with `i < j` and `f 0 \<le> i` have "i - f 0 < j - f 0" by auto
            ultimately have False using `bad ?P (?B \<circ> f)` by (auto simp: goodp_def)
          } moreover {
            have subset: "?B (f (j - f 0)) \<subseteq> ?A (f (j - f 0))" using a by auto
            assume "i < f 0" and "f 0 \<le> j"
            with * have "?P\<^sup>=\<^sup>= (?A i) (?B (f (j - f 0)))" by auto
            hence "?P (?A i) (?B (f (j - f 0))) \<or> ?A i = ?B (f (j - f 0))" by simp
            hence False
            proof
              assume "?P (?A i) (?B (f (j - f 0)))"
              with subset have "?P (?A i) (?A (f (j - f 0)))" using set_le_subset[of _ _ P] by blast
              moreover from ge[THEN spec[of _ "j - f 0"]] and `i < f 0` have "i < f (j - f 0)" by auto
              ultimately show ?thesis using `bad ?P ?A` by (auto simp: goodp_def)
            next
              from `\<forall>i. reflp_on P (g i)` and ex_subset and reflp_on_subset
                have "reflp_on P (?A i)" by blast
              assume "?A i = ?B (f (j - f 0))"
              with subset have "?A i \<subseteq> ?A (f (j - f 0))" by auto
              moreover have "?P (?A i) (?A i)" using set_le_refl[OF `reflp_on P (?A i)`] .
              ultimately have "?P (?A i) (?A (f (j - f 0)))" using set_le_subset by blast
              moreover from ge[THEN spec[of _ "j - f 0"]] and `i < f 0` have "i < f (j - f 0)" by auto
              ultimately show ?thesis using `bad ?P ?A` by (auto simp: goodp_def)
            qed
          } ultimately show False by arith
        qed
        have "\<forall>i<f 0. ?C i = ?g (f 0) i" using 2 by auto
        moreover have "?C (f 0) \<subset> ?g (f 0) (f 0)" using a by auto
        moreover have "\<forall>i\<ge>f 0. \<exists>j\<ge>f 0. ?C i \<subseteq> ?g (f 0) j"
        proof (intro allI impI)
          fix i
          let ?i = "f (i - f 0)"
          assume "f 0 \<le> i"
          with `\<forall>i. f 0 \<le> f i` have "f 0 \<le> ?i" by auto
          from `f 0 \<le> i` have "?C i = ?B ?i" by auto
          with a have "?C i \<subseteq> ?g ?i ?i" by auto
          from iterated_subseq[OF 7, of "f 0" "?i", THEN spec[of _ "?i"], OF `f 0 \<le> ?i`]
            obtain j where "j \<ge> f 0" and "?g ?i ?i \<subseteq> ?g (f 0) j" by blast
          with `?C i \<subseteq> ?g ?i ?i`
            show "\<exists>j\<ge>f 0. ?C i \<subseteq> ?g (f 0) j" by auto
        qed
        ultimately have "goodp ?P ?C"
          using 1[rule_format, of "f 0", OF le_refl, unfolded mbp_def] by auto
        with `bad ?P ?C` have False by blast
      }
      hence no_index: "\<not> (\<exists>f. (\<forall>i. f 0 \<le> f i) \<and> bad ?P (?B \<circ> f))" by blast
      let ?B' = "{?B i | i. True}"
      have subset: "?B' \<subseteq> {B \<in> Pow A. finite B}"
      proof
        fix B assume "B \<in> ?B'"
        then obtain i where B: "B = ?B i" by auto
        hence "B \<subseteq> ?A i" using a by auto
        with ex_subset[THEN spec[of _ i], THEN spec[of _ i]] obtain j
          where "B \<subseteq> g j" by blast
        with `g j \<subseteq> A` and `\<forall>j. finite (g j)` and finite_subset
          have "B \<subseteq> A" and "finite B" by auto
        thus "B \<in> {B \<in> Pow A. finite B}" by auto
      qed
      have "wqo_on ?P ?B'"
      proof
        from reflp_on_subset[OF subset refl] show "reflp_on ?P ?B'" .
      next
        from transp_on_subset[OF subset trans] show "transp_on ?P ?B'" .
      next
        fix f :: "'a set seq" assume "\<forall>i. f i \<in> ?B'"
        from no_bad_of_special_shape_imp_goodp[of ?P ?B f, OF no_index this]
          show "goodp ?P f" .
      qed
      let ?a' = "{a i | i. True}"
      have "?a' \<subseteq> A" using a and ex_subset and `\<And>j. g j \<subseteq> A` by blast
      from wqo_on_subset[OF this assms]
        have "wqo_on P ?a'" .
      from wqo_on_Sigma[OF `wqo_on P ?a'` `wqo_on ?P ?B'`]
        have wqo: "wqo_on (prod_le P ?P) (?a' \<times> ?B')" .
      let ?aB = "\<lambda>i. (a i, ?B i)"
      let ?P' = "prod_le P ?P"
      have "\<forall>i. ?aB i \<in> (?a' \<times> ?B')" by auto
      with wqo have "goodp ?P' ?aB" unfolding wqo_on_def by auto
      then obtain i j where "i < j" and "?P'\<^sup>=\<^sup>= (?aB i) (?aB j)"
        by (auto simp: goodp_def)
      hence "(a i = a j \<and> ?B i = ?B j) \<or> (P (a i) (a j) \<and> ?P (?B i) (?B j))"
        unfolding prod_le_def by auto
      thus False
      proof
        assume *: "a i = a j \<and> ?B i = ?B j"
        hence "?A i = ?A j" by (metis a insert_Diff_single insert_absorb)
        hence "?P\<^sup>=\<^sup>= (?A i) (?A j)" by auto
        with `i < j` and `bad ?P ?A` show False by (auto simp: goodp_def)
      next
        assume "P (a i) (a j) \<and> ?P (?B i) (?B j)"
        hence *: "P (a i) (a j)" and **: "?P (?B i) (?B j)" by auto
        from **[unfolded set_le_def] obtain f
          where ***: "\<forall>a\<in>?B i. f a \<in> ?B j \<and> P a (f a)"
          and inj[unfolded inj_on_def]: "inj_on f (?B i)" by blast
        let ?f = "f(a i := a j)"
        have "inj_on ?f (?A i)" unfolding inj_on_def
        proof (intro ballI impI)
          fix x y
          assume "x \<in> ?A i" and "y \<in> ?A i" and "?f x = ?f y"
          hence "x = a i \<or> x \<in> ?B i" by auto
          thus "x = y"
          proof
            assume "x = a i"
            from `y \<in> ?A i` have "y = a i \<or> y \<in> ?B i" by auto
            thus ?thesis
            proof
              assume "y = a i" with `x = a i` show ?thesis by simp
            next
              assume "y \<in> ?B i" hence "y \<noteq> a i" by auto
              with `y \<in> ?B i` and *** have "?f y \<in> ?B j" by auto
              hence "?f y \<noteq> a j" by auto
              with `x = a i` and `?f x = ?f y` show ?thesis by auto
            qed
          next
            assume "x \<in> ?B i"
            hence "x \<noteq> a i" by simp
            hence "?f x \<noteq> a j" using *** and `x \<in> ?B i` by auto
            from `y \<in> ?A i` have "y = a i \<or> y \<in> ?B i" by auto
            thus ?thesis
            proof
              assume "y = a i" hence "?f y = a j" by auto
              with `?f x \<noteq> a j` and `?f x = ?f y` show ?thesis by simp
            next
              assume "y \<in> ?B i" hence "y \<noteq> a i" by auto
              with `x \<in> ?B i` and `x \<noteq> a i` and `?f x = ?f y`
              have "f x = f y" by simp
              with `x \<in> ?B i` and `y \<in> ?B i` and inj show ?thesis by blast
            qed
          qed
        qed
        moreover have "\<forall>a\<in>?A i. ?f a \<in> ?A j \<and> P a (?f a)"
        proof (intro ballI)
          fix x assume "x \<in> ?A i" hence "x = a i \<or> x \<in> ?B i" by auto
          thus "?f x \<in> ?A j \<and> P x (?f x)"
          proof
            assume "x = a i" with * and a show ?thesis by simp
          next
            assume "x \<in> ?B i"
            moreover hence "x \<noteq> a i" by auto
            ultimately show ?thesis using *** by auto
          qed
        qed
        ultimately have "?P (?A i) (?A j)" unfolding set_le_def by blast
        hence "?P\<^sup>=\<^sup>= (?A i) (?A j)" by auto
        with `i < j` and `bad ?P ?A` show False by (auto simp: goodp_def)
      qed
    qed
  }
  with refl and trans show ?thesis unfolding wqo_on_def by blast
qed

end
