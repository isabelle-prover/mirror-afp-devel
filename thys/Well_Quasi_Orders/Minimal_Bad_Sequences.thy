(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Constructing Minimal Bad Sequences *}

theory Minimal_Bad_Sequences
imports
  "../Abstract-Rewriting/Seq"
  Restricted_Predicates
begin

definition good :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a seq \<Rightarrow> bool" where
  "good P f \<equiv> \<exists>i j. i < j \<and> P (f i) (f j)"

abbreviation bad where "bad P f \<equiv> \<not> good P f"

fun minimal_bad_seq :: "('a seq \<Rightarrow> nat \<Rightarrow> 'a seq) \<Rightarrow> 'a seq \<Rightarrow> nat \<Rightarrow> 'a seq" where
  "minimal_bad_seq A f 0 = f"
| "minimal_bad_seq A f (Suc n) = (
    let g = minimal_bad_seq A f n in
    A g n)"

lemma choice2:
  "\<forall>x y. P x y \<longrightarrow> (\<exists>z. Q x y z) \<Longrightarrow> \<exists>f. \<forall>x y. P x y \<longrightarrow> Q x y (f x y)"
  using bchoice [of "{(x, y). P x y}" "\<lambda>(x, y) z. Q x y z"] by force

text {*A locale capturing the construction of minimal bad sequences over
\emph{values} from @{term "A"}. Where @{term less} is the order that
is used for checking minimality. The required properties are:
\begin{itemize}
\item @{term "less"} has to be well-founded on @{term "A"}
\item @{term "less"} has to be transitive
\end{itemize}*}
locale mbs =
  fixes less :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and A :: "'b set"
  assumes wfp_on_less: "wfp_on less A"
    and less_trans: "less x y \<Longrightarrow> less y z \<Longrightarrow> less x z"
begin

abbreviation lesseq where "lesseq \<equiv> less\<^sup>=\<^sup>="

lemma lesseq_trans: "lesseq x y \<Longrightarrow> lesseq y z \<Longrightarrow> lesseq x z"
  using less_trans by auto

text {*An infinite sequence, is minimal at position @{text n}, if every
subsequence that coincides on the first @{text "n - 1"} elements is good,
whenever the @{text n}-th element is replaced by a smaller one.*}
definition min_at :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b seq \<Rightarrow> nat \<Rightarrow> bool" where
  "min_at P f n \<equiv>
    \<forall>g. (\<forall>i. g i \<in> A) \<and> (\<forall>i<n. g i = f i) \<and> less (g n) (f n) \<longrightarrow> good P g"

lemma less_induct [consumes 1, case_names IH]:
  assumes "x \<in> A"
    and "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> less y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using wfp_on_induct [OF wfp_on_less, of x P] and assms by blast

lemma less_imp_lesseq: "less x y \<Longrightarrow> lesseq x y" by auto

text {*Constructing a bad sequence that is minimal at @{term "Suc n"}
from a bad sequence that is minimal at @{term n}. Moreover, the first
@{term n} elements coincide with the given sequence (hence minimality
at @{term n} is preserved) and the remaining elements are lessly
related to the remaining elements of the given sequence.*}
(*same proof as for minimal_bad_Suc, but with explicit structure
of induction (better suited for textual explanation)*)
lemma
  assumes "\<forall>i. f i \<in> A"
    and "bad P f"
    and "min_at P f n"
  shows "\<exists>g.
    (\<forall>i\<le>n. g i = f i) \<and>
    lesseq (g (Suc n)) (f (Suc n)) \<and>
    (\<forall>i. g i \<in> A) \<and>
    bad P g \<and>
    min_at P g (Suc n)"
  (is "\<exists>g. ?C g f (f (Suc n))")
proof -
  let ?I = "\<lambda>x. \<forall>f. x = f (Suc n) \<and> (\<forall>i. f i \<in> A) \<and> bad P f \<and> min_at P f n \<longrightarrow> (\<exists>g. ?C g f x)"
  {
    fix x
    assume "x = f (Suc n)"
    hence "x \<in> A" using assms by simp+
    hence "?I x"
    proof (induct x rule: less_induct)
      fix x
      assume "x \<in> A" and IH: "\<And>y. \<lbrakk>y \<in> A; less y x\<rbrakk> \<Longrightarrow> ?I y"
      show "?I x"
      proof (intro allI impI, elim conjE)
        fix f
        assume [simp]: "x = f (Suc n)" and vals: "\<forall>i. f i \<in> A"
          and "bad P f" and "min_at P f n"
        show "\<exists>g. ?C g f x"
        proof (cases "min_at P f (Suc n)")
          case True with vals and `bad P f` show ?thesis by auto
        next
          case False
          then obtain h
            where less: "less (h (Suc n)) x"
            and [simp]: "\<And>i. i < Suc n \<Longrightarrow> h i = f i"
            and "\<forall>i. h i \<in> A"
            and "bad P h" by (auto simp: min_at_def)
          moreover then have "?I (h (Suc n))" using IH by blast
          moreover have "min_at P h n"
            using `min_at P f n` by (auto simp: min_at_def)
          ultimately obtain M where "?C M h (h (Suc n))" by blast
          moreover with less_imp_lesseq [OF less]
            have "lesseq (M (Suc n)) (f (Suc n))"
            and "\<forall>i\<le>n. M i = f i"
            using lesseq_trans [of "M (Suc n)" "h (Suc n)"] by auto
          ultimately show ?thesis by auto
        qed
      qed
    qed
  }
  hence "\<And>x. x = f (Suc n) \<Longrightarrow> ?I x" .
  from this [OF refl, THEN spec [of _ f]] and assms
    show ?thesis by blast
qed

lemma minimal_bad_Suc:
  assumes "\<forall>i. f i \<in> A"
    and "bad P f"
    and "min_at P f n"
  shows "\<exists>g.
    (\<forall>i\<le>n. g i = f i) \<and>
    lesseq (g (Suc n)) (f (Suc n)) \<and>
    (\<forall>i. g i \<in> A) \<and>
    bad P g \<and>
    min_at P g (Suc n)"
  (is "\<exists>g. ?C g f (f (Suc n))")
using assms(1) [THEN spec, of "Suc n"] and assms
proof (induct x\<equiv>"f (Suc n)" arbitrary: f rule: less_induct)
  case IH
  then have *: "\<forall>i. f i \<in> A" by simp
  show ?case
  proof (cases "min_at P f (Suc n)")
    case True with * and `bad P f` show ?thesis by auto
  next
    case False
    then obtain h
    where less: "less (h (Suc n)) (f (Suc n))"
      and [simp]: "\<forall>i<Suc n. h i = f i"
      and "\<forall>i. h i \<in> A"
      and "bad P h" by (auto simp: min_at_def)
    moreover then have "less (h (Suc n)) (f (Suc n))"
      and "h (Suc n) \<in> A"
      and "min_at P h n"
      using `min_at P f n` by (auto simp: min_at_def)
    ultimately obtain M where "?C M h (h (Suc n))"
      using IH(2) by blast
    moreover with less_imp_lesseq [OF less]
      have "lesseq (M (Suc n)) (f (Suc n))"
      and "\<forall>i\<le>n. M i = f i"
      using lesseq_trans [of "M (Suc n)" "h (Suc n)"] by auto
    ultimately show ?thesis by auto
  qed
qed

text {*If there is a bad sequence, then there is a bad sequence that is
minimal at its first element (used for the base case of constructing a
minimal bad sequence.*}
lemma minimal_bad_0:
  assumes "\<forall>i. f i \<in> A"
    and "bad P f"
  shows "\<exists>g. (\<forall>i. g i \<in> A) \<and> min_at P g 0 \<and> bad P g"
using assms(1) [THEN spec, of "0"] and assms
proof (induct x\<equiv>"f 0" arbitrary: f rule: less_induct)
  case IH show ?case
  proof (cases "min_at P f 0")
    case True with IH show ?thesis by blast
  next
    case False
    then obtain h where "less (h 0) (f 0)"
      and "\<forall>i. h i \<in> A" and "bad P h"
      by (auto simp: min_at_def)
    with IH show ?thesis by blast
  qed
qed

text {*If there is a bad sequence over elements of @{term "A"},
then there is a minimal (i.e., minimal at all positions) bad sequence
over elements of @{term "A"}.*}
lemma mbs:
  assumes "\<forall>i. f i \<in> A" and "bad P f"
  shows "\<exists>g. (\<forall>i. g i \<in> A) \<and> bad P g \<and> (\<forall>n. min_at P g n)"
proof -
  from minimal_bad_0 [of f, OF assms(1) `bad P f`] obtain g
    where "\<And>i. g i \<in> A" and "min_at P g 0" and "bad P g" by blast
  from minimal_bad_Suc
    have "\<forall>f n. (\<forall>i. f i \<in> A) \<and> min_at P f n \<and> bad P f \<longrightarrow>
    (\<exists>\<nu>.
      (\<forall>i. \<nu> i \<in> A) \<and>
      (\<forall>i\<le>n. \<nu> i = f i) \<and>
      lesseq (\<nu> (Suc n)) (f (Suc n)) \<and>
      bad P \<nu> \<and>
      min_at P \<nu> (Suc n))"
      (is "\<forall>f n. ?Q f n \<longrightarrow> (\<exists>\<nu>. ?Q' f n \<nu>)")
      by blast
  from choice2 [OF this] obtain \<nu>
    where * [rule_format]: "\<forall>f n. ?Q f n \<longrightarrow> ?Q' f n (\<nu> f n)" by force
  def [simp]: m' \<equiv> "minimal_bad_seq \<nu> g"
  txt {*The minimal bad sequence is the diagonal of @{term m'}.*}
  def [simp]: m \<equiv> "\<lambda>i. m' i i"
  have "\<forall>n. (\<forall>i. m' n i \<in> A)
    \<and> (\<forall>i\<le>n. min_at P (m' n) i)
    \<and> (\<forall>i\<le>n. m i = m' n i)
    \<and> bad P (m' n)" (is "\<forall>n. ?Q n")
  proof
    fix n show "?Q n"
    proof (induction n)
      case 0
      then show ?case
        using `\<And>i. g i \<in> A` and `min_at P g 0` and `bad P g` by auto
    next
      case (Suc n)
      with * [of "m' n" n]
        have eq: "\<forall>i\<le>n. m i = m' n i"
        and vals: "\<forall>i. m' n i \<in> A"
        and bad: "bad P (m' n)"
        and "bad P (m' (Suc n))"
        and min_at: "min_at P (m' n) n"
        and min_at_Suc: "min_at P (m' (Suc n)) (Suc n)"
        by (simp_all add: Let_def)
      moreover have vals': "\<forall>i\<ge>Suc n. m' (Suc n) i \<in> A"
      proof (intro allI impI)
        fix i assume "Suc n \<le> i"
        moreover from * [of "m' n"] and vals and min_at and bad
          have "\<nu> (m' n) n i \<in> A" by simp
        ultimately show "m' (Suc n) i \<in> A" by (simp add: Let_def)
      qed
      moreover have *: "\<forall>i\<le>Suc n. m i = m' (Suc n) i"
        using min_at and vals and bad using eq by (auto simp: * elim: le_SucE)
      moreover have "\<forall>i. m' (Suc n) i \<in> A"
      proof
        fix i
        show "m' (Suc n) i \<in> A"
          by (cases "i \<ge> Suc n") (insert vals' vals eq *, simp+)
      qed
      moreover have "\<forall>i\<le>Suc n. min_at P (m' (Suc n)) i"
      proof (intro allI impI)
        fix i assume "i \<le> Suc n"
        show "min_at P (m' (Suc n)) i"
        proof (cases "i = Suc n")
          case True with min_at_Suc show ?thesis by simp
        next
          case False
          moreover with `i \<le> Suc n` have "i \<le> n" by auto
          ultimately show ?thesis using Suc and * by (auto simp: min_at_def) 
        qed
      qed
      ultimately show ?case by simp
    qed
  qed
  then have "\<And>i. m i \<in> A"
    and min: "\<And>n i. i \<le> n \<Longrightarrow> min_at P (m' n) i"
    and eq: "\<And>n i. i \<le> n \<Longrightarrow> m i = m' n i"
    and bad: "\<And>n. bad P (m' n)" by (auto)
  then have "\<forall>i. m i \<in> A" by simp
  moreover have "bad P m"
  proof
    assume "good P m"
    then obtain i j :: nat where "i < j"
      and "P (m i) (m j)" by (auto simp: good_def)
    with eq [of i j] and bad show False by (auto simp: good_def)
  qed
  moreover have "\<forall>n. min_at P m n"
  proof (unfold min_at_def, intro allI impI, elim conjE)
    fix S n
    assume "\<forall>i<n. S i = m i"
    then have "\<forall>i<n. S i = m' n i" using eq by auto
    moreover assume "\<forall>i. S i \<in> A" and "less (S n) (m n)"
    ultimately show "good P S"
      using min [of n] by (auto simp: min_at_def)
  qed
  ultimately show ?thesis by blast
qed

end

end

