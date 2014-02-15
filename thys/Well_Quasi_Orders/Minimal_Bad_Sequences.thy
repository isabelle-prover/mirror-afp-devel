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
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and A :: "'a set"
  assumes wfp_on_less: "wfp_on less A"
    and less_trans: "less x y \<Longrightarrow> less y z \<Longrightarrow> less x z"
begin

abbreviation lesseq where "lesseq \<equiv> less\<^sup>=\<^sup>="

lemma lesseq_trans: "lesseq x y \<Longrightarrow> lesseq y z \<Longrightarrow> lesseq x z"
  using less_trans by auto

text {*An infinite sequence, is minimal at position @{text n}, if every
subsequence that coincides on the first @{text "n - 1"} elements is good,
whenever the @{text n}-th element is replaced by a smaller one.*}
definition min_at :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a seq \<Rightarrow> nat \<Rightarrow> bool" where
  "min_at P f n \<equiv>
    \<forall>g. (\<forall>i. g i \<in> A) \<and> (\<forall>i<n. g i = f i) \<and> less (g n) (f n) \<longrightarrow> good P g"

lemma less_induct [consumes 1, case_names IH]:
  assumes "x \<in> A"
    and "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> less y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using wfp_on_induct [OF wfp_on_less, of x P] and assms by blast

lemma less_imp_lesseq:
  "less x y \<Longrightarrow> lesseq x y" by auto

lemma less_not_eq [simp]:
  "x \<in> A \<Longrightarrow> less x y \<Longrightarrow> x = y \<Longrightarrow> False"
  by (metis less_trans strict_reflclp transp_onI wfp_on_imp_irreflp_on wfp_on_less)

abbreviation "BAD P \<equiv> {f::'a seq. (\<forall>i. f i \<in> A) \<and> bad P f}"

text {*A partial order on infinite bad sequences.*}
definition gebseq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a seq \<times> 'a seq) set" where
  "gebseq P = {(f, g). f \<in> BAD P \<and> g \<in> BAD P \<and> (f = g \<or> (\<exists>i. less (g i) (f i) \<and> (\<forall>j<i. f j = g j)))}"

definition gbseq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a seq \<times> 'a seq) set" where
  "gbseq P = {(f, g). f \<in> BAD P \<and> g \<in> BAD P \<and> (\<exists>i. less (g i) (f i) \<and> (\<forall>j<i. f j = g j))}"

lemma gbseqI [intro]:
  assumes "f \<in> BAD P" and "g \<in> BAD P"
    and "less (g i) (f i)"
    and "\<And>j. j < i \<Longrightarrow> f j = g j"
  shows "(f, g) \<in> gbseq P"
  using assms by (auto simp: gbseq_def)

lemma gbseq_imp_gebseq:
  "(f, g) \<in> gbseq P \<Longrightarrow> (f, g) \<in> gebseq P"
  by (auto simp: gbseq_def gebseq_def)

lemma Field_gebseq [simp]:
  "Field (gebseq P) = BAD P"
  by (auto simp: Field_def gebseq_def)

lemma gebseq_refl:
  "refl_on (Field (gebseq P)) (gebseq P)"
  unfolding Field_gebseq by (auto simp add: refl_on_def gebseq_def)

lemma gebseqE [elim]:
  assumes "(f, g) \<in> gebseq P" and "f = g \<Longrightarrow> Q"
    and "\<And>i. \<lbrakk>f \<in> BAD P; g \<in> BAD P; less (g i) (f i); \<forall>j<i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: gebseq_def)

lemma gebseq_trans:
  assumes "(f, g) \<in> gebseq P" and "(g, h) \<in> gebseq P"
  shows "(f, h) \<in> gebseq P"
using assms(1)
proof
  assume "f = g"
  with assms(2) show ?thesis by simp
next
  fix i
  assume BAD: "f \<in> BAD P" "g \<in> BAD P"
    and less_i: "less (g i) (f i)" and eq_i: "\<forall>j<i. f j = g j"
  from assms(2) show ?thesis
  proof
    assume "g = h"
    with assms(1) show ?thesis by simp
  next
    fix j
    assume "h \<in> BAD P"
    note BAD = BAD this
    assume less_j: "less (h j) (g j)" and eq_j: "\<forall>k<j. g k = h k"
    { assume [simp]: "i = j"
      then have "less (h j) (f j)" using less_trans [OF less_j] and less_i by simp
      moreover have "\<forall>k<j. f k = h k" using eq_i and eq_j by simp
      ultimately have ?thesis using BAD by (auto simp: gebseq_def) }
    moreover
    { assume "i < j"
      then have "less (h i) (f i)" and "\<forall>j<i. f j = h j" using less_i and eq_j and eq_i by auto
      then have ?thesis using BAD by (auto simp: gebseq_def) }
    moreover
    { assume "j < i"
      then have "less (h j) (f j)" and "\<forall>k<j. f k = h k" using less_j and eq_j and eq_i by auto
      then have ?thesis using BAD by (auto simp: gebseq_def) }
    ultimately show ?thesis by arith
  qed
qed

lemma gebseq_trans':
  "trans (gebseq P)"
  using gebseq_trans [of _ _ P] unfolding trans_def by blast

lemma Preorder_gebseq:
  "Preorder (gebseq P)"
  using gebseq_trans' [of P] and gebseq_refl [of P] by (simp add: preorder_on_def)

lemma lebseq_antisym:
  "antisym (gebseq P)"
  apply (unfold antisym_def, intro allI impI, auto simp: gebseq_def)
  apply (case_tac "i < ia")
  apply (auto dest: less_not_eq)
  by (metis less_not_eq less_trans nat_neq_iff)

lemma Partial_order_gebseq:
  "Partial_order (gebseq P)"
  using Preorder_gebseq [of P] and lebseq_antisym [of P] by (simp add: partial_order_on_def)

lemma minimal:
  assumes "x \<in> A" and "P x"
  shows "\<exists>y \<in> A. lesseq y x \<and> P y \<and> (\<forall>z \<in> A. less z y \<longrightarrow> \<not> P z)"
using assms
proof (induction rule: less_induct)
  case (IH x)
  show ?case
  proof (cases "\<forall>y \<in> A. less y x \<longrightarrow> \<not> P y")
    case True
    then have "x \<in> A \<and> lesseq x x \<and> P x \<and> (\<forall>y \<in> A. less y x \<longrightarrow> \<not> P y)"
      using IH.prems and IH.hyps by auto
    then show ?thesis by blast
  next
    case False
    then obtain y where "y \<in> A" and "less y x" and "P y" by blast
    from IH.IH [OF this] show ?thesis using `less y x` by (metis less_imp_lesseq lesseq_trans)
  qed
qed

text {*A minimal element from a set.*}
definition "min_elt B x \<longleftrightarrow> x \<in> B \<and> (\<forall>y \<in> A. less y x \<longrightarrow> y \<notin> B)"

text {*Let @{term C} be a chain w.r.t. @{term "gebseq P"}.*}
context
  fixes C :: "'a seq set" and P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes C: "C \<in> Chains (gebseq P)"
begin

text {*The restriction of @{term C} to sequences that are similar to a given sequence @{term f}
up to position @{term i}.*}
definition similar_upto :: "'a seq \<Rightarrow> nat \<Rightarrow> 'a seq set"
where
  "similar_upto f i = {g \<in> C. \<forall>j < i. f j = g j}"

lemma similar_upto_conv [simp]:
  "g \<in> similar_upto f i \<longleftrightarrow> g \<in> C \<and> (\<forall>j < i. f j = g j)"
  by (simp add: similar_upto_def)

lemma similar_upto_0 [simp]:
  "similar_upto f 0 = C"
  by (auto simp: similar_upto_def)

text {*The @{term i}-th "column" of a set @{term B} of infinite sequences.*}
definition "ith B i = {f i | f. f \<in> B}"

lemma ith_conv [simp]:
  "x \<in> ith B i \<longleftrightarrow> (\<exists>f \<in> B. f i = x)"
  by (auto simp: ith_def)

lemma similar_upto_cong [fundef_cong]:
  assumes "\<And>j. j < i \<Longrightarrow> f j = g j"
  shows "similar_upto f i = similar_upto g i"
  using assms by (auto simp: similar_upto_def)

text {*A lower bound to all sequences in @{term C}.*}
fun lb :: "nat \<Rightarrow> 'a" where
  "lb 0 = (SOME x. min_elt (ith C 0) x)" |
  "lb (Suc i) = (SOME x. min_elt (ith (similar_upto lb (Suc i)) (Suc i)) x)"

lemma lb:
  "lb i = (SOME x. min_elt (ith (similar_upto lb i) i) x)"
  by (induct i) simp_all

declare lb.simps [simp del]

lemma Chains_conv [simp]:
  "C \<in> Chains Q \<longleftrightarrow> (\<forall>x y. x \<in> C \<and> y \<in> C \<longrightarrow> (x, y) \<in> Q \<or> (y, x) \<in> Q)"
  by (auto simp: Chains_def)

lemma min_elt_lb:
  assumes "g \<in> C"
  shows "min_elt (ith (similar_upto lb i) i) (lb i)"
proof -
  let ?P = "\<lambda>i. ith (similar_upto lb i) i"
  have A: "\<forall>f \<in> C. \<forall>i. f i \<in> A" using C by (auto simp: gebseq_def)
  have "\<exists>x. min_elt (?P i) x"
  proof (induct i)
    case 0
    from minimal [of _ "\<lambda>x. x \<in> ith C 0"] show ?case
      using A and `g \<in> C` by (auto simp: min_elt_def) blast
  next
    case (Suc i)
    then have "min_elt (?P i) (lb i)" by (auto) (metis lb someI_ex)
    then have "lb i \<in> ith (similar_upto lb i) i" by (auto simp: min_elt_def)
    then obtain g where "g \<in> similar_upto lb i" and "g i = lb i" by (force simp: ith_def)
    then have "g (Suc i) \<in> A" and "g (Suc i) \<in> ith (similar_upto lb (Suc i)) (Suc i)"
      using A by (force simp: ith_def elim: less_SucE)+
    from minimal [of _ "\<lambda>x. x \<in> ?P (Suc i)", OF this]
      show ?case unfolding min_elt_def by blast
  qed
  from this [THEN someI_ex] show ?thesis by (metis lb)
qed

lemma min_elt_ith_lesseq:
  assumes "g \<in> C" and g_eq: "\<forall>j < i. g j = lb j"
    and *: "min_elt (ith (similar_upto lb i) i) (lb i)"
  shows "lesseq (lb i) (g i)"
proof -
  let ?P = "\<lambda>i. ith (similar_upto lb i) i"
  from C and `g \<in> C` have "g \<in> BAD P" by (auto simp: gebseq_def)
  from * have "lb i \<in> ?P i"
    and min: "\<forall>y \<in> A. less y (lb i) \<longrightarrow> y \<notin> ?P i" by (auto simp: min_elt_def)
  from `lb i \<in> ?P i` obtain f where "f \<in> C"
    and "\<forall>j < i. f j = lb j"
    and f_eq: "f i = lb i" by (auto)
  with g_eq have **: "\<forall>j < i. f j = g j" by auto
  from C and `f \<in> C` have "f \<in> BAD P" by (auto simp: gebseq_def)
  from `f \<in> C` and `g \<in> C` and C
    have "(f, g) \<in> gebseq P \<or> (g, f) \<in> gebseq P" by auto
  then show ?thesis
  proof
    assume "(f, g) \<in> gebseq P"
    with ** have "f i = g i \<or> less (g i) (f i)"
      by (auto simp: gebseq_def) (metis less_not_eq nat_less_cases)
    with min show ?thesis
      using `g \<in> BAD P` and `g \<in> C`
      by (force simp: f_eq g_eq similar_upto_def)
  next
    assume "(g, f) \<in> gebseq P"
    with ** have "f i = g i \<or> less (f i) (g i)"
      by (auto simp: gebseq_def) (metis less_not_eq nat_less_cases)
    then show ?thesis by (auto simp: f_eq)
  qed
qed

lemma lower_bound_ex:
  assumes "h \<in> BAD P"
  shows "\<exists>f \<in> BAD P. \<forall>g \<in> C. (g, f) \<in> gebseq P"
proof (cases "C = {}")
  assume "C = {}"
  with `h \<in> BAD P` show ?thesis by auto
next
  assume "C \<noteq> {}"
  then obtain g where "g \<in> C" by blast
  have A: "\<forall>f \<in> C. \<forall>i. f i \<in> A" using C by (auto simp: gebseq_def)

  from min_elt_lb [OF `g \<in> C`]
    have *: "\<forall>i. min_elt (ith (similar_upto lb i) i) (lb i)" ..
  then have "\<forall>i. lb i \<in> A" by (auto simp: min_elt_def similar_upto_def) (metis A)
  moreover have "bad P lb"
  proof
    assume "good P lb"
    then obtain i j where "i < j" and "P (lb i) (lb j)" by (auto simp: good_def)
    with * have "lb j \<in> ith (similar_upto lb j) j" by (auto simp: min_elt_def)
    then obtain g where "g \<in> similar_upto lb j" and g: "g j = lb j" by force
    then have "\<forall>k < j. g k = lb k" by auto
    with `i < j` and `P (lb i) (lb j)` and g have "P (g i) (g j)" by auto
    with `i < j` have "good P g" by (auto simp: good_def)
    with `g \<in> similar_upto lb j` and C show False by (auto simp: gebseq_def)
  qed
  ultimately have "lb \<in> BAD P" by simp
  moreover have "\<forall>g \<in> C. (g, lb) \<in> gebseq P"
  proof
    fix g
    assume "g \<in> C"
    then have "g \<in> BAD P" using C by (auto simp: gebseq_def)
    have "\<forall>i. (\<forall>j \<le> i. g j = lb j) \<or> (\<exists>j \<le> i. less (lb j) (g j) \<and> (\<forall>k < j. g k = lb k))"
    proof
      fix i
      show "(\<forall>j \<le> i. g j = lb j) \<or> (\<exists>j \<le> i. less (lb j) (g j) \<and> (\<forall>k < j. g k = lb k))"
      proof (induct i)
        case 0
        with * [THEN spec, of 0] show ?case
          using min_elt_ith_lesseq [OF `g \<in> C`, of 0] by auto
      next
        case (Suc i)
        then show ?case
        proof
          assume "\<forall>j \<le> i. g j = lb j"
          then show ?thesis
            using * [THEN spec, of "Suc i"]
            and min_elt_ith_lesseq [OF `g \<in> C`, of "Suc i"]
            by (auto simp: le_Suc_eq)
        next
          assume "(\<exists>j\<le>i. less (lb j) (g j) \<and> (\<forall>k<j. g k = lb k))"
          then show ?thesis by force
        qed
      qed
    qed
    then have "g = lb \<or> (\<exists>i. less (lb i) (g i) \<and> (\<forall>j < i. g j = lb j))" by auto
    then show "(g, lb) \<in> gebseq P" using `lb \<in> BAD P` and `g \<in> BAD P` by (auto simp: gebseq_def)
  qed
  ultimately show ?thesis by blast
qed

end

lemma gbseq_conv:
  "(f, g) \<in> gbseq P \<longleftrightarrow> f \<noteq> g \<and> (f, g) \<in> gebseq P"
  apply (auto simp: gbseq_def gebseq_def)
  by (metis less_not_eq)

definition
  "minimal P f \<longleftrightarrow>
    f \<in> BAD P \<and>
    (\<forall>g. (\<forall>i. g i \<in> A) \<and> (f, g) \<in> gbseq P \<longrightarrow> good P g)"

lemma mbs:
  assumes "h \<in> BAD P"
  shows "\<exists>f. minimal P f"
proof -
  from Zorns_po_lemma [OF Partial_order_gebseq, of P]
    and lower_bound_ex [OF _ assms]
  have "\<exists>f \<in> BAD P. \<forall>g \<in> BAD P. (f, g) \<in> gebseq P \<longrightarrow> g = f"
    unfolding Field_gebseq by blast
  then show ?thesis by (auto simp: gbseq_conv minimal_def)
qed

(*
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
*)

end

end

