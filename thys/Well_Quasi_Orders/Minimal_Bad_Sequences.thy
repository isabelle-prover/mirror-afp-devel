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

text {*An infinite sequence is \emph{good} whenever there are indices
@{term "i < j"} such that @{term "P (f i) (f j)"}.*}
definition good :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a seq \<Rightarrow> bool" where
  "good P f \<equiv> \<exists>i j. i < j \<and> P (f i) (f j)"

text {*A sequence that is not good is called \emph{bad}.*}
abbreviation bad where "bad P f \<equiv> \<not> good P f"

text {*A locale capturing the construction of minimal bad sequences over
values from @{term "A"}. Where @{term less} is the order that is used for
checking minimality. The required properties are:
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

lemma less_induct [consumes 1, case_names IH]:
  assumes "x \<in> A"
    and "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> less y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using wfp_on_induct [OF wfp_on_less, of x P] and assms by blast

text {*Since @{term A} is well-founded, whenever an element of it
satisfies some property, then there is a minimal such element.*}
lemma minimal:
  assumes "x \<in> A" and "P x"
  shows "\<exists>y \<in> A. lesseq y x \<and> P y \<and> (\<forall>z \<in> A. less z y \<longrightarrow> \<not> P z)"
using assms
proof (induction rule: less_induct)
  case (IH x)
  show ?case
  proof (cases "\<forall>y \<in> A. less y x \<longrightarrow> \<not> P y")
    case True
    with IH show ?thesis by blast
  next
    case False
    then obtain y where "y \<in> A" and "less y x" and "P y" by blast
    from IH.IH [OF this] show ?thesis
      using `less y x` by (simp) (metis less_trans)
  qed
qed

lemma less_not_eq [simp]:
  "x \<in> A \<Longrightarrow> less x y \<Longrightarrow> x = y \<Longrightarrow> False"
  by (metis less_trans strict_reflclp transp_onI wfp_on_imp_irreflp_on wfp_on_less)

text {*The set of all bad sequences over @{term A}.*}
abbreviation "BAD P \<equiv> {f::'a seq. (\<forall>i. f i \<in> A) \<and> bad P f}"

text {*A partial order on infinite bad sequences. Needed for the
partial order variant of Zorn's lemma.*}
definition gebseq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a seq \<times> 'a seq) set" where
  "gebseq P =
    {(f, g). f \<in> BAD P \<and> g \<in> BAD P \<and> (f = g \<or> (\<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j)))}"

definition gbseq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a seq \<times> 'a seq) set" where
  "gbseq P = {(f, g). f \<in> BAD P \<and> g \<in> BAD P \<and> (\<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j))}"

lemma gebseqI [intro!]:
  assumes "f \<in> BAD P" and "g \<in> BAD P"
    and "f \<noteq> g \<Longrightarrow> \<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j)"
  shows "(f, g) \<in> gebseq P"
  using assms by (auto simp: gebseq_def)

lemma gbseqI [intro!]:
  assumes "f \<in> BAD P" and "g \<in> BAD P"
    and "less (g i) (f i)"
    and "\<And>j. j < i \<Longrightarrow> f j = g j"
  shows "(f, g) \<in> gbseq P"
  using assms by (auto simp: gbseq_def)

lemma gebseqE [elim!]:
  assumes "(f, g) \<in> gebseq P" and "f = g \<Longrightarrow> Q"
    and "\<And>i. \<lbrakk>f \<in> BAD P; g \<in> BAD P; less (g i) (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: gebseq_def)

lemma gbseqE [elim!]:
  assumes "(f, g) \<in> gbseq P"
    and "\<And>i. \<lbrakk>f \<in> BAD P; g \<in> BAD P; less (g i) (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: gbseq_def)

lemma gbseq_imp_gebseq:
  "(f, g) \<in> gbseq P \<Longrightarrow> (f, g) \<in> gebseq P" by auto

lemma Field_gebseq [simp]:
  "Field (gebseq P) = BAD P"
  by (auto simp: Field_def gebseq_def)

lemma gebseq_refl:
  "refl_on (Field (gebseq P)) (gebseq P)"
  unfolding Field_gebseq by (auto simp add: refl_on_def gebseq_def)

lemma gebseq_trans:
  "(f, g) \<in> gebseq P \<Longrightarrow> (g, h) \<in> gebseq P \<Longrightarrow> (f, h) \<in> gebseq P"
  by (auto) (case_tac "i < ia", auto simp: less_Suc_eq not_less_eq dest: less_trans,
             metis dual_order.strict_trans)

lemma Preorder_gebseq:
  "Preorder (gebseq P)"
  using gebseq_refl by (auto simp: preorder_on_def trans_def elim!: gebseq_trans)

lemma gebseq_antisym:
  "antisym (gebseq P)"
  apply (auto simp: antisym_def gebseq_def)
  apply (case_tac "i < ia")
  apply (auto dest: less_not_eq)
  by (metis less_not_eq less_trans nat_neq_iff)

lemma Partial_order_gebseq:
  "Partial_order (gebseq P)"
  using Preorder_gebseq and gebseq_antisym by (simp add: partial_order_on_def)

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

text {*A minimal element from a set.*}
definition "min_elt B x \<longleftrightarrow> x \<in> B \<and> (\<forall>y \<in> A. less y x \<longrightarrow> y \<notin> B)"

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

text {*@{term "lb"} consists of minimal elements.*}
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

text {*If there is at least one bad sequence, then every chain of bad
sequences has a lower bound.*}
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

text {*A minimal bad sequence is a bad sequence such that any sequence
that is smaller w.r.t. @{term "gbseq P"} is good.*}
definition minimal :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a seq \<Rightarrow> bool"
where
  "minimal P f \<longleftrightarrow>
    f \<in> BAD P \<and>
    (\<forall>g. (\<forall>i. g i \<in> A) \<and> (f, g) \<in> gbseq P \<longrightarrow> good P g)"

text {*If there is a bad sequence, then there is a minimal bad sequence.*}
lemma mbs:
  assumes "h \<in> BAD P"
  shows "\<exists>f. minimal P f"
proof -
  from Zorns_po_lemma [OF Partial_order_gebseq, of P]
    and lower_bound_ex [OF _ assms]
  have "\<exists>f \<in> BAD P. \<forall>g \<in> BAD P. (f, g) \<in> gebseq P \<longrightarrow> g = f"
    unfolding Field_gebseq by blast
  then show ?thesis by (auto simp: gbseq_conv minimal_def) metis
qed

end

end

