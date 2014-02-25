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
    and less_trans: "\<lbrakk>x \<in> A; y \<in> A; z \<in> A; less x y; less y z\<rbrakk> \<Longrightarrow> less x z"
begin

abbreviation lesseq where "lesseq \<equiv> less\<^sup>=\<^sup>="

lemma less_induct [consumes 1, case_names IH]:
  assumes "x \<in> A"
    and "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> less y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using wfp_on_induct [OF wfp_on_less, of x P] and assms by blast

text {*Since @{term A} is well-founded w.r.t.~the transitive relation @{term P}, whenever
an element of it satisfies some property, then there is a minimal such element.*}
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
    with IH.IH show ?thesis using `x \<in> A` by (fastforce elim!: less_trans)
  qed
qed

lemma less_not_eq [simp]:
  "x \<in> A \<Longrightarrow> less x y \<Longrightarrow> x = y \<Longrightarrow> False"
  by (metis minimal)

text {*The set of all sequences over @{term A}.*}
abbreviation "SEQ \<equiv> {f::'a seq. \<forall>i. f i \<in> A}"
text {*The set of all bad sequences over @{term A}.*}
abbreviation "BAD P \<equiv> {f::'a seq. (\<forall>i. f i \<in> A) \<and> bad P f}"

text {*A partial order on infinite bad sequences. Needed for the
partial order variant of Zorn's lemma.*}
definition gebseq :: "('a seq \<times> 'a seq) set" where
  "gebseq = {(f, g). f \<in> SEQ \<and> g \<in> SEQ \<and> (f = g \<or> (\<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j)))}"

text {*The strict part of the above order.*}
definition gbseq :: "('a seq \<times> 'a seq) set" where
  "gbseq = {(f, g). f \<in> SEQ \<and> g \<in> SEQ \<and> (\<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j))}"

lemma gebseqI [intro!]:
  assumes "f \<in> SEQ" and "g \<in> SEQ"
    and "f \<noteq> g \<Longrightarrow> \<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j)"
  shows "(f, g) \<in> gebseq"
  using assms by (auto simp: gebseq_def)

lemma gbseqI [intro!]:
  assumes "f \<in> SEQ" and "g \<in> SEQ"
    and "less (g i) (f i)"
    and "\<And>j. j < i \<Longrightarrow> f j = g j"
  shows "(f, g) \<in> gbseq"
  using assms by (auto simp: gbseq_def)

lemma gebseqE [elim!]:
  assumes "(f, g) \<in> gebseq" and "f = g \<Longrightarrow> Q"
    and "\<And>i. \<lbrakk>f \<in> SEQ; g \<in> SEQ; less (g i) (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: gebseq_def)

lemma gbseqE [elim!]:
  assumes "(f, g) \<in> gbseq"
    and "\<And>i. \<lbrakk>f \<in> SEQ; g \<in> SEQ; less (g i) (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: gbseq_def)

text {*The @{term i}-th "column" of a set @{term B} of infinite sequences.*}
definition "ith B i = {f i | f. f \<in> B}"

lemma ith_conv [simp]:
  "x \<in> ith B i \<longleftrightarrow> (\<exists>f \<in> B. f i = x)"
  by (auto simp: ith_def)

text {*A minimal element (w.r.t.~@{term less}) from a set.*}
definition "min_elt B = (SOME x. x \<in> A \<inter> B \<and> (\<forall>y \<in> A. less y x \<longrightarrow> y \<notin> B))"

lemma min_elt_ex:
  assumes "A \<inter> B \<noteq> {}"
  shows "\<exists>x. x \<in> A \<inter> B \<and> (\<forall>y \<in> A. less y x \<longrightarrow> y \<notin> B)"
  using assms using minimal [of _ "\<lambda>x. x \<in> B"] by auto

lemma min_elt_mem:
  assumes "A \<inter> B \<noteq> {}"
  shows "min_elt B \<in> B"
  using someI_ex [OF min_elt_ex [OF assms]] by (auto simp: min_elt_def)

lemma min_elt_minimal:
  assumes "A \<inter> B \<noteq> {}"
    and "y \<in> A" and "less y (min_elt B)"
  shows "y \<notin> B"
  using someI_ex [OF min_elt_ex [OF assms(1)]] and assms(2-) by (auto simp: min_elt_def)

context
  fixes P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

text {*The restriction of @{term "BAD P"} to sequences that are equal to a given sequence @{term f}
up to position @{term i}.*}
definition similar_upto :: "'a seq \<Rightarrow> nat \<Rightarrow> 'a seq set"
where
  "similar_upto f i = {g \<in> BAD P. \<forall>j < i. f j = g j}"

lemma similar_upto_conv [simp]:
  "g \<in> similar_upto f i \<longleftrightarrow> g \<in> BAD P \<and> (\<forall>j < i. f j = g j)"
  by (simp add: similar_upto_def)

lemma similar_upto_0 [simp]:
  "similar_upto f 0 = BAD P"
  by (auto simp: similar_upto_def)

lemma similar_upto_id [simp, intro]:
  "f \<in> BAD P \<Longrightarrow> f \<in> similar_upto f i"
  by (simp add: similar_upto_def)

lemma similar_upto_cong [fundef_cong]:
  assumes "\<And>j. j < i \<Longrightarrow> f j = g j"
  shows "similar_upto f i = similar_upto g i"
  using assms by (auto simp: similar_upto_def)

text {*A lower bound to all sequences in a set of sequences @{term B}.*}
fun lb :: "'a seq" where
  "lb 0 = min_elt (ith (BAD P) 0)" |
  "lb (Suc i) = min_elt (ith (similar_upto lb (Suc i)) (Suc i))"

text {*Short definition of the lower bound.*}
lemma lb:
  "lb i = min_elt (ith (similar_upto lb i) i)"
  by (induct i) simp_all

declare lb.simps [simp del]

lemma similar_upto_mono:
  "i < j \<Longrightarrow> similar_upto f j \<subseteq> similar_upto f i"
  by auto

lemma similar_upto_mem:
  assumes "f \<in> similar_upto g i"
  shows "f j \<in> A"
  using assms by (auto simp: gebseq_def)

text {*When the given chain is not empty, then filtering it w.r.t.~positions in @{term lb}
never yields an empty set of sequences.*}
lemma similar_upto_non_empty:
  assumes "BAD P \<noteq> {}"
  shows "similar_upto lb i \<noteq> {}"
proof (induct i)
  case 0
  with assms show ?case by simp
next
  let ?A = "\<lambda>i. ith (similar_upto lb i) i"
  case (Suc i)
  then have "?A i \<noteq> {}" by (force simp: ith_def)
  moreover have "similar_upto lb i \<subseteq> similar_upto lb 0" using similar_upto_mono by auto
  ultimately have "A \<inter> ?A i \<noteq> {}" by (force dest: similar_upto_mem)
  from min_elt_mem [OF this, folded lb] obtain f
    where "f \<in> BAD P" and "\<forall>j < Suc i. lb j = f j" by (force simp: less_Suc_eq)
  then show ?case by force
qed

lemma non_empty_ith:
  assumes "g \<in> BAD P"
  shows "A \<inter> ith (similar_upto lb i) i \<noteq> {}"
proof -
  from assms have "BAD P \<noteq> {}" by auto
  from similar_upto_non_empty [OF this]
    show ?thesis by auto (metis IntI empty_iff equals0I ith_conv similar_upto_mem)
qed

lemmas
  lb_minimal = non_empty_ith [THEN min_elt_minimal, of , folded lb]

lemmas
  lb_mem = non_empty_ith [THEN min_elt_mem, folded lb]

text {*If there is at least one bad sequence, then there is also a minimal one.*}
lemma lower_bound_ex:
  assumes "h \<in> BAD P"
  shows "\<exists>f \<in> BAD P. \<forall>g. (f, g) \<in> gbseq \<longrightarrow> g \<notin> BAD P"
proof (cases "BAD P = {}")
  assume "BAD P = {}"
  with `h \<in> BAD P` show ?thesis by auto
next
  assume "BAD P \<noteq> {}"
  then obtain g where g: "g \<in> BAD P" by blast

  from lb_mem [OF g]
    have *: "\<And>j. lb j \<in> ith (similar_upto lb j) j" .
  then have "\<forall>i. lb i \<in> A" by (auto simp: min_elt_def similar_upto_def) (metis)
  moreover have "bad P lb"
  proof
    assume "good P lb"
    then obtain i j where "i < j" and "P (lb i) (lb j)" by (auto simp: good_def)
    with * have "lb j \<in> ith (similar_upto lb j) j" by (auto simp: min_elt_def)
    then obtain g where "g \<in> similar_upto lb j" and g: "g j = lb j" by force
    then have "\<forall>k < j. g k = lb k" by auto
    with `i < j` and `P (lb i) (lb j)` and g have "P (g i) (g j)" by auto
    with `i < j` have "good P g" by (auto simp: good_def)
    with `g \<in> similar_upto lb j` show False by (auto simp: gebseq_def)
  qed
  ultimately have "lb \<in> BAD P" by simp
  moreover have "\<forall>g. (lb, g) \<in> gbseq \<longrightarrow> g \<notin> BAD P"
  proof (intro allI impI)
    fix g
    assume "(lb, g) \<in> gbseq"
    then obtain i where "\<forall>i. lb i \<in> A" and "\<forall>i. g i \<in> A"
      and "\<forall>j < i. lb j = g j" and "less (g i) (lb i)" by auto
    with lb_minimal [OF g, of _ i]
      have *: "g i \<notin> ith (similar_upto lb i) i" by auto
    show "g \<notin> BAD P"
    proof
      assume "g \<in> BAD P"
      then have "g \<in> similar_upto lb i" using `\<forall>j < i. lb j = g j` by (auto simp: similar_upto_def)
      then have "g i \<in> ith (similar_upto lb i) i" by auto
      with * show False by contradiction
    qed
  qed
  ultimately show ?thesis by blast
qed

end

lemma gbseq_conv:
  "(f, g) \<in> gbseq \<longleftrightarrow> f \<noteq> g \<and> (f, g) \<in> gebseq"
  by (auto simp: gbseq_def gebseq_def) (metis less_not_eq)

text {*A minimal bad sequence is a bad sequence such that any sequence
that is smaller w.r.t. @{term "gbseq"} is good.*}
definition minimal :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a seq \<Rightarrow> bool"
where
  "minimal P f \<longleftrightarrow> f \<in> BAD P \<and> (\<forall>g. (\<forall>i. g i \<in> A) \<and> (f, g) \<in> gbseq \<longrightarrow> good P g)"

text {*If there is a bad sequence, then there is a minimal bad sequence.*}
lemma mbs:
  assumes "h \<in> BAD P"
  shows "\<exists>f. minimal P f"
proof -
  from lower_bound_ex [OF assms]
    show ?thesis by (auto simp: minimal_def gbseq_conv) metis
qed

end

end

