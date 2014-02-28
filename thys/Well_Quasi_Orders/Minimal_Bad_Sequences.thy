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

text {*The set of all sequences over elements from @{term A}.*}
definition "SEQ A = {f::'a seq. \<forall>i. f i \<in> A}"

lemma SEQ_iff [iff]:
  "f \<in> SEQ A \<longleftrightarrow> (\<forall>i. f i \<in> A)"
  by (auto simp: SEQ_def)

(*it is unclear why the following two rules are needed at all*)
lemma ball_SEQ [simp]:
  "(\<forall>g \<in> SEQ A. P g) \<longleftrightarrow> (\<forall>g. g \<in> SEQ A \<longrightarrow> P g)"
  by blast

lemma ball_SEQ_D [dest!]:
  "Ball (SEQ A) P \<Longrightarrow> \<forall>g. g \<in> SEQ A \<longrightarrow> P g"
  by (auto)

text {*An infinite sequence is \emph{good} whenever there are indices
@{term "i < j"} such that @{term "P (f i) (f j)"}.*}
definition good :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a seq \<Rightarrow> bool" where
  "good P f \<longleftrightarrow> (\<exists>i j. i < j \<and> P (f i) (f j))"

text {*A sequence that is not good is called \emph{bad}.*}
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

text {*A locale capturing the construction of minimal bad sequences over
values from @{term "A"}. Where @{term less} is the order that is used for
checking minimality. The required properties are:
\begin{itemize}
\item @{term "less"} has to be well-founded on @{term "A"}
\item @{term "less"} has to be transitive on @{term "A"}
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

text {*The set of all bad sequences over @{term A}.*}
definition "BAD P \<equiv> {f \<in> SEQ A. bad P f}"

lemma BAD_iff [iff]:
  "f \<in> BAD P \<longleftrightarrow> (\<forall>i. f i \<in> A) \<and> bad P f"
  by (auto simp: BAD_def)

text {*A partial order on infinite bad sequences.*}
definition geseq :: "('a seq \<times> 'a seq) set" where
  "geseq =
    {(f, g). f \<in> SEQ A \<and> g \<in> SEQ A \<and> (f = g \<or> (\<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j)))}"

text {*The strict part of the above order.*}
definition gseq :: "('a seq \<times> 'a seq) set" where
  "gseq = {(f, g). f \<in> SEQ A \<and> g \<in> SEQ A \<and> (\<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j))}"

lemma geseq_iff:
  "(f, g) \<in> geseq \<longleftrightarrow>
    f \<in> SEQ A \<and> g \<in> SEQ A \<and> (f = g \<or> (\<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j)))"
  by (auto simp: geseq_def)

lemma gseq_iff:
  "(f, g) \<in> gseq \<longleftrightarrow>
    f \<in> SEQ A \<and> g \<in> SEQ A \<and> (\<exists>i. less (g i) (f i) \<and> (\<forall>j < i. f j = g j))"
  by (auto simp: gseq_def)

lemma geseqE:
  assumes "(f, g) \<in> geseq"
    and "\<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; f = g\<rbrakk> \<Longrightarrow> Q"
    and "\<And>i. \<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; less (g i) (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: geseq_iff)

lemma gseqE:
  assumes "(f, g) \<in> gseq"
    and "\<And>i. \<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; less (g i) (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: gseq_iff)

text {*The @{term i}-th "column" of a set @{term B} of infinite sequences.*}
definition "ith B i = {f i | f. f \<in> B}"

lemma ithI [intro]:
  "f \<in> B \<Longrightarrow> f i = x \<Longrightarrow> x \<in> ith B i"
  by (auto simp: ith_def)

lemma ithE [elim]:
  "\<lbrakk>x \<in> ith B i; \<And>f. \<lbrakk>f \<in> B; f i = x\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (auto simp: ith_def)

lemma ith_conv:
  "x \<in> ith B i \<longleftrightarrow> (\<exists>f \<in> B. x = f i)"
  by auto

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

end

text {*The restriction of a set @{term "B"} of sequences to sequences that are equal to a given
sequence @{term f} up to position @{term i}.*}
definition eq_upto :: "'a seq set \<Rightarrow> 'a seq \<Rightarrow> nat \<Rightarrow> 'a seq set"
where
  "eq_upto B f i = {g \<in> B. \<forall>j < i. f j = g j}"

lemma eq_uptoI [intro]:
  "\<lbrakk>g \<in> B; \<And>j. j < i \<Longrightarrow> f j = g j\<rbrakk> \<Longrightarrow> g \<in> eq_upto B f i"
  by (auto simp: eq_upto_def)

lemma eq_uptoE [elim]:
  "\<lbrakk>g \<in> eq_upto B f i; \<lbrakk>g \<in> B; \<And>j. j < i \<Longrightarrow> f j = g j\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (auto simp: eq_upto_def)

lemma eq_upto_Suc:
  "\<lbrakk>g \<in> eq_upto B f i; g i = f i\<rbrakk> \<Longrightarrow> g \<in> eq_upto B f (Suc i)"
  by (auto simp: eq_upto_def less_Suc_eq)

lemma eq_upto_0 [simp]:
  "eq_upto B f 0 = B"
  by (auto simp: eq_upto_def)

lemma eq_upto_cong [fundef_cong]:
  assumes "\<And>j. j < i \<Longrightarrow> f j = g j" and "B = C"
  shows "eq_upto B f i = eq_upto C g i"
  using assms by (auto simp: eq_upto_def)

context mbs
begin

context
  fixes P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

text {*A lower bound to all sequences in a set of sequences @{term B}.*}
fun lb :: "'a seq" where
  lb: "lb i = min_elt (ith (eq_upto (BAD P) lb i) i)"

declare lb.simps [simp del]

lemma eq_upto_BAD_mem:
  assumes "f \<in> eq_upto (BAD P) g i"
  shows "f j \<in> A"
  using assms by (auto)

text {*Assume that there is some infinite bad sequence @{term h}.*}
context
  fixes h :: "'a seq"
  assumes BAD_ex: "h \<in> BAD P"
begin

text {*When there is a bad sequence, then filtering @{term "BAD P"} w.r.t.~positions in @{term lb}
never yields an empty set of sequences.*}
lemma eq_upto_BAD_non_empty:
  "eq_upto (BAD P) lb i \<noteq> {}"
proof (induct i)
  case 0
  show ?case using BAD_ex by auto
next
  let ?A = "\<lambda>i. ith (eq_upto (BAD P) lb i) i"
  case (Suc i)
  then have "?A i \<noteq> {}" by auto
  moreover have "eq_upto (BAD P) lb i \<subseteq> eq_upto (BAD P) lb 0" by auto
  ultimately have "A \<inter> ?A i \<noteq> {}" by (auto simp: ith_def)
  from min_elt_mem [OF this, folded lb] obtain f
    where "f \<in> eq_upto (BAD P) lb (Suc i)" by (auto dest: eq_upto_Suc)
  then show ?case by blast
qed

lemma non_empty_ith:
  shows "A \<inter> ith (eq_upto (BAD P) lb i) i \<noteq> {}"
  using eq_upto_BAD_non_empty [of i] by auto

lemmas
  lb_minimal = non_empty_ith [THEN min_elt_minimal, of , folded lb]

lemmas
  lb_mem = non_empty_ith [THEN min_elt_mem, folded lb]

text {*@{term "lb"} is a infinite bad sequence.*}
lemma lb_BAD:
  "lb \<in> BAD P"
proof -
  have *: "\<And>j. lb j \<in> ith (eq_upto (BAD P) lb j) j" by (rule lb_mem)
  then have "\<forall>i. lb i \<in> A" by (auto simp: ith_conv) (metis eq_upto_BAD_mem)
  moreover
  { assume "good P lb"
    then obtain i j where "i < j" and "P (lb i) (lb j)" by (auto simp: good_def)
    from * have "lb j \<in> ith (eq_upto (BAD P) lb j) j" by (auto)
    then obtain g where "g \<in> eq_upto (BAD P) lb j" and "g j = lb j" by force
    then have "\<forall>k \<le> j. g k = lb k" by (auto simp: order_le_less)
    with `i < j` and `P (lb i) (lb j)` have "P (g i) (g j)" by auto
    with `i < j` have "good P g" by (auto simp: good_def)
    with `g \<in> eq_upto (BAD P) lb j` have False by auto }
  ultimately show ?thesis by blast
qed

text {*There is no infinite bad sequence that is strictly smaller than @{term lb}.*}
lemma lb_lower_bound:
  "\<forall>g. (lb, g) \<in> gseq \<longrightarrow> g \<notin> BAD P"
proof (intro allI impI)
  fix g
  assume "(lb, g) \<in> gseq"
  then obtain i where "g i \<in> A" and "less (g i) (lb i)"
    and "\<forall>j < i. lb j = g j" by (auto simp: gseq_iff)
  moreover with lb_minimal
    have "g i \<notin> ith (eq_upto (BAD P) lb i) i" by auto
  ultimately show "g \<notin> BAD P" by blast
qed

text {*If there is at least one bad sequence, then there is also a minimal one.*}
lemma lower_bound_ex:
  "\<exists>f \<in> BAD P. \<forall>g. (f, g) \<in> gseq \<longrightarrow> g \<notin> BAD P"
  using lb_BAD and lb_lower_bound by blast

lemma gseq_conv:
  "(f, g) \<in> gseq \<longleftrightarrow> f \<noteq> g \<and> (f, g) \<in> geseq"
  by (auto simp: gseq_def geseq_def dest: less_not_eq)

text {*There is a minimal bad sequence.*}
lemma mbs:
  "\<exists>f \<in> BAD P. \<forall>g. (f, g) \<in> gseq \<longrightarrow> good P g"
  using lower_bound_ex by (auto simp: gseq_conv geseq_iff)

end

end

end

end

