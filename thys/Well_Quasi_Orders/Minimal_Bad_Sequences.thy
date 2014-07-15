(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Constructing Minimal Bad Sequences *}

theory Minimal_Bad_Sequences
imports Restricted_Predicates
begin

text {*
  The set of all infinite sequences over elements from @{term A}.
*}
definition "SEQ A = {f::nat \<Rightarrow> 'a. \<forall>i. f i \<in> A}"

lemma SEQ_iff [iff]:
  "f \<in> SEQ A \<longleftrightarrow> (\<forall>i. f i \<in> A)"
  by (auto simp: SEQ_def)

text {*
  An infinite sequence is \emph{good} whenever there are indices @{term "i < j"} such that
  @{term "P (f i) (f j)"}.
*}
definition good :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "good P f \<longleftrightarrow> (\<exists>i j. i < j \<and> P (f i) (f j))"

text {*
  A sequence that is not good is called \emph{bad}.
*}
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

text {*
  A locale capturing the construction of minimal bad sequences over values from @{term "A"}. Where
  minimality is to be understood w.r.t.\ @{term size} of an element.
*}
locale mbs =
  fixes A :: "('a :: size) set"
begin

text {*
  Since the @{term size} is a well-founded measure, whenever some element satisfies a property
  @{term P}, then there is a size-minimal such element.
*}
lemma minimal:
  assumes "x \<in> A" and "P x"
  shows "\<exists>y \<in> A. size y \<le> size x \<and> P y \<and> (\<forall>z \<in> A. size z < size y \<longrightarrow> \<not> P z)"
using assms
proof (induction x taking: size rule: measure_induct)
  case (1 x)
  then show ?case
  proof (cases "\<forall>y \<in> A. size y < size x \<longrightarrow> \<not> P y")
    case True
    with 1 show ?thesis by blast
  next
    case False
    then obtain y where "y \<in> A" and "size y < size x" and "P y" by blast
    with "1.IH" show ?thesis by (fastforce elim!: order_trans)
  qed
qed

lemma less_not_eq [simp]:
  "x \<in> A \<Longrightarrow> size x < size y \<Longrightarrow> x = y \<Longrightarrow> False"
  by simp

text {*
  The set of all bad sequences over @{term A}.
*}
definition "BAD P = {f \<in> SEQ A. bad P f}"

lemma BAD_iff [iff]:
  "f \<in> BAD P \<longleftrightarrow> (\<forall>i. f i \<in> A) \<and> bad P f"
  by (auto simp: BAD_def)

text {*
  A partial order on infinite bad sequences.
*}
definition geseq :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set"
where
  "geseq =
    {(f, g). f \<in> SEQ A \<and> g \<in> SEQ A \<and> (f = g \<or> (\<exists>i. size (g i) < size (f i) \<and> (\<forall>j < i. f j = g j)))}"

text {*
  The strict part of the above order.
*}
definition gseq :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set" where
  "gseq = {(f, g). f \<in> SEQ A \<and> g \<in> SEQ A \<and> (\<exists>i. size (g i) < size (f i) \<and> (\<forall>j < i. f j = g j))}"

lemma geseq_iff:
  "(f, g) \<in> geseq \<longleftrightarrow>
    f \<in> SEQ A \<and> g \<in> SEQ A \<and> (f = g \<or> (\<exists>i. size (g i) < size (f i) \<and> (\<forall>j < i. f j = g j)))"
  by (auto simp: geseq_def)

lemma gseq_iff:
  "(f, g) \<in> gseq \<longleftrightarrow> f \<in> SEQ A \<and> g \<in> SEQ A \<and> (\<exists>i. size (g i) < size (f i) \<and> (\<forall>j < i. f j = g j))"
  by (auto simp: gseq_def)

lemma geseqE:
  assumes "(f, g) \<in> geseq"
    and "\<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; f = g\<rbrakk> \<Longrightarrow> Q"
    and "\<And>i. \<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; size (g i) < size (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: geseq_iff)

lemma gseqE:
  assumes "(f, g) \<in> gseq"
    and "\<And>i. \<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; size (g i) < size (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: gseq_iff)

text {*
  The @{term i}-th "column" of a set @{term B} of infinite sequences.
*}
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

context
  fixes B :: "'a set"
  assumes subset_A: "B \<subseteq> A" and ne: "B \<noteq> {}"
begin

text {*
  A minimal element (w.r.t.~@{term size}) from a set.
*}
definition "min_elt = (SOME x. x \<in> B \<and> (\<forall>y \<in> A. size y < size x \<longrightarrow> y \<notin> B))"

lemma min_elt_ex:
  "\<exists>x. x \<in> B \<and> (\<forall>y \<in> A. size y < size x \<longrightarrow> y \<notin> B)"
  using subset_A and ne using minimal [of _ "\<lambda>x. x \<in> B"] by auto

lemma min_elt_mem:
  "min_elt \<in> B"
  using someI_ex [OF min_elt_ex] by (auto simp: min_elt_def)

lemma min_elt_minimal:
  assumes "y \<in> A" and "size y < size min_elt"
  shows "y \<notin> B"
  using someI_ex [OF min_elt_ex] and assms by (auto simp: min_elt_def)

end

end

text {*
  The restriction of a set @{term "B"} of sequences to sequences that are equal to a given sequence
  @{term f} up to position @{term i}.
*}
definition eq_upto :: "(nat \<Rightarrow> 'a) set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) set"
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

text {*
  A lower bound to all sequences in a set of sequences @{term B}.
*}
fun lb :: "nat \<Rightarrow> 'a" where
  lb: "lb i = min_elt (ith (eq_upto (BAD P) lb i) i)"

declare lb.simps [simp del]

lemma eq_upto_BAD_mem:
  assumes "f \<in> eq_upto (BAD P) g i"
  shows "f j \<in> A"
  using assms by (auto)

text {*
  Assume that there is some infinite bad sequence @{term h}.
*}
context
  fixes h :: "nat \<Rightarrow> 'a"
  assumes BAD_ex: "h \<in> BAD P"
begin

text {*
  When there is a bad sequence, then filtering @{term "BAD P"} w.r.t.~positions in @{term lb} never
  yields an empty set of sequences.
*}
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
  ultimately have "?A i \<subseteq> A" and "?A i \<noteq> {}" by (auto simp: ith_def)
  from min_elt_mem [OF this, folded lb] obtain f
    where "f \<in> eq_upto (BAD P) lb (Suc i)" by (auto dest: eq_upto_Suc)
  then show ?case by blast
qed

lemma non_empty_ith:
  shows "ith (eq_upto (BAD P) lb i) i \<subseteq> A"
  and "ith (eq_upto (BAD P) lb i) i \<noteq> {}"
  using eq_upto_BAD_non_empty [of i] by auto

lemmas
  lb_minimal = min_elt_minimal [OF non_empty_ith, folded lb] and
  lb_mem = min_elt_mem [OF non_empty_ith, folded lb]

text {*
  @{term "lb"} is a infinite bad sequence.
*}
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

text {*
  There is no infinite bad sequence that is strictly smaller than @{term lb}.
*}
lemma lb_lower_bound:
  "\<forall>g. (lb, g) \<in> gseq \<longrightarrow> g \<notin> BAD P"
proof (intro allI impI)
  fix g
  assume "(lb, g) \<in> gseq"
  then obtain i where "g i \<in> A" and "size (g i) < size (lb i)"
    and "\<forall>j < i. lb j = g j" by (auto simp: gseq_iff)
  moreover with lb_minimal
    have "g i \<notin> ith (eq_upto (BAD P) lb i) i" by auto
  ultimately show "g \<notin> BAD P" by blast
qed

text {*
  If there is at least one bad sequence, then there is also a minimal one.
*}
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

