(*  Title:      Open Induction
    Author:     Mizuhito Ogawa
                Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Open Induction *}

theory Open_Induction
imports
  Main
  "~~/src/HOL/Library/Zorn"
  "../Well_Quasi_Orders/Restricted_Predicates"
begin


subsection {* (Greatest) Lower Bounds and Chains *}

text {*A set @{term B} has the \emph{lower bound} @{term x} w.r.t.\ to the order
@{term_type "P :: 'a => 'a => bool"} iff @{term x} is less than or equal to every element
of @{term B}.*}
definition lb where
  "lb P B x \<equiv> \<forall>y\<in>B. P x y"

text {*A set @{term B} has the \emph{greatest lower bound} @{term x} (w.r.t.\ @{term P})
iff @{term x} is a lower bound \emph{and} less than or equal to every other lower bound
of @{term B}.*}
definition glb where
  "glb P B x \<equiv> lb P B x \<and> (\<forall>y. lb P B y \<longrightarrow> P y x)"

text {*A subset @{term C} of @{term A} is a \emph{chain} on @{term A} (w.r.t.\ @{term P})
iff for all pairs of elements of @{term C}, one is less than or equal to the other one.*}
definition chain_on where
  "chain_on P C A \<equiv> C \<subseteq> A \<and> (\<forall>x\<in>C. \<forall>y\<in>C. P x y \<or> P y x)"

text {*A chain @{term M} on @{term A} (w.r.t.\ @{term P}) is a \emph{maximal chain} iff
there is no chain on @{term A} that is a superset of @{term M}.*}
definition max_chain_on where
  "max_chain_on P M A \<equiv> chain_on P M A \<and> (\<forall>C. chain_on P C A \<and> M \<subseteq> C \<longrightarrow> M = C)"

lemma chain_onI [Pure.intro!]:
  "C \<subseteq> A \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> C; y \<in> C\<rbrakk> \<Longrightarrow> P x y \<or> P y x) \<Longrightarrow> chain_on P C A"
  unfolding chain_on_def by blast

lemma chain_on_subset:
  "A \<subseteq> B \<Longrightarrow> chain_on P C A \<Longrightarrow> chain_on P C B"
  unfolding chain_on_def by force

lemma chain_on_imp_subset:
  "chain_on P C A \<Longrightarrow> C \<subseteq> A" by (simp add: chain_on_def)

lemma chain_on_Union:
  assumes "C \<in> Zorn.chain {C. chain_on P C A}" (is "C \<in> Zorn.chain ?A")
  shows "chain_on P (\<Union>C) A"
proof
  from assms have "C \<subseteq> ?A" and
    *[rule_format]: "\<forall>x\<in>C. \<forall>y\<in>C. x \<subseteq> y \<or> y \<subseteq> x"
    by (auto simp: chain_def chain_subset_def)
  then show "\<Union>C \<subseteq> A" unfolding chain_on_def by blast
  fix x y assume "x \<in> \<Union>C" and "y \<in> \<Union>C"
  then obtain X Y
    where "X \<in> C" and "Y \<in> C" and "x \<in> X" and "y \<in> Y" by auto
  with `C \<subseteq> ?A` have "X \<subseteq> A" and "Y \<subseteq> A"
    and "chain_on P X A" and "chain_on P Y A" unfolding chain_on_def by auto
  with `x \<in> X` and `y \<in> Y` show "P x y \<or> P y x"
    using * [OF `X \<in> C` `Y \<in> C`]
    unfolding chain_on_def by blast
qed

lemma chain_on_glb:
  assumes "qo_on P A"
  shows "chain_on P C A \<Longrightarrow> C \<noteq> {} \<Longrightarrow> glb P C x \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> P y x \<Longrightarrow> chain_on P ({y} \<union> C) A"
  using qo_on_imp_reflp_on [OF assms, unfolded reflp_on_def, rule_format, of y]
    and qo_on_imp_transp_on [OF assms, unfolded transp_on_def]
  unfolding chain_on_def glb_def lb_def by blast


subsection {* Open Properties *}

definition open_on where
  "open_on P Q A \<equiv>
    \<forall>C. chain_on P C A \<and> C \<noteq> {} \<and> (\<exists>x\<in>A. glb P C x \<and> Q x) \<longrightarrow> (\<exists>y\<in>C. Q y)"

lemma open_on_glb:
  "\<lbrakk>chain_on P C A; C \<noteq> {}; open_on P Q A; \<forall>x\<in>C. \<not> Q x; x \<in> A; glb P C x\<rbrakk> \<Longrightarrow> \<not> Q x"
  by (auto simp: open_on_def)

lemma max_chain_on_exists:
  "\<exists>M. max_chain_on P M A"
proof -
  let ?S = "{C. chain_on P C A}"
  have "\<And>C. C \<in> Zorn.chain ?S \<Longrightarrow> \<Union>C \<in> ?S"
    using chain_on_Union and chain_on_imp_subset by blast
  with Zorn_Lemma [of ?S]
    obtain M where "M \<in> ?S" and *: "\<forall>z\<in>?S. M \<subseteq> z \<longrightarrow> M = z" by blast
  then have "M \<subseteq> A" and "chain_on P M A" by (auto dest: chain_on_imp_subset)
  moreover {
    fix C assume "chain_on P C A" and "M \<subseteq> C"
    with * have "M = C"
      using chain_on_imp_subset [OF `chain_on P C A`]
      by blast }
  ultimately show "?thesis" by (auto simp: max_chain_on_def)
qed


subsection {* Downward Completeness *}

text {*An order @{term P} is \emph{downward-complete} on @{term A} iff every non-empty
chain on @{term A} has a greatest lower bound in @{term A}.*}
definition dc_on where
  "dc_on P A \<equiv> \<forall>C. chain_on P C A \<and> C \<noteq> {} \<longrightarrow> (\<exists>x\<in>A. glb P C x)"


subsection {* The Open Induction Schema *}

lemma open_induct_on [consumes 4]:
  assumes "qo_on P A" and "dc_on P A" and "open_on P Q A"
    and "x \<in> A"
    and ind: "\<And>x. \<lbrakk>x \<in> A; \<And>y. \<lbrakk>y \<in> A; strict P y x\<rbrakk> \<Longrightarrow> Q y\<rbrakk> \<Longrightarrow> Q x"
  shows "Q x"
proof (rule ccontr)
  note refl =
    qo_on_imp_reflp_on [OF `qo_on P A`, unfolded reflp_on_def, rule_format]
  assume "\<not> Q x"
  let ?A = "{x\<in>A. \<not> Q x}"
  from max_chain_on_exists [of P ?A] obtain M where
    chain: "chain_on P M ?A" and
    max: "\<And>C. chain_on P C ?A \<Longrightarrow> M \<subseteq> C \<Longrightarrow> M = C" by (auto simp: max_chain_on_def)
  from chain have "M \<subseteq> ?A" by (auto simp: chain_on_imp_subset)
  show False
  proof (cases "M = {}")
    assume "M = {}"
    moreover have "chain_on P {x} ?A"
      using refl and `x \<in> A` and `\<not> Q x` by (simp add: chain_on_def)
    ultimately show False using max by blast
  next
    assume "M \<noteq> {}"
    have "?A \<subseteq> A" by blast
    with chain have "chain_on P M A"
      using chain_on_subset by blast
    moreover with `dc_on P A` and `M \<noteq> {}` obtain m where
      "m \<in> A" and "glb P M m"
      unfolding dc_on_def by auto
    ultimately have "\<not> Q m" and "m \<in> ?A"
      using open_on_glb [OF _ `M \<noteq> {}` `open_on P Q A` _ _ `glb P M m`]
      and `M \<subseteq> ?A` by auto
    from ind [OF `m \<in> A`] and `\<not> Q m` obtain y where
      "y \<in> A" and "strict P y m" and "\<not> Q y" by blast
    then have "P y m" and "y \<in> ?A" by simp+
    from qo_on_subset [OF `?A \<subseteq> A` `qo_on P A`] have "qo_on P ?A" .
    from chain_on_glb [OF this chain, of m y]
     and `M \<noteq> {}` and `glb P M m` and `m \<in> ?A` and `y \<in> ?A` and `P y m`
      have "chain_on P ({y} \<union> M) ?A" by blast
    show False
    proof (cases "y \<in> M")
      assume "y \<in> M"
      with `glb P M m` and `strict P y m`
        show False by (simp add: glb_def lb_def)
    next
      assume "y \<notin> M"
      with max [OF `chain_on P ({y} \<union> M) ?A`] show False by blast
    qed
  qed
qed


subsection {* Universal Open Induction Schemas *}

text {*Open induction on quasi-orders (i.e., @{class preorder}).*}
lemma (in preorder) dc_open_induct [consumes 2]:
  assumes "dc_on (op \<le>) UNIV"
    and "open_on (op \<le>) Q UNIV"
    and "\<And>x. (\<And>y. y < x \<Longrightarrow> Q y) \<Longrightarrow> Q x"
  shows "Q x"
proof -
  have "qo_on (op \<le>) UNIV"
    unfolding qo_on_UNIV_conv
    unfolding less_le_not_le [symmetric] ..
  moreover have "dc_on (op \<le>) UNIV" by fact
  ultimately show "Q x"
    using assms and open_induct_on [of "op \<le>" UNIV Q]
    unfolding less_le_not_le by blast
qed


subsection {* Type Class of Downward Complete Orders *}

class dcorder = preorder +
  assumes dc: "\<lbrakk>chain_on (op \<le>) C UNIV; C \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. glb (op \<le>) C x)"
begin

lemma dc_on_UNIV: "dc_on (op \<le>) UNIV"
  using dc unfolding dc_on_def by blast

text {*Open induction on downward-complete orders.*}
lemmas open_induct [consumes 1] = dc_open_induct [OF dc_on_UNIV]

end

end
