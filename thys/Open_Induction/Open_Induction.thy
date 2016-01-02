(*  Title:      Open Induction
    Author:     Mizuhito Ogawa
                Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Open Induction\<close>

theory Open_Induction
imports "../Well_Quasi_Orders/Restricted_Predicates"
begin


subsection \<open>(Greatest) Lower Bounds and Chains\<close>

text \<open>
  A set \<open>B\<close> has the \emph{lower bound} \<open>x\<close> w.r.t.\ the order
  \<open>P\<close> iff \<open>x\<close> is less than or equal to every element of \<open>B\<close>.
\<close>
definition "lb P B x \<longleftrightarrow> (\<forall>y\<in>B. P\<^sup>=\<^sup>= x y)"

text \<open>
  A set \<open>B\<close> has the \emph{greatest lower bound} \<open>x\<close> (w.r.t.\ \<open>P\<close>)
  iff \<open>x\<close> is a lower bound \emph{and} less than or equal to every
  other lower bound of \<open>B\<close>.
\<close>
definition "glb P B x \<longleftrightarrow> lb P B x \<and> (\<forall>y. lb P B y \<longrightarrow> P\<^sup>=\<^sup>= y x)"

text \<open>Antisymmetric relations have unique glbs.\<close>
lemma glb_unique:
  "antisymp_on P A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> glb P B x \<Longrightarrow> glb P B y \<Longrightarrow> x = y"
by (auto simp: glb_def antisymp_on_def)

text \<open>
  A subset \<open>C\<close> of \<open>A\<close> is a \emph{chain} on \<open>A\<close> (w.r.t.\ \<open>P\<close>)
  iff for all pairs of elements of \<open>C\<close>, one is less than or equal
  to the other one.
\<close>
definition chain_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "chain_on P C A \<longleftrightarrow> C \<subseteq> A \<and> (\<forall>x\<in>C. \<forall>y\<in>C. P\<^sup>=\<^sup>= x y \<or> P\<^sup>=\<^sup>= y x)"

text \<open>
  A chain \<open>M\<close> on \<open>A\<close> (w.r.t.\ \<open>P\<close>) is a \emph{maximal chain} iff
  there is no chain on \<open>A\<close> that is a superset of \<open>M\<close>.
\<close>
definition "max_chain_on P M A \<longleftrightarrow> chain_on P M A \<and> (\<forall>C. chain_on P C A \<and> M \<subseteq> C \<longrightarrow> M = C)"

lemma chain_onI [Pure.intro!]:
  "C \<subseteq> A \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> C; y \<in> C\<rbrakk> \<Longrightarrow> P x y \<or> P y x \<or> x = y) \<Longrightarrow> chain_on P C A"
unfolding chain_on_def by blast

lemma chain_on_subset:
  "A \<subseteq> B \<Longrightarrow> chain_on P C A \<Longrightarrow> chain_on P C B"
by (force simp: chain_on_def)

lemma chain_on_imp_subset:
  "chain_on P C A \<Longrightarrow> C \<subseteq> A"
by (simp add: chain_on_def)

lemma chain_on_Union:
  assumes "C \<in> chains {C. chain_on P C A}" (is "C \<in> chains ?A")
  shows "chain_on P (\<Union>C) A"
proof
  have "C \<subseteq> ?A" and *: "\<And>x y. x \<in> C \<Longrightarrow> y \<in> C \<Longrightarrow> x \<subseteq> y \<or> y \<subseteq> x"
    using assms by (auto simp: chains_def chain_subset_def)
  then show "\<Union>C \<subseteq> A" unfolding chain_on_def by blast
  fix x y assume "x \<in> \<Union>C" and "y \<in> \<Union>C"
  then obtain X Y
    where "X \<in> C" and "Y \<in> C" and "x \<in> X" and "y \<in> Y" by auto
  with \<open>C \<subseteq> ?A\<close> have "X \<subseteq> A" and "Y \<subseteq> A"
    and "chain_on P X A" and "chain_on P Y A" unfolding chain_on_def by auto
  with \<open>x \<in> X\<close> and \<open>y \<in> Y\<close> show "P x y \<or> P y x \<or> x = y"
    using * [OF \<open>X \<in> C\<close> \<open>Y \<in> C\<close>]
    unfolding chain_on_def by blast
qed

lemma chain_on_glb:
  assumes "qo_on P A"
  shows "chain_on P C A \<Longrightarrow> C \<noteq> {} \<Longrightarrow> glb P C x \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> P y x \<Longrightarrow> chain_on P ({y} \<union> C) A"
using qo_on_imp_reflp_on [OF assms, unfolded reflp_on_def, rule_format, of y]
  and qo_on_imp_transp_on [OF assms, unfolded transp_on_def]
  unfolding chain_on_def glb_def lb_def by blast


subsection \<open>Open Properties\<close>

definition "open_on P Q A \<longleftrightarrow>
    (\<forall>C. chain_on P C A \<and> C \<noteq> {} \<and> (\<exists>x\<in>A. glb P C x \<and> Q x) \<longrightarrow> (\<exists>y\<in>C. Q y))"

lemma open_on_glb:
  "\<lbrakk>chain_on P C A; C \<noteq> {}; open_on P Q A; \<forall>x\<in>C. \<not> Q x; x \<in> A; glb P C x\<rbrakk> \<Longrightarrow> \<not> Q x"
by (auto simp: open_on_def)

lemma max_chain_on_exists:
  "\<exists>M. max_chain_on P M A"
proof -
  let ?S = "{C. chain_on P C A}"
  have "\<And>C. C \<in> chains ?S \<Longrightarrow> \<Union>C \<in> ?S"
    using chain_on_Union and chain_on_imp_subset by blast
  with Zorn_Lemma [of ?S]
    obtain M where "M \<in> ?S" and *: "\<forall>z\<in>?S. M \<subseteq> z \<longrightarrow> z = M" by blast
  then have "M \<subseteq> A" and "chain_on P M A" by (auto dest: chain_on_imp_subset)
  moreover
  { fix C assume "chain_on P C A" and "M \<subseteq> C"
    with * have "M = C"
      using chain_on_imp_subset [OF \<open>chain_on P C A\<close>] by blast }
  ultimately show "?thesis" by (auto simp: max_chain_on_def)
qed


subsection \<open>Downward Completeness\<close>

text \<open>
  An relation \<open>P\<close> is \emph{downward-complete} on \<open>A\<close> iff every non-empty
  chain on \<open>A\<close> has a greatest lower bound in \<open>A\<close>.
\<close>
definition "dc_on P A \<longleftrightarrow> (\<forall>C. chain_on P C A \<and> C \<noteq> {} \<longrightarrow> (\<exists>x\<in>A. glb P C x))"


subsection \<open>The Open Induction Schema\<close>

lemma open_induct_on [consumes 4, case_names less]:
  assumes "qo_on P A" and "dc_on P A" and "open_on P Q A"
    and "x \<in> A"
    and ind: "\<And>x. \<lbrakk>x \<in> A; \<And>y. \<lbrakk>y \<in> A; strict P y x\<rbrakk> \<Longrightarrow> Q y\<rbrakk> \<Longrightarrow> Q x"
  shows "Q x"
proof (rule ccontr)
  note refl =
    qo_on_imp_reflp_on [OF \<open>qo_on P A\<close>, unfolded reflp_on_def, rule_format]
  assume "\<not> Q x"
  let ?A = "{x\<in>A. \<not> Q x}"
  from max_chain_on_exists [of P ?A] obtain M
    where chain: "chain_on P M ?A"
    and max: "\<And>C. chain_on P C ?A \<Longrightarrow> M \<subseteq> C \<Longrightarrow> M = C" by (auto simp: max_chain_on_def)
  then have "M \<subseteq> ?A" by (auto simp: chain_on_imp_subset)
  show False
  proof (cases "M = {}")
    assume "M = {}"
    moreover have "chain_on P {x} ?A"
      using refl and \<open>x \<in> A\<close> and \<open>\<not> Q x\<close> by (simp add: chain_on_def)
    ultimately show False using max by blast
  next
    assume "M \<noteq> {}"
    have "?A \<subseteq> A" by blast
    with chain have "chain_on P M A"
      using chain_on_subset by blast
    moreover with \<open>dc_on P A\<close> and \<open>M \<noteq> {}\<close> obtain m
      where "m \<in> A" and "glb P M m" by (auto simp: dc_on_def)
    ultimately have "\<not> Q m" and "m \<in> ?A"
      using open_on_glb [OF _ \<open>M \<noteq> {}\<close> \<open>open_on P Q A\<close> _ _ \<open>glb P M m\<close>]
      and \<open>M \<subseteq> ?A\<close> by auto
    from ind [OF \<open>m \<in> A\<close>] and \<open>\<not> Q m\<close> obtain y
      where "y \<in> A" and "strict P y m" and "\<not> Q y" by blast
    then have "P y m" and "y \<in> ?A" by simp+
    from qo_on_subset [OF \<open>?A \<subseteq> A\<close> \<open>qo_on P A\<close>] have "qo_on P ?A" .
    from chain_on_glb [OF this chain, of m y]
     and \<open>M \<noteq> {}\<close> and \<open>glb P M m\<close> and \<open>m \<in> ?A\<close> and \<open>y \<in> ?A\<close> and \<open>P y m\<close>
      have "chain_on P ({y} \<union> M) ?A" by blast
    show False
    proof (cases "y \<in> M")
      assume "y \<in> M"
      with \<open>glb P M m\<close> and \<open>strict P y m\<close>
        show False by (auto simp add: glb_def lb_def)
    next
      assume "y \<notin> M"
      with max [OF \<open>chain_on P ({y} \<union> M) ?A\<close>] show False by blast
    qed
  qed
qed


subsection \<open>Universal Open Induction Schemas\<close>

text \<open>Open induction on quasi-orders (i.e., @{class preorder}).\<close>
lemma (in preorder) dc_open_induct [consumes 2, case_names less]:
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


subsection \<open>Type Class of Downward Complete Orders\<close>

class dcorder = preorder +
  assumes dc: "\<lbrakk>chain_on (op \<le>) C UNIV; C \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>x. glb (op \<le>) C x"
begin

lemma dc_on_UNIV: "dc_on (op \<le>) UNIV"
using dc unfolding dc_on_def by blast

text \<open>Open induction on downward-complete orders.\<close>
lemmas open_induct [consumes 1, case_names less] = dc_open_induct [OF dc_on_UNIV]

end

end
