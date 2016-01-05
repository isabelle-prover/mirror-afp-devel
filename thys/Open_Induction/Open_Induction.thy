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
  A set \<open>B\<close> has the \emph{lower bound} \<open>x\<close> iff \<open>x\<close> is
  less than or equal to every element of \<open>B\<close>.
\<close>
definition "lb P B x \<longleftrightarrow> (\<forall>y\<in>B. P\<^sup>=\<^sup>= x y)"

lemma lbI [Pure.intro]:
  "(\<And>y. y \<in> B \<Longrightarrow> P\<^sup>=\<^sup>= x y) \<Longrightarrow> lb P B x"
by (auto simp: lb_def)

text \<open>
  A set \<open>B\<close> has the \emph{greatest lower bound} \<open>x\<close> iff \<open>x\<close> is
  a lower bound of \<open>B\<close> \emph{and} less than or equal to every
  other lower bound of \<open>B\<close>.
\<close>
definition "glb P B x \<longleftrightarrow> lb P B x \<and> (\<forall>y. lb P B y \<longrightarrow> P\<^sup>=\<^sup>= y x)"

lemma glbI [Pure.intro]:
  "lb P B x \<Longrightarrow> (\<And>y. lb P B y \<Longrightarrow> P\<^sup>=\<^sup>= y x) \<Longrightarrow> glb P B x"
by (auto simp: glb_def)

text \<open>Antisymmetric relations have unique glbs.\<close>
lemma glb_unique:
  "antisymp_on P A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> glb P B x \<Longrightarrow> glb P B y \<Longrightarrow> x = y"
by (auto simp: glb_def antisymp_on_def)

context pred_on
begin

lemma chain_glb:
  assumes "transp_on (op \<sqsubset>) A"
  shows "chain C \<Longrightarrow> C \<noteq> {} \<Longrightarrow> glb (op \<sqsubset>) C x \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> chain ({y} \<union> C)"
using assms [unfolded transp_on_def] unfolding chain_def glb_def lb_def by blast


subsection \<open>Open Properties\<close>

definition "open Q \<longleftrightarrow> (\<forall>C. chain C \<and> C \<noteq> {} \<and> (\<exists>x\<in>A. glb (op \<sqsubset>) C x \<and> Q x) \<longrightarrow> (\<exists>y\<in>C. Q y))"

lemma openI [Pure.intro]:
  "(\<And>C. chain C \<Longrightarrow> C \<noteq> {} \<Longrightarrow> \<exists>x\<in>A. glb (op \<sqsubset>) C x \<and> Q x \<Longrightarrow> \<exists>y\<in>C. Q y) \<Longrightarrow> open Q"
by (auto simp: open_def)

lemma open_glb:
  "\<lbrakk>chain C; C \<noteq> {}; open Q; \<forall>x\<in>C. \<not> Q x; x \<in> A; glb (op \<sqsubset>) C x\<rbrakk> \<Longrightarrow> \<not> Q x"
by (auto simp: open_def)


subsection \<open>Downward Completeness\<close>

text \<open>
  A relation \<open>\<sqsubset>\<close> is \emph{downward-complete} iff
  every non-empty \<open>\<sqsubset>\<close>-chain has a greatest lower bound.
\<close>
definition "downward_complete \<longleftrightarrow> (\<forall>C. chain C \<and> C \<noteq> {} \<longrightarrow> (\<exists>x\<in>A. glb (op \<sqsubset>) C x))"

lemma downward_completeI [Pure.intro]:
  assumes "\<And>C. chain C \<Longrightarrow> C \<noteq> {} \<Longrightarrow> \<exists>x\<in>A. glb (op \<sqsubset>) C x"
  shows "downward_complete"
using assms by (auto simp: downward_complete_def)

end

abbreviation "open_on P Q A \<equiv> pred_on.open A P Q"
abbreviation "dc_on P A \<equiv> pred_on.downward_complete A P"
lemmas open_on_def = pred_on.open_def
  and dc_on_def = pred_on.downward_complete_def

lemma dc_onI [Pure.intro]:
  assumes "\<And>C. chain_on P C A \<Longrightarrow> C \<noteq> {} \<Longrightarrow> \<exists>x\<in>A. glb P C x"
  shows "dc_on P A"
using assms by (auto simp: dc_on_def)

lemma open_onI [Pure.intro]:
  "(\<And>C. chain_on P C A \<Longrightarrow> C \<noteq> {} \<Longrightarrow> \<exists>x\<in>A. glb P C x \<and> Q x \<Longrightarrow> \<exists>y\<in>C. Q y) \<Longrightarrow> open_on P Q A"
by (auto simp: open_on_def)

lemma chain_on_reflclp:
  "chain_on P\<^sup>=\<^sup>= A C \<longleftrightarrow> chain_on P A C"
by (auto simp: pred_on.chain_def)

lemma lb_reflclp:
  "lb P\<^sup>=\<^sup>= B x \<longleftrightarrow> lb P B x"
by (auto simp: lb_def)

lemma glb_reflclp:
  "glb P\<^sup>=\<^sup>= B x \<longleftrightarrow> glb P B x"
by (auto simp: glb_def lb_reflclp)

lemma dc_on_reflclp:
  "dc_on P\<^sup>=\<^sup>= A \<longleftrightarrow> dc_on P A"
by (auto simp: dc_on_def chain_on_reflclp glb_reflclp)


subsection \<open>The Open Induction Schema\<close>

lemma open_induct_on [consumes 4, case_names less]:
  assumes po: "qo_on P A" and "dc_on P A" and "open_on P Q A"
    and "x \<in> A"
    and ind: "\<And>x. \<lbrakk>x \<in> A; \<And>y. \<lbrakk>y \<in> A; strict P y x\<rbrakk> \<Longrightarrow> Q y\<rbrakk> \<Longrightarrow> Q x"
  shows "Q x"
proof (rule ccontr)
  assume "\<not> Q x"
  let ?A = "{x\<in>A. \<not> Q x}"
  interpret A?: pred_on ?A P .
  from Hausdorff obtain M
    where chain: "chain M"
    and max: "\<And>C. chain C \<Longrightarrow> M \<subseteq> C \<Longrightarrow> M = C" by (auto simp: maxchain_def)
  then have "M \<subseteq> ?A" by (auto simp: chain_def)
  show False
  proof (cases "M = {}")
    assume "M = {}"
    moreover have "chain {x}"
      using refl and \<open>x \<in> A\<close> and \<open>\<not> Q x\<close> by (simp add: chain_def)
    ultimately show False using max by blast
  next
    interpret pred_on A P .
    assume "M \<noteq> {}"
    have "?A \<subseteq> A" by blast
    with chain have "chain M" by (auto simp: chain_def A.chain_def)
    moreover with \<open>dc_on P A\<close> and \<open>M \<noteq> {}\<close> obtain m
      where "m \<in> A" and "glb P M m" by (auto simp: downward_complete_def)
    ultimately have "\<not> Q m" and "m \<in> ?A"
      using open_glb [OF _ \<open>M \<noteq> {}\<close> \<open>open_on P Q A\<close> _ _ \<open>glb P M m\<close>]
      and \<open>M \<subseteq> ?A\<close> by auto
    from ind [OF \<open>m \<in> A\<close>] and \<open>\<not> Q m\<close> obtain y
      where "y \<in> A" and "strict P y m" and "\<not> Q y" by blast
    then have "P y m" and "y \<in> ?A" by simp+
    from transp_on_subset [OF \<open>?A \<subseteq> A\<close> qo_on_imp_transp_on [OF po]]
      have "transp_on P ?A" .
    from A.chain_glb [OF this chain \<open>M \<noteq> {}\<close> \<open>glb P M m\<close> \<open>m \<in> ?A\<close> \<open>y \<in> ?A\<close> \<open>P y m\<close>]
      have "A.chain ({y} \<union> M)" .
    show False
    proof (cases "y \<in> M")
      assume "y \<in> M"
      with \<open>glb P M m\<close> and \<open>strict P y m\<close>
        show False by (auto simp: glb_def lb_def)
    next
      assume "y \<notin> M"
      with max [OF \<open>A.chain ({y} \<union> M)\<close>] show False by blast
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
  have "qo_on (op \<le>) UNIV" by (auto simp: qo_on_def transp_on_def reflp_on_def dest: order_trans)
  from open_induct_on [OF this assms(1,2)]
    show "Q x" using assms(3) unfolding less_le_not_le by blast
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
