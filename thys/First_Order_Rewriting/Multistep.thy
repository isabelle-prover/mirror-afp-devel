section \<open>Multi-Step Rewriting\<close>

theory Multistep
  imports Trs
begin

text \<open>Multi-step rewriting (without proof terms).\<close>
inductive_set
  mstep :: "('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
  for R
  where
    Var: "(Var x, Var x) \<in> mstep R" |
    args: "\<And>f n ss ts. \<lbrakk>length ss = n; length ts = n;
    \<forall>i<n. (ss ! i, ts ! i) \<in> mstep R\<rbrakk> \<Longrightarrow>
    (Fun f ss, Fun f ts) \<in> mstep R" |
    rule: "\<And>l r \<sigma> \<tau>. \<lbrakk>(l, r) \<in> R; \<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> mstep R\<rbrakk> \<Longrightarrow>
    (l \<cdot> \<sigma>, r \<cdot> \<tau>) \<in> mstep R"

lemma mstep_refl [simp]:
  "(t, t) \<in> mstep R"
  by (induct t) (auto intro: mstep.intros)

lemma mstep_ctxt:
  assumes "(s, t) \<in> mstep R"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> mstep R"
proof (induction C)
  case Hole with assms show ?case by simp
next
  case (More f ss C ts)
  let ?ss = "ss @ C\<langle>s\<rangle> # ts"
  let ?ts = "ss @ C\<langle>t\<rangle> # ts"
  { fix i assume "i = length ss"
    then have "(?ss ! i, ?ts ! i) \<in> mstep R"
      using More.IH by simp }
  moreover
  { fix i assume "i < length ss"
    then have "(?ss ! i, ?ts ! i) \<in> mstep R"
      by (simp add: nth_append) }
  moreover
  { fix i assume "i < length ?ss" and "i > length ss"
    then have "(?ss ! i, ?ts ! i) \<in> mstep R"
      by (simp add: nth_append) }
  ultimately
  have "\<forall>i<length ?ss.  (?ss ! i, ?ts ! i) \<in> mstep R"
    by (metis linorder_neqE_nat)
  from mstep.args [OF _ _ this, simplified]
  show ?case by simp
qed

lemma rstep_imp_mstep:
  assumes "(s, t) \<in> rstep R"
  shows "(s, t) \<in> mstep R"
  using assms
proof (induct)
  case (IH C \<sigma> l r)
  have "\<forall>x\<in>vars_term l. (\<sigma> x, \<sigma> x) \<in> mstep R" by simp
  from mstep.rule [OF \<open>(l, r) \<in> R\<close> this]
  have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> mstep R" by simp
  from mstep_ctxt [OF this] show ?case by blast
qed

lemma rstep_mstep_subset:
  "rstep R \<subseteq> mstep R"
  by (auto simp: rstep_imp_mstep)

lemma subst_rsteps_imp_rule_rsteps:
  assumes "\<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> (rstep R)\<^sup>*"
    and "(l, r) \<in> R"
  shows "(l \<cdot> \<sigma>, r \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
proof -
  let ?\<sigma>="\<lambda>x. (if x \<in> vars_term l then \<sigma> x else \<tau> x)"
  have "l \<cdot> \<sigma> = l \<cdot> ?\<sigma>" 
    by (simp add: term_subst_eq_conv)
  with \<open>(l, r) \<in> R\<close> have "(l \<cdot> \<sigma>, r \<cdot> ?\<sigma>) \<in> rstep R"
    by auto
  moreover have "(r \<cdot> ?\<sigma>, r \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
    by (rule subst_rsteps_imp_rsteps) (insert assms, auto)
  ultimately show ?thesis by auto
qed

lemma mstep_imp_rsteps:
  assumes "(s, t) \<in> mstep R"
  shows "(s, t) \<in> (rstep R)\<^sup>*"
  using assms
proof (induct)
  case (args f n ss ts)
  then show ?case by (metis args_rsteps_imp_rsteps)
next
  case (rule l r \<sigma> \<tau>)
  then show ?case using \<open>(l, r) \<in> R\<close> by (metis subst_rsteps_imp_rule_rsteps)
qed simp

lemma mstep_rsteps_subset:
  shows "mstep R \<subseteq> (rstep R)\<^sup>*"
  by (auto simp: mstep_imp_rsteps)

lemma mstep_mono: "R \<subseteq> S \<Longrightarrow> mstep R \<subseteq> mstep S" 
proof -
  have "(s,t) \<in> mstep R \<Longrightarrow> R \<subseteq> S \<Longrightarrow> (s,t) \<in> mstep S" for s t
    by (induct rule: mstep.induct, auto intro: mstep.intros)
  thus "R \<subseteq> S \<Longrightarrow> mstep R \<subseteq> mstep S" by auto
qed


text \<open>Thus if @{term " mstep R"} has the diamond property,
then @{term "rstep R"} is confluent.\<close>

lemma Var_mstep:
  assumes *: "\<And>l r. (l, r) \<in> R \<Longrightarrow> \<not> is_Var l"
    and "(Var x, t) \<in> mstep R"
  shows "t = Var x"
  using assms(2-) 
proof cases
  case (rule l r \<sigma> \<tau>)
  then show ?thesis using * by (cases l, auto)
qed auto


subsection \<open>Maximal multi-step rewriting.\<close>
inductive_set
  mmstep :: "('f, 'v) trs \<Rightarrow> ('f, 'v) term rel"
  for R
  where
    Var: "(Var x, Var x) \<in> mmstep R" |
    args: "\<And>f n ss ts. \<lbrakk>length ss = n; length ts = n;
    \<not> (\<exists>(l, r)\<in>R. \<exists>\<sigma>. Fun f ss = l \<cdot> \<sigma>);
    \<forall>i<n. (ss ! i, ts ! i) \<in> mmstep R\<rbrakk> \<Longrightarrow>
    (Fun f ss, Fun f ts) \<in> mmstep R" |
    rule: "\<And>l r \<sigma> \<tau>. \<lbrakk>(l, r) \<in> R; \<forall>x\<in>vars_term l. (\<sigma> x, \<tau> x) \<in> mmstep R\<rbrakk> \<Longrightarrow>
    (l \<cdot> \<sigma>, r \<cdot> \<tau>) \<in> mmstep R"

lemma mmstep_imp_mstep:
  assumes "(s, t) \<in> mmstep R"
  shows "(s, t) \<in> mstep R"
  using assms by (induct) (auto intro: mstep.intros)

lemma mmstep_mstep_subset:
  "mmstep R \<subseteq> mstep R"
  by (auto simp: mmstep_imp_mstep)


end