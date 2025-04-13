section \<open>Term Rewrite Systems\<close>

theory Trs
  imports
    Relation_Closure
    First_Order_Terms.Term_More
    "Abstract-Rewriting.Relative_Rewriting"
begin

text \<open>
  A rewrite rule is a pair of terms. A term rewrite system (TRS) is a set of rewrite rules.
\<close>
type_synonym ('f, 'v) rule = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) trs  = "('f, 'v) rule set"

inductive_set rstep :: "_ \<Rightarrow> ('f, 'v) term rel" for R :: "('f, 'v) trs"
  where
    rstep: "\<And>C \<sigma> l r. (l, r) \<in> R \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> (s, t) \<in> rstep R"

lemma rstep_induct_rule [case_names IH, induct set: rstep]:
  assumes "(s, t) \<in> rstep R"
    and "\<And>C \<sigma> l r. (l, r) \<in> R \<Longrightarrow> P (C\<langle>l \<cdot> \<sigma>\<rangle>) (C\<langle>r \<cdot> \<sigma>\<rangle>)"
  shows "P s t"
  using assms by (induct) simp

text \<open>
  An alternative induction scheme that treats the rule-case, the
  substition-case, and the context-case separately.
\<close>
lemma rstep_induct [consumes 1, case_names rule subst ctxt]:
  assumes "(s, t) \<in> rstep R"
    and rule: "\<And>l r. (l, r) \<in> R \<Longrightarrow> P l r"
    and subst: "\<And>s t \<sigma>. P s t \<Longrightarrow> P (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
    and ctxt: "\<And>s t C. P s t \<Longrightarrow> P (C\<langle>s\<rangle>) (C\<langle>t\<rangle>)"
  shows "P s t"
  using assms by (induct) auto

lemmas rstepI = rstep.intros [intro]

lemmas rstepE = rstep.cases [elim]

lemma rstep_ctxt [intro]: "(s, t) \<in> rstep R \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> rstep R"
  by (force simp flip: ctxt_ctxt_compose)

lemma rstep_rule [intro]: "(l, r) \<in> R \<Longrightarrow> (l, r) \<in> rstep R"
  using rstep.rstep [where C = \<box> and \<sigma> = Var and R = R] by simp

lemma rstep_subst [intro]: "(s, t) \<in> rstep R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep R"
  by (force simp flip: subst_subst_compose)

lemma rstep_empty [simp]: "rstep {} = {}"
  by auto

lemma rstep_mono: "R \<subseteq> S \<Longrightarrow> rstep R \<subseteq> rstep S"
  by force

lemma rstep_union: "rstep (R \<union> S) = rstep R \<union> rstep S"
  by auto

lemma rstep_converse [simp]: "rstep (R\<inverse>) = (rstep R)\<inverse>"
  by auto

interpretation subst: rel_closure "\<lambda>\<sigma> t. t \<cdot> \<sigma>" Var "\<lambda>x y. y \<circ>\<^sub>s x" by (standard) auto
declare subst.closure.induct [consumes 1, case_names subst, induct pred: subst.closure]
declare subst.closure.cases [consumes 1, case_names subst, cases pred: subst.closure]

interpretation ctxt: rel_closure "ctxt_apply_term" \<box> "(\<circ>\<^sub>c)" by (standard) auto
declare ctxt.closure.induct [consumes 1, case_names ctxt, induct pred: ctxt.closure]
declare ctxt.closure.cases [consumes 1, case_names ctxt, cases pred: ctxt.closure]

lemma rstep_eq_closure: "rstep R = ctxt.closure (subst.closure R)"
  by (force elim: ctxt.closure.cases subst.closure.cases)

lemma ctxt_closed_rstep [intro]: "ctxt.closed (rstep R)"
  by (simp add: rstep_eq_closure ctxt.closed_closure)

lemma ctxt_closed_one:
  "ctxt.closed r \<Longrightarrow> (s, t) \<in> r \<Longrightarrow> (Fun f (ss @ s # ts), Fun f (ss @ t # ts)) \<in> r"
  using ctxt.closedD [of r s t "More f ss \<box> ts"] by auto

subsection\<open>Well-formed TRSs\<close>

definition
  wf_trs :: "('f, 'v) trs \<Rightarrow> bool"
  where
    "wf_trs R = (\<forall>l r. (l,r) \<in> R \<longrightarrow> (\<exists>f ts. l = Fun f ts) \<and> vars_term r \<subseteq> vars_term l)"

lemma wf_trs_imp_lhs_Fun:
  "wf_trs R \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> \<exists>f ts. l = Fun f ts"
  unfolding wf_trs_def by blast

lemma rstep_imp_Fun:
  assumes "wf_trs R"
  shows "(s, t) \<in> rstep R \<Longrightarrow> \<exists>f ss. s = Fun f ss"
proof -
  assume "(s, t) \<in> rstep R"
  then obtain C l r \<sigma> where lr: "(l,r) \<in> R" and s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>" by auto
  with wf_trs_imp_lhs_Fun[OF assms lr] show ?thesis by (cases C, auto)
qed

lemma SN_Var:
  assumes "wf_trs R" shows "SN_on (rstep R) {Var x}"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain S where [symmetric]: "S 0 = Var x"
    and chain: "chain (rstep R) S" by auto
  then have "(Var x, S (Suc 0)) \<in> rstep R" by force
  then obtain C l r \<sigma> where "(l, r) \<in> R" and "Var x = C\<langle>l \<cdot> \<sigma>\<rangle>" by best
  then have "Var x = l \<cdot> \<sigma>" by (induct C) simp_all
  then obtain y where "l = Var y" by (induct l) simp_all
  with assms and \<open>(l, r) \<in> R\<close> show False unfolding wf_trs_def by blast
qed

subsection \<open>Function Symbols and Variables of Rules and TRSs\<close>

definition
  vars_rule :: "('f, 'v) rule \<Rightarrow> 'v set"
  where
    "vars_rule r = vars_term (fst r) \<union> vars_term (snd r)"

lemma finite_vars_rule:
  "finite (vars_rule r)"
  by (auto simp: vars_rule_def)

definition vars_trs :: "('f, 'v) trs \<Rightarrow> 'v set" where
  "vars_trs R = (\<Union>r\<in>R. vars_rule r)"

lemma vars_trs_union: "vars_trs (R \<union> S) = vars_trs R \<union> vars_trs S"
  unfolding vars_trs_def by auto

lemma finite_trs_has_finite_vars:
  assumes "finite R" shows "finite (vars_trs R)"
  using assms unfolding vars_trs_def vars_rule_def [abs_def] by simp

lemmas vars_defs = vars_trs_def vars_rule_def

definition funs_rule :: "('f, 'v) rule \<Rightarrow> 'f set" where
  "funs_rule r = funs_term (fst r) \<union> funs_term (snd r)"


text \<open>The same including arities.\<close>
definition funas_rule :: "('f, 'v) rule \<Rightarrow> 'f sig" where
  "funas_rule r = funas_term (fst r) \<union> funas_term (snd r)"

definition funs_trs :: "('f, 'v) trs \<Rightarrow> 'f set" where
  "funs_trs R = (\<Union>r\<in>R. funs_rule r)"

definition funas_trs :: "('f, 'v) trs \<Rightarrow> 'f sig" where
  "funas_trs R = (\<Union>r\<in>R. funas_rule r)"

lemma funs_rule_funas_rule: "funs_rule rl = fst ` funas_rule rl"
  using funs_term_funas_term unfolding funs_rule_def funas_rule_def image_Un by metis

lemma funs_trs_funas_trs:"funs_trs R = fst ` funas_trs R"
  unfolding funs_trs_def funas_trs_def image_UN using funs_rule_funas_rule by metis

lemma finite_funas_rule: "finite (funas_rule lr)"
  unfolding funas_rule_def
  using finite_funas_term by auto

lemma finite_funas_trs:
  assumes "finite R"
  shows "finite (funas_trs R)"
  unfolding funas_trs_def
  using assms finite_funas_rule by auto

lemma funas_empty[simp]: "funas_trs {} = {}" unfolding funas_trs_def by simp

lemma funas_trs_union[simp]: "funas_trs (R \<union> S) = funas_trs R \<union> funas_trs S"
  unfolding funas_trs_def by blast

definition funas_args_rule :: "('f, 'v) rule \<Rightarrow> 'f sig" where
  "funas_args_rule r = funas_args_term (fst r) \<union> funas_args_term (snd r)"

definition funas_args_trs :: "('f, 'v) trs \<Rightarrow> 'f sig" where
  "funas_args_trs R = (\<Union>r\<in>R. funas_args_rule r)"

lemmas funas_args_defs =
  funas_args_trs_def funas_args_rule_def funas_args_term_def

definition roots_rule :: "('f, 'v) rule \<Rightarrow> 'f sig"
  where
    "roots_rule r = set_option (root (fst r)) \<union> set_option (root (snd r))"

definition roots_trs :: "('f, 'v) trs \<Rightarrow> 'f sig" where
  "roots_trs R = (\<Union>r\<in>R. roots_rule r)"

lemmas roots_defs =
  roots_trs_def roots_rule_def

definition funas_head :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f sig" where
  "funas_head P R = funas_trs P - (funas_trs R \<union> funas_args_trs P)"

lemmas funs_defs = funs_trs_def funs_rule_def
lemmas funas_defs =
  funas_trs_def funas_rule_def
  funas_args_defs
  funas_head_def
  roots_defs

text \<open>A function symbol is said to be \emph{defined} (w.r.t.\ to a given
TRS) if it occurs as root of some left-hand side.\<close>
definition
  defined :: "('f, 'v) trs \<Rightarrow> ('f \<times> nat) \<Rightarrow> bool"
  where
    "defined R fn \<longleftrightarrow> (\<exists>l r. (l, r) \<in> R \<and> root l = Some fn)"

lemma defined_funas_trs: assumes d: "defined R fn" shows "fn \<in> funas_trs R"
proof -
  from d [unfolded defined_def] obtain l r
    where "(l, r) \<in> R" and "root l = Some fn" by auto
  then show ?thesis
    unfolding funas_trs_def funas_rule_def [abs_def] by (cases l) force+
qed

fun root_list :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) list"
  where
    "root_list (Var x) = []" |
    "root_list (Fun f ts) = [(f, length ts)]"

definition vars_rule_list :: "('f, 'v) rule \<Rightarrow> 'v list"
  where
    "vars_rule_list r = vars_term_list (fst r) @ vars_term_list (snd r)"

definition funs_rule_list :: "('f, 'v) rule \<Rightarrow> 'f list"
  where
    "funs_rule_list r = funs_term_list (fst r) @ funs_term_list (snd r)"

definition funas_rule_list :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list"
  where
    "funas_rule_list r = funas_term_list (fst r) @ funas_term_list (snd r)"

definition roots_rule_list :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list"
  where
    "roots_rule_list r = root_list (fst r) @ root_list (snd r)"

definition funas_args_rule_list :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list"
  where
    "funas_args_rule_list r = funas_args_term_list (fst r) @ funas_args_term_list (snd r)"

lemma set_vars_rule_list [simp]:
  "set (vars_rule_list r) = vars_rule r"
  by (simp add: vars_rule_list_def vars_rule_def)

lemma set_funs_rule_list [simp]:
  "set (funs_rule_list r) = funs_rule r"
  by (simp add: funs_rule_list_def funs_rule_def)

lemma set_funas_rule_list [simp]:
  "set (funas_rule_list r) = funas_rule r"
  by (simp add: funas_rule_list_def funas_rule_def)

lemma set_roots_rule_list [simp]:
  "set (roots_rule_list r) = roots_rule r"
  by (cases "fst r" "snd r" rule: term.exhaust [case_product term.exhaust])
    (auto simp: roots_rule_list_def roots_rule_def ac_simps)

lemma set_funas_args_rule_list [simp]:
  "set (funas_args_rule_list r) = funas_args_rule r"
  by (simp add: funas_args_rule_list_def funas_args_rule_def)

definition vars_trs_list :: "('f, 'v) rule list \<Rightarrow> 'v list"
  where
    "vars_trs_list trs = concat (map vars_rule_list trs)"

definition funs_trs_list :: "('f, 'v) rule list \<Rightarrow> 'f list"
  where
    "funs_trs_list trs = concat (map funs_rule_list trs)"

definition funas_trs_list :: "('f, 'v) rule list \<Rightarrow> ('f \<times> nat) list"
  where
    "funas_trs_list trs = concat (map funas_rule_list trs)"

definition roots_trs_list :: "('f, 'v) rule list \<Rightarrow> ('f \<times> nat) list"
  where
    "roots_trs_list trs = remdups (concat (map roots_rule_list trs))"

definition funas_args_trs_list :: "('f, 'v) rule list \<Rightarrow> ('f \<times> nat) list"
  where
    "funas_args_trs_list trs = concat (map funas_args_rule_list trs)"

lemma set_vars_trs_list [simp]:
  "set (vars_trs_list trs) = vars_trs (set trs)"
  by (simp add: vars_trs_def vars_trs_list_def)

lemma set_funs_trs_list [simp]:
  "set (funs_trs_list R) = funs_trs (set R)"
  by (simp add: funs_trs_def funs_trs_list_def)

lemma set_funas_trs_list [simp]:
  "set (funas_trs_list R) = funas_trs (set R)"
  by (simp add: funas_trs_def funas_trs_list_def)

lemma set_roots_trs_list [simp]:
  "set (roots_trs_list R) = roots_trs (set R)"
  by (simp add: roots_trs_def roots_trs_list_def)

lemma set_funas_args_trs_list [simp]:
  "set (funas_args_trs_list R) = funas_args_trs (set R)"
  by (simp add: funas_args_trs_def funas_args_trs_list_def)

lemmas vars_list_defs = vars_trs_list_def vars_rule_list_def
lemmas funs_list_defs = funs_trs_list_def funs_rule_list_def
lemmas funas_list_defs = funas_trs_list_def funas_rule_list_def
lemmas roots_list_defs = roots_trs_list_def roots_rule_list_def
lemmas funas_args_list_defs = funas_args_trs_list_def funas_args_rule_list_def

lemma vars_trs_list_Nil [simp]:
  "vars_trs_list [] = []" unfolding vars_trs_list_def by simp

context
  fixes R :: "('f, 'v) trs"
  assumes "wf_trs R"
begin

lemma funas_term_subst_rhs:
  assumes "funas_trs R \<subseteq> F" and "(l, r) \<in> R" and "funas_term (l \<cdot> \<sigma>) \<subseteq> F"
  shows "funas_term (r \<cdot> \<sigma>) \<subseteq> F"
proof -
  have "vars_term r \<subseteq> vars_term l"  using \<open>wf_trs R\<close> and \<open>(l, r) \<in> R\<close> by (auto simp: wf_trs_def)
  moreover have "funas_term l \<subseteq> F" and "funas_term r \<subseteq> F"
    using \<open>funas_trs R \<subseteq> F\<close> and \<open>(l, r) \<in> R\<close> by (auto simp: funas_defs) force+
  ultimately show ?thesis
    using \<open>funas_term (l \<cdot> \<sigma>) \<subseteq> F\<close> by (force simp: funas_term_subst)
qed

lemma vars_rule_lhs:
  "r \<in> R \<Longrightarrow> vars_rule r = vars_term (fst r)"
  using \<open>wf_trs R\<close> by (cases r) (auto simp: wf_trs_def vars_rule_def)

end

subsection\<open>Closure Properties\<close>

lemma ctxt_closed_R_imp_supt_R_distr:
  assumes "ctxt.closed R" and "s \<rhd> t" and "(t, u) \<in> R" shows "\<exists>t. (s, t) \<in> R \<and> t \<rhd> u"
proof -
  from \<open>s \<rhd> t\<close> obtain C where "C \<noteq> \<box>" and "C\<langle>t\<rangle> = s" by auto
  from \<open>ctxt.closed R\<close> and \<open>(t,u) \<in> R\<close>
  have RCtCu: "(C\<langle>t\<rangle>,C\<langle>u\<rangle>) \<in> R" by (rule ctxt.closedD)
  from \<open>C \<noteq> \<box>\<close> have "C\<langle>u\<rangle> \<rhd> u" by auto
  from RCtCu have "(s,C\<langle>u\<rangle>) \<in> R" unfolding \<open>C\<langle>t\<rangle> = s\<close> .
  from this and \<open>C\<langle>u\<rangle> \<rhd> u\<close> show ?thesis by auto
qed

lemma ctxt_closed_imp_qc_supt: "ctxt.closed R \<Longrightarrow> {\<rhd>} O R \<subseteq> R O (R \<union> {\<rhd>})\<^sup>*" by blast

text \<open>Let~$R$ be a relation on terms that is closed under contexts. If~$R$
is well-founded then $R \cup \rhd$ is well-founed.\<close>
lemma SN_imp_SN_union_supt:
  assumes "SN R" and "ctxt.closed R"
  shows "SN (R \<union> {\<rhd>})"
proof -
  from \<open>ctxt.closed R\<close> have "quasi_commute R {\<rhd>}"
    unfolding quasi_commute_def by (rule ctxt_closed_imp_qc_supt)
  have "SN {\<rhd>}" by (rule SN_supt)
  from \<open>SN R\<close> and \<open>SN {\<rhd>}\<close> and \<open>quasi_commute R {\<rhd>}\<close>
  show ?thesis by (rule quasi_commute_imp_SN)
qed

lemma stable_loop_imp_not_SN:
  assumes stable: "subst.closed r" and steps: "(s, s \<cdot> \<sigma>) \<in> r\<^sup>+"
  shows "\<not> SN_on r {s}"
proof -
  let ?f =  "\<lambda> i. s \<cdot> (power.power Var (\<circ>\<^sub>s) \<sigma> i)"
  have main: "\<And> i. (?f i, ?f (Suc i)) \<in> r\<^sup>+"
  proof -
    fix i
    show "(?f i, ?f (Suc i)) \<in> r\<^sup>+"
    proof (induct i)
      case (Suc i)
      from Suc subst.closed_trancl[OF stable] have step: "(?f i \<cdot> \<sigma>, ?f (Suc i) \<cdot> \<sigma>) \<in> r\<^sup>+" by auto
      let ?\<sigma>g = "power.power Var (\<circ>\<^sub>s) \<sigma> i"
      let ?\<sigma>gs = "power.power Var (\<circ>\<^sub>s) \<sigma> (Suc i)"
      have idi: "?\<sigma>g \<circ>\<^sub>s \<sigma> = \<sigma> \<circ>\<^sub>s ?\<sigma>g" by (rule subst_monoid_mult.power_commutes)
      have idsi: "?\<sigma>gs \<circ>\<^sub>s \<sigma> = \<sigma> \<circ>\<^sub>s ?\<sigma>gs" by (rule subst_monoid_mult.power_commutes)
      have "?f i \<cdot> \<sigma> = s \<cdot> ?\<sigma>g  \<circ>\<^sub>s \<sigma>" by simp
      also have "\<dots> = ?f (Suc i)" unfolding idi by simp
      finally have one: "?f i \<cdot> \<sigma> = ?f (Suc i)" .
      have "?f (Suc i) \<cdot> \<sigma> = s \<cdot> ?\<sigma>gs \<circ>\<^sub>s \<sigma>" by simp
      also have "\<dots> = ?f (Suc (Suc i))" unfolding idsi by simp
      finally have two: "?f (Suc i) \<cdot> \<sigma> = ?f (Suc (Suc i))" by simp
      show ?case using one two step by simp
    qed (auto simp: steps)
  qed
  then have "\<not> SN_on (r\<^sup>+) {?f 0}" unfolding SN_on_def by best
  then show ?thesis using SN_on_trancl by force
qed

lemma subst_closed_supteq: "subst.closed {\<unrhd>}" by blast

lemma subst_closed_supt: "subst.closed {\<rhd>}" by blast

lemma ctxt_closed_supt_subset: "ctxt.closed R \<Longrightarrow> {\<rhd>} O R \<subseteq> R O {\<rhd>}" by blast

subsection\<open>Properties of Rewrite Steps\<close>

lemma rstep_relcomp_idemp1 [simp]:
  "rstep (rstep R O rstep S) = rstep R O rstep S"
proof -
  { fix s t
    assume "(s, t) \<in> rstep (rstep R O rstep S)"
    then have "(s, t) \<in> rstep R O rstep S"
      by (induct) blast+ }
  then show ?thesis by auto
qed

lemma rstep_relcomp_idemp2 [simp]:
  "rstep (rstep R O rstep S O rstep T) = rstep R O rstep S O rstep T"
proof -
  { fix s t
    assume "(s, t) \<in> rstep (rstep R O rstep S O rstep T)"
    then have "(s, t) \<in> rstep R O rstep S O rstep T"
      by (induct) blast+ }
  then show ?thesis by auto
qed

lemma ctxt_closed_rsteps [intro]: "ctxt.closed ((rstep R)\<^sup>*)" by blast

lemma subset_rstep: "R \<subseteq> rstep R" by auto

lemma subst_closure_rstep_subset: "subst.closure (rstep R) \<subseteq> rstep R"
  by (auto elim: subst.closure.cases)

lemma subst_closed_rstep [intro]: "subst.closed (rstep R)" by blast

lemma subst_closed_rsteps: "subst.closed ((rstep R)\<^sup>*)" by blast

lemmas supt_rsteps_subset = ctxt_closed_supt_subset [OF ctxt_closed_rsteps]

lemma supteq_rsteps_subset:
  "{\<unrhd>} O (rstep R)\<^sup>* \<subseteq> (rstep R)\<^sup>* O {\<unrhd>}" (is "?S \<subseteq> ?T")
  using supt_rsteps_subset [of R] by (auto simp: supt_supteq_set_conv)

lemma quasi_commute_rsteps_supt:
  "quasi_commute ((rstep R)\<^sup>*) {\<rhd>}"
  unfolding quasi_commute_def using supt_rsteps_subset [of R] by auto

lemma rstep_UN:
  "rstep (\<Union>i\<in>A. R i) = (\<Union>i\<in>A. rstep (R i))"
  by (force)

definition
  rstep_r_p_s :: "('f, 'v) trs \<Rightarrow> ('f, 'v) rule \<Rightarrow> pos \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) trs"
  where
    "rstep_r_p_s R r p \<sigma> = {(s, t).
    let C = ctxt_of_pos_term p s in p \<in> poss s \<and> r \<in> R \<and> (C\<langle>fst r \<cdot> \<sigma>\<rangle> = s) \<and> (C\<langle>snd r \<cdot> \<sigma>\<rangle> = t)}"

lemma rstep_r_p_s_def':
  "rstep_r_p_s R r p \<sigma> = {(s, t).
    p \<in> poss s \<and> r \<in> R \<and> s |_ p = fst r \<cdot> \<sigma> \<and> t = replace_at s p (snd r \<cdot> \<sigma>)}" (is "?l = ?r")
proof -
  { fix s t
    have "((s,t) \<in> ?l) = ((s,t) \<in> ?r)"
      unfolding rstep_r_p_s_def Let_def
      using ctxt_supt_id [of p s] and subt_at_ctxt_of_pos_term [of p s "fst r \<cdot> \<sigma>"] by auto }
  then show ?thesis by auto
qed

lemma parallel_steps:
  fixes p\<^sub>1 :: pos
  assumes "(s, t) \<in> rstep_r_p_s R\<^sub>1 (l\<^sub>1, r\<^sub>1) p\<^sub>1 \<sigma>\<^sub>1"
    and "(s, u) \<in> rstep_r_p_s R\<^sub>2 (l\<^sub>2, r\<^sub>2) p\<^sub>2 \<sigma>\<^sub>2"
    and par: "p\<^sub>1 \<bottom> p\<^sub>2"
  shows "(t, (ctxt_of_pos_term p\<^sub>1 u)\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>) \<in> rstep_r_p_s R\<^sub>2 (l\<^sub>2, r\<^sub>2) p\<^sub>2 \<sigma>\<^sub>2 \<and>
         (u, (ctxt_of_pos_term p\<^sub>1 u)\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>) \<in> rstep_r_p_s R\<^sub>1 (l\<^sub>1, r\<^sub>1) p\<^sub>1 \<sigma>\<^sub>1"
proof -
  have p1: "p\<^sub>1 \<in> poss s" and lr1: "(l\<^sub>1, r\<^sub>1) \<in> R\<^sub>1" and \<sigma>1: "s |_ p\<^sub>1 = l\<^sub>1 \<cdot> \<sigma>\<^sub>1"
    and t: "t = replace_at s p\<^sub>1 (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
    and p2: "p\<^sub>2 \<in> poss s" and lr2: "(l\<^sub>2, r\<^sub>2) \<in> R\<^sub>2" and \<sigma>2: "s |_ p\<^sub>2 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2"
    and u: "u = replace_at s p\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2)" using assms by (auto simp: rstep_r_p_s_def')

  have "replace_at t p\<^sub>2 (r\<^sub>2 \<cdot> \<sigma>\<^sub>2) = replace_at u p\<^sub>1 (r\<^sub>1 \<cdot> \<sigma>\<^sub>1)"
    using t and u and parallel_replace_at [OF \<open>p\<^sub>1 \<bottom> p\<^sub>2\<close> p1 p2] by auto
  moreover
  have "(t, (ctxt_of_pos_term p\<^sub>2 t)\<langle>r\<^sub>2 \<cdot> \<sigma>\<^sub>2\<rangle>) \<in> rstep_r_p_s R\<^sub>2 (l\<^sub>2, r\<^sub>2) p\<^sub>2 \<sigma>\<^sub>2"
  proof -
    have "t |_ p\<^sub>2 = l\<^sub>2 \<cdot> \<sigma>\<^sub>2" using \<sigma>2 and parallel_replace_at_subt_at [OF par p1 p2] and t by auto
    moreover have "p\<^sub>2 \<in> poss t" using parallel_poss_replace_at [OF par p1] and t and p2 by auto
    ultimately show ?thesis using lr2 and ctxt_supt_id [of p\<^sub>2 t] by (simp add: rstep_r_p_s_def)
  qed
  moreover
  have "(u, (ctxt_of_pos_term p\<^sub>1 u)\<langle>r\<^sub>1 \<cdot> \<sigma>\<^sub>1\<rangle>) \<in> rstep_r_p_s R\<^sub>1 (l\<^sub>1, r\<^sub>1) p\<^sub>1 \<sigma>\<^sub>1"
  proof -
    have par': "p\<^sub>2 \<bottom> p\<^sub>1" using parallel_pos_sym [OF par] .
    have "u |_ p\<^sub>1 = l\<^sub>1 \<cdot> \<sigma>\<^sub>1" using \<sigma>1 and parallel_replace_at_subt_at [OF par' p2 p1] and u by auto
    moreover have "p\<^sub>1 \<in> poss u" using parallel_poss_replace_at [OF par' p2] and u and p1 by auto
    ultimately show ?thesis using lr1 and ctxt_supt_id [of p\<^sub>1 u] by (simp add: rstep_r_p_s_def)
  qed
  ultimately show ?thesis by auto
qed

lemma rstep_iff_rstep_r_p_s:
  "(s, t) \<in> rstep R \<longleftrightarrow> (\<exists>l r p \<sigma>. (s, t) \<in> rstep_r_p_s R (l, r) p \<sigma>)" (is "?lhs = ?rhs")
proof
  assume "(s, t) \<in> rstep R"
  then obtain C \<sigma> l r where s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and "(l, r) \<in> R" by auto
  let ?p = "hole_pos C"
  let ?C = "ctxt_of_pos_term ?p s"
  have C: "ctxt_of_pos_term ?p s = C" unfolding s by (induct C) simp_all
  have "?p \<in> poss s" unfolding s by simp
  moreover have "(l, r) \<in> R" by fact
  moreover have "?C\<langle>l \<cdot> \<sigma>\<rangle> = s" unfolding C by (simp add: s)
  moreover have "?C\<langle>r \<cdot> \<sigma>\<rangle> = t" unfolding C by (simp add: t)
  ultimately show "?rhs" unfolding rstep_r_p_s_def Let_def by auto
next
  assume "?rhs"
  then obtain l r p \<sigma> where "p \<in> poss s"
    and "(l, r) \<in> R"
    and s[symmetric]: "(ctxt_of_pos_term p s)\<langle>l \<cdot> \<sigma>\<rangle> = s"
    and t[symmetric]: "(ctxt_of_pos_term p s)\<langle>r \<cdot> \<sigma>\<rangle> = t"
    unfolding rstep_r_p_s_def Let_def by auto
  then show "?lhs" by auto
qed

lemma rstep_r_p_s_imp_rstep:
  assumes "(s, t) \<in> rstep_r_p_s R r p \<sigma>"
  shows "(s, t) \<in> rstep R"
  using assms by (cases r) (auto simp: rstep_iff_rstep_r_p_s)

text \<open>Rewriting steps below the root position.\<close>
definition
  nrrstep :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
  where
    "nrrstep R = {(s,t). \<exists>r i ps \<sigma>. (s,t) \<in> rstep_r_p_s R r (i#ps) \<sigma>}"

text \<open>An alternative characterisation of non-root rewrite steps.\<close>
lemma nrrstep_def':
  "nrrstep R = {(s, t). \<exists>l r C \<sigma>. (l, r) \<in> R \<and> C \<noteq> \<box> \<and> s = C\<langle>l\<cdot>\<sigma>\<rangle> \<and> t = C\<langle>r\<cdot>\<sigma>\<rangle>}"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof (rule subrelI)
    fix s t assume "(s, t) \<in> nrrstep R"
    then obtain l r i ps \<sigma> where step: "(s, t) \<in> rstep_r_p_s R (l, r) (i # ps) \<sigma>"
      unfolding nrrstep_def by best
    let ?C = "ctxt_of_pos_term (i # ps) s"
    from step have"i # ps \<in> poss s" and "(l, r) \<in> R" and "s = ?C\<langle>l\<cdot>\<sigma>\<rangle>" and "t = ?C\<langle>r\<cdot>\<sigma>\<rangle>"
      unfolding rstep_r_p_s_def Let_def by auto
    moreover from \<open>i # ps \<in> poss s\<close> have "?C \<noteq> \<box>" by (induct s) auto
    ultimately show "(s, t) \<in> ?rhs" by auto
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof (rule subrelI)
    fix s t assume "(s, t) \<in> ?rhs"
    then obtain l r C \<sigma> where in_R: "(l, r) \<in> R" and "C \<noteq> \<box>"
      and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
    from \<open>C \<noteq> \<box>\<close> obtain i p where ip: "hole_pos C = i # p" by (induct C) auto
    have "i # p \<in> poss s" using hole_pos_poss[of C] unfolding s ip by simp
    then have C: "C = ctxt_of_pos_term (i # p) s"
      unfolding s ip[symmetric] by simp
    from \<open>i # p \<in> poss s\<close> in_R s t have "(s, t) \<in> rstep_r_p_s R (l, r) (i # p) \<sigma>"
      unfolding rstep_r_p_s_def C by simp
    then show "(s, t) \<in> nrrstep R" unfolding nrrstep_def by best
  qed
qed

lemma nrrstepI: "(l,r) \<in> R \<Longrightarrow> s = C\<langle>l\<cdot>\<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> C \<noteq> \<box> \<Longrightarrow> (s,t) \<in> nrrstep R" unfolding nrrstep_def' by auto

lemma nrrstep_union: "nrrstep (R \<union> S) = nrrstep R \<union> nrrstep S"
  unfolding nrrstep_def' by blast

lemma nrrstep_empty[simp]: "nrrstep {} = {}" unfolding nrrstep_def' by blast

text \<open>Rewriting step at the root position.\<close>
definition
  rrstep :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
  where
    "rrstep R = {(s,t). \<exists>r \<sigma>. (s,t) \<in> rstep_r_p_s R r [] \<sigma>}"

text \<open>An alternative characterisation of root rewrite steps.\<close>
lemma rrstep_def': "rrstep R = {(s, t). \<exists>l r \<sigma>. (l, r) \<in> R \<and> s = l\<cdot>\<sigma> \<and> t = r\<cdot>\<sigma>}"
  (is "_ = ?rhs")
  by (auto simp: rrstep_def rstep_r_p_s_def)

lemma rules_subset_rrstep [simp]: "R \<subseteq> rrstep R"
  by (force simp: rrstep_def' intro: exI [of _ Var])

lemma rrstep_union: "rrstep (R \<union> S) = rrstep R \<union> rrstep S" unfolding rrstep_def' by blast

lemma rrstep_empty[simp]: "rrstep {} = {}"
  unfolding rrstep_def' by auto

lemma subst_closed_rrstep: "subst.closed (rrstep R)"
  unfolding subst.closed_def
proof
  fix ss ts
  assume "(ss,ts) \<in> subst.closure (rrstep R)"
  then show "(ss,ts) \<in> rrstep R"
  proof
    fix s t \<sigma>
    assume ss: "ss = s \<cdot> \<sigma>" and ts: "ts = t \<cdot> \<sigma>" and step: "(s,t) \<in> rrstep R"
    from step obtain l r \<delta> where lr: "(l,r) \<in> R" and s: "s = l \<cdot> \<delta>" and t: "t = r \<cdot> \<delta>" unfolding rrstep_def' by auto
    obtain sig where "sig = \<delta> \<circ>\<^sub>s \<sigma>" by auto
    with ss s ts t have "ss = l \<cdot> sig" and "ts = r \<cdot> sig" by simp+
    with lr show "(ss,ts) \<in> rrstep R" unfolding rrstep_def' by (auto simp: Let_def)
  qed
qed

lemma rstep_iff_rrstep_or_nrrstep: "rstep R = (rrstep R \<union> nrrstep R)"
proof
  show "rstep R \<subseteq> rrstep R \<union> nrrstep R"
  proof (rule subrelI)
    fix s t assume "(s,t) \<in> rstep R"
    then obtain l r p \<sigma> where rstep_rps: "(s,t) \<in> rstep_r_p_s R (l,r) p \<sigma>"
      by (auto simp: rstep_iff_rstep_r_p_s)
    then show "(s,t) \<in> rrstep R \<union> nrrstep R" unfolding rrstep_def nrrstep_def by (cases p) auto
  qed
next
  show "rrstep R \<union> nrrstep R \<subseteq> rstep R"
  proof (rule subrelI)
    fix s t assume "(s,t) \<in> rrstep R \<union> nrrstep R"
    then show "(s,t) \<in> rstep R" by (auto simp: rrstep_def nrrstep_def rstep_iff_rstep_r_p_s)
  qed
qed

lemma rstep_i_pos_imp_rstep_arg_i_pos:
  assumes nrrstep: "(Fun f ss,t) \<in> rstep_r_p_s R (l,r) (i#ps) \<sigma>"
  shows "(ss!i,t|_[i]) \<in> rstep_r_p_s R (l,r) ps \<sigma>"
proof -
  from nrrstep obtain C where C:"C = ctxt_of_pos_term (i#ps) (Fun f ss)"
    and pos: "(i#ps) \<in> poss (Fun f ss)"
    and Rlr: "(l,r) \<in> R"
    and Fun: "C\<langle>l\<cdot>\<sigma>\<rangle> = Fun f ss"
    and t: "C\<langle>r\<cdot>\<sigma>\<rangle> = t" unfolding rstep_r_p_s_def Let_def by auto
  then obtain D where C':"C = More f (take i ss) D (drop (Suc i) ss)" by auto
  then have CFun: "C\<langle>l\<cdot>\<sigma>\<rangle> = Fun f (take i ss @ (D\<langle>l\<cdot>\<sigma>\<rangle>) # drop (Suc i) ss)" by auto
  from pos have len: "i < length ss" by auto
  from len
  have "(take i ss @ (D\<langle>l\<cdot>\<sigma>\<rangle>) # drop (Suc i) ss)!i = D\<langle>l\<cdot>\<sigma>\<rangle>" by (auto simp: nth_append)
  with C Fun CFun have ssi: "ss!i = D\<langle>l\<cdot>\<sigma>\<rangle>" by auto
  from C' t have t': "t = Fun f (take i ss @ (D\<langle>r\<cdot>\<sigma>\<rangle>) # drop (Suc i) ss)" by auto
  from len
  have "(take i ss @ (D\<langle>r\<cdot>\<sigma>\<rangle>) # drop (Suc i) ss)!i = D\<langle>r\<cdot>\<sigma>\<rangle>" by (auto simp: nth_append)
  with t' have "t|_[i] = (D\<langle>r\<cdot>\<sigma>\<rangle>)|_[]" by auto
  then have subt_at: "t|_[i] = D\<langle>r\<cdot>\<sigma>\<rangle>" by simp
  from C C' have "D = ctxt_of_pos_term ps (ss!i)" by auto
  with pos Rlr ssi[symmetric] subt_at[symmetric]
  show ?thesis unfolding rstep_r_p_s_def Let_def by auto
qed

lemma ctxt_closure_rstep_eq [simp]: "ctxt.closure (rstep R) = rstep R"
  by (rule ctxt.closure_id) blast

lemma subst_closure_rstep_eq [simp]: "subst.closure (rstep R) = rstep R"
  by (rule subst.closure_id) blast

lemma supt_rstep_subset:
  "{\<rhd>} O rstep R \<subseteq> rstep R O {\<rhd>}"
proof (rule subrelI)
  fix s t assume "(s,t) \<in> {\<rhd>} O rstep R" then show "(s,t) \<in> rstep R O {\<rhd>}"
  proof (induct s)
    case (Var x)
    then have "\<exists>u. Var x \<rhd> u \<and> (u,t) \<in> rstep R" by auto
    then obtain u where "Var x \<rhd> u" and "(u,t) \<in> rstep R" by auto
    from \<open>Var x \<rhd> u\<close> show ?case by (cases rule: supt.cases)
  next
    case (Fun f ss)
    then obtain u where "Fun f ss \<rhd> u" and "(u,t) \<in> rstep R" by auto
    from \<open>Fun f ss \<rhd> u\<close> obtain C
      where "C \<noteq> \<box>" and "C\<langle>u\<rangle> = Fun f ss" by auto
    from \<open>C \<noteq> \<box>\<close> have "C\<langle>t\<rangle> \<rhd> t" by (rule nectxt_imp_supt_ctxt)
    from \<open>(u,t) \<in> rstep R\<close> have "(C\<langle>u\<rangle>,C\<langle>t\<rangle>) \<in> rstep R" ..
    then have "(Fun f ss,C\<langle>t\<rangle>) \<in> rstep R" unfolding \<open>C\<langle>u\<rangle> = Fun f ss\<close> .
    with \<open>C\<langle>t\<rangle> \<rhd> t\<close> show ?case by auto
  qed
qed

lemma ne_rstep_seq_imp_list_of_terms:
  assumes "(s,t) \<in> (rstep R)\<^sup>+"
  shows "\<exists>ts. length ts > 1 \<and> ts!0 = s \<and> ts!(length ts - 1) = t \<and>
         (\<forall>i<length ts - 1. (ts!i,ts!(Suc i)) \<in> (rstep R))" (is "\<exists>ts. _ \<and> _ \<and> _ \<and> ?P ts")
  using assms
proof (induct rule: trancl.induct)
  case (r_into_trancl x y)
  let ?ts = "[x,y]"
  have "length ?ts > 1" by simp
  moreover have "?ts!0 = x" by simp
  moreover have "?ts!(length ?ts - 1) = y" by simp
  moreover from r_into_rtrancl r_into_trancl have "?P ?ts" by auto
  ultimately show ?case by fast
next
  case (trancl_into_trancl x y z)
  then obtain ts where "length ts > 1" and "ts!0 = x"
    and last1: "ts!(length ts - 1) = y" and "?P ts" by auto
  let ?ts = "ts@[z]"
  have len: "length ?ts = length ts + 1" by simp
  from \<open>length ts > 1\<close> have "length ?ts > 1" by auto
  moreover with \<open>ts!0 = x\<close> have "?ts!0 = x" by (induct ts) auto
  moreover have last2: "?ts!(length ?ts - 1) = z" by simp
  moreover have "?P ?ts"
  proof (intro allI impI)
    fix i assume A: "i < length ?ts - 1"
    show "(?ts!i,?ts!(Suc i)) \<in> rstep R"
    proof (cases "i < length ts - 1")
      case True with \<open>?P ts\<close> A show ?thesis unfolding len unfolding nth_append by auto
    next
      case False with A have "i = length ts - 1" by simp
      with last1 \<open>length ts > 1\<close> have "?ts!i = y" unfolding nth_append by auto
      have "Suc i = length ?ts - 1" using \<open>i = length ts - 1\<close> using \<open>length ts > 1\<close> by auto
      with last2 have "?ts!(Suc i) = z" by auto
      from \<open>(y,z) \<in> rstep R\<close> show ?thesis unfolding \<open>?ts!(Suc i) = z\<close> \<open>?ts!i = y\<close> .
    qed
  qed
  ultimately show ?case by fast
qed


locale E_compatible =
  fixes R :: "('f,'v)trs" and E :: "('f,'v)trs"
  assumes E: "E O R = R" "Id \<subseteq> E"
begin

definition restrict_SN_supt_E :: "('f, 'v) trs" where
  "restrict_SN_supt_E = restrict_SN R R \<union> restrict_SN (E O {\<rhd>} O E) R"

lemma ctxt_closed_R_imp_supt_restrict_SN_E_distr:
  assumes "ctxt.closed R"
    and "(s,t) \<in> (restrict_SN (E O {\<rhd>}) R)"
    and "(t,u) \<in> restrict_SN R R"
  shows "(\<exists>t. (s,t) \<in> restrict_SN R R \<and> (t,u) \<in> restrict_SN (E O {\<rhd>}) R)" (is "\<exists> t. _ \<and> (t,u) \<in> ?snSub")
proof -
  from \<open>(s,t) \<in> ?snSub\<close> obtain v where "SN_on R {s}" and ac: "(s,v) \<in> E" and "v \<rhd> t" unfolding restrict_SN_def supt_def by auto
  from \<open>v \<rhd> t\<close> obtain C where "C \<noteq> Hole" and v: "C\<langle>t\<rangle> = v" by best
  from \<open>(t,u) \<in> restrict_SN R R\<close> have "(t,u) \<in> R" unfolding restrict_SN_def by auto
  from \<open>ctxt.closed R\<close> and this have RCtCu: "(C\<langle>t\<rangle>,C\<langle>u\<rangle>) \<in> R" by (rule ctxt.closedD)
  with v ac have "(s,C\<langle>u\<rangle>) \<in> E O R" by auto
  then have sCu: "(s,C\<langle>u\<rangle>) \<in> R" using E by simp
  with \<open>SN_on R {s}\<close> have one: "SN_on R {C\<langle>u\<rangle>}"
    using step_preserves_SN_on[of "s" "C\<langle>u\<rangle>" R] by blast
  from \<open>C \<noteq> \<box>\<close> have "C\<langle>u\<rangle> \<rhd> u" by auto
  with one E have "(C\<langle>u\<rangle>,u) \<in> ?snSub" unfolding restrict_SN_def supt_def by auto
  from sCu and \<open>SN_on R {s}\<close> and \<open>(C\<langle>u\<rangle>,u) \<in> ?snSub\<close> show ?thesis unfolding restrict_SN_def by auto
qed

lemma ctxt_closed_R_imp_restrict_SN_qc_E_supt:
  assumes ctxt: "ctxt.closed R"
  shows "quasi_commute (restrict_SN R R) (restrict_SN (E O {\<rhd>} O E) R)" (is "quasi_commute ?r ?s")
proof -
  have "?s O ?r \<subseteq> ?r O (?r \<union> ?s)\<^sup>*"
  proof (rule subrelI)
    fix x y
    assume "(x,y) \<in> ?s O ?r"
    from this obtain z where "(x,z) \<in> ?s" and "(z,y) \<in> ?r" by best
    then obtain v w where ac: "(x,v) \<in> E" and vw: "v \<rhd> w" and wz: "(w,z) \<in> E" and zy: "(z,y) \<in> R" and "SN_on R {x}" unfolding restrict_SN_def supt_def
      using E(2) by auto
    from wz zy have "(w,y) \<in> E O R" by auto
    with E have wy: "(w,y) \<in> R" by auto
    from ctxt_closed_R_imp_supt_R_distr[OF ctxt vw wy] obtain w where "(v,w) \<in> R" and "w \<rhd> y" using ctxt_closed_R_imp_supt_R_distr[where R = R and s = v and t = z and u = y] by auto
    with ac E have "(x,w) \<in> R" and "w \<rhd> y" by auto
    from this and \<open>SN_on R {x}\<close> have "SN_on R {w}" using step_preserves_SN_on
      unfolding supt_supteq_conv by auto
    with \<open>w \<rhd> y\<close> E have "(w,y) \<in> ?s" unfolding restrict_SN_def supt_def by force
    with \<open>(x,w) \<in> R\<close> \<open>SN_on R {x}\<close> show "(x,y) \<in> ?r O (?r \<union> ?s)\<^sup>*" unfolding restrict_SN_def by auto
  qed
  then show ?thesis unfolding quasi_commute_def .
qed

lemma ctxt_closed_imp_SN_restrict_SN_E_supt:
  assumes "ctxt.closed R"
    and SN: "SN (E O {\<rhd>} O E)"
  shows "SN restrict_SN_supt_E"
proof -
  let ?r = "restrict_SN R R"
  let ?s = "restrict_SN (E O {\<rhd>} O E) R"
  from \<open>ctxt.closed R\<close> have "quasi_commute ?r ?s"
    by (rule ctxt_closed_R_imp_restrict_SN_qc_E_supt)
  from SN have "SN ?s" by (rule SN_subset, auto simp: restrict_SN_def)
  have "SN ?r" by (rule SN_restrict_SN_idemp)
  from \<open>SN ?r\<close> and \<open>SN ?s\<close> and \<open>quasi_commute ?r ?s\<close>
  show ?thesis unfolding restrict_SN_supt_E_def by (rule quasi_commute_imp_SN)
qed
end

lemma E_compatible_Id: "E_compatible R Id"
  by standard auto

definition restrict_SN_supt :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs" where
  "restrict_SN_supt R = restrict_SN R R \<union> restrict_SN {\<rhd>} R"

lemma ctxt_closed_SN_on_subt:
  assumes "ctxt.closed R" and "SN_on R {s}" and "s \<unrhd> t"
  shows "SN_on R {t}"
proof (rule ccontr)
  assume "\<not> SN_on R {t}"
  then obtain A where "A 0 = t" and "\<forall>i. (A i,A (Suc i)) \<in> R"
    unfolding SN_on_def by best
  from \<open>s \<unrhd> t\<close> obtain C where "s = C\<langle>t\<rangle>" by auto
  let ?B = "\<lambda>i. C\<langle>A i\<rangle>"
  have "\<forall>i. (?B i,?B(Suc i)) \<in> R"
  proof
    fix i
    from \<open>\<forall>i. (A i,A(Suc i)) \<in> R\<close> have "(?B i,?B(Suc i)) \<in> ctxt.closure(R)" by fast
    then show "(?B i,?B(Suc i)) \<in> R" using \<open>ctxt.closed R\<close> by auto
  qed
  with \<open>A 0 = t\<close> have "?B 0 = s \<and> (\<forall>i. (?B i,?B(Suc i)) \<in> R)" unfolding \<open>s = C\<langle>t\<rangle>\<close> by auto
  then have "\<not> SN_on R {s}" unfolding SN_on_def by auto
  with assms show "False" by simp
qed

lemma ctxt_closed_R_imp_supt_restrict_SN_distr:
  assumes R: "ctxt.closed R"
    and st: "(s,t) \<in> (restrict_SN {\<rhd>} R)"
    and tu: "(t,u) \<in> restrict_SN R R"
  shows "(\<exists>t. (s,t) \<in> restrict_SN R R \<and> (t,u) \<in> restrict_SN {\<rhd>} R)" (is "\<exists> t. _ \<and> (t,u) \<in> ?snSub")
  using E_compatible.ctxt_closed_R_imp_supt_restrict_SN_E_distr[OF E_compatible_Id R _ tu, of s]
    st by auto

lemma ctxt_closed_R_imp_restrict_SN_qc_supt:
  assumes "ctxt.closed R"
  shows "quasi_commute (restrict_SN R R) (restrict_SN supt R)" (is "quasi_commute ?r ?s")
  using E_compatible.ctxt_closed_R_imp_restrict_SN_qc_E_supt[OF E_compatible_Id assms] by auto

lemma ctxt_closed_imp_SN_restrict_SN_supt:
  assumes "ctxt.closed R"
  shows "SN (restrict_SN_supt R)"
  using E_compatible.ctxt_closed_imp_SN_restrict_SN_E_supt[OF E_compatible_Id assms]
  unfolding E_compatible.restrict_SN_supt_E_def[OF E_compatible_Id] restrict_SN_supt_def
  using SN_supt by auto

lemma SN_restrict_SN_supt_rstep:
  shows "SN (restrict_SN_supt (rstep R))"
proof -
  have "ctxt.closed (rstep R)" by (rule ctxt_closed_rstep)
  then show ?thesis by (rule ctxt_closed_imp_SN_restrict_SN_supt)
qed

lemma nrrstep_imp_pos_term:
  "(Fun f ss,t) \<in> nrrstep R \<Longrightarrow>
    \<exists>i s. t = Fun f (ss[i:=s]) \<and> (ss!i,s) \<in> rstep R \<and> i < length ss"
proof -
  assume "(Fun f ss,t) \<in> nrrstep R"
  then obtain l r i ps \<sigma> where rstep_rps:"(Fun f ss,t) \<in> rstep_r_p_s R (l,r) (i#ps) \<sigma>"
    unfolding nrrstep_def by auto
  then obtain C
    where "(l,r) \<in> R"
      and pos: "(i#ps) \<in> poss (Fun f ss)"
      and C: "C = ctxt_of_pos_term (i#ps) (Fun f ss)"
      and "C\<langle>l\<cdot>\<sigma>\<rangle> = Fun f ss"
      and t: "C\<langle>r\<cdot>\<sigma>\<rangle> = t"
    unfolding rstep_r_p_s_def Let_def by auto
  then obtain D where "C = More f (take i ss) D (drop (Suc i) ss)" by auto
  with t have t': "t = Fun f (take i ss @ (D\<langle>r\<cdot>\<sigma>\<rangle>) # drop (Suc i) ss)" by auto
  from rstep_rps have "(ss!i,t|_[i]) \<in> rstep_r_p_s R (l,r) ps \<sigma>"
    by (rule rstep_i_pos_imp_rstep_arg_i_pos)
  then have rstep:"(ss!i,t|_[i]) \<in> rstep R" by (auto simp: rstep_iff_rstep_r_p_s)
  then have "(C\<langle>ss!i\<rangle>,C\<langle>t|_[i]\<rangle>) \<in> rstep R" ..
  from pos have len: "i < length ss" by auto
  from len
  have "(take i ss @ (D\<langle>r\<cdot>\<sigma>\<rangle>) # drop (Suc i) ss)!i = D\<langle>r\<cdot>\<sigma>\<rangle>" by (auto simp: nth_append)
  with C t' have "t|_[i] = D\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  with t' have "t = Fun f (take i ss @ (t|_[i]) # drop (Suc i) ss)" by auto
  with len have "t = Fun f (ss[i:=t|_[i]])" by (auto simp: upd_conv_take_nth_drop)
  with rstep len show "\<exists>i s. t = Fun f (ss[i:=s]) \<and> (ss!i,s) \<in> rstep R \<and> i < length ss" by auto
qed


lemma rstep_cases[consumes 1, case_names root nonroot]:
  "\<lbrakk>(s,t) \<in> rstep R; (s,t) \<in> rrstep R \<Longrightarrow> P; (s,t) \<in> nrrstep R \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: rstep_iff_rrstep_or_nrrstep)

lemma nrrstep_imp_rstep: "(s,t) \<in> nrrstep R \<Longrightarrow> (s,t) \<in> rstep R"
  by (auto simp: rstep_iff_rrstep_or_nrrstep)

lemma nrrstep_imp_Fun: "(s,t) \<in> nrrstep R \<Longrightarrow> \<exists>f ss. s = Fun f ss"
proof -
  assume "(s,t) \<in> nrrstep R"
  then obtain i ps where "i#ps \<in> poss s"
    unfolding nrrstep_def rstep_r_p_s_def Let_def by auto
  then show "\<exists>f ss. s = Fun f ss" by (cases s) auto
qed

lemma nrrstep_imp_subt_rstep:
  assumes "(s,t) \<in> nrrstep R"
  shows "\<exists>i. i < num_args s \<and> num_args s = num_args t \<and> (s|_[i],t|_[i]) \<in> rstep R \<and> (\<forall>j. i \<noteq> j \<longrightarrow> s|_[j] = t|_[j])"
proof -
  from \<open>(s,t) \<in> nrrstep R\<close> obtain f ss where "s = Fun f ss" using nrrstep_imp_Fun by blast
  with \<open>(s,t) \<in> nrrstep R\<close> have "(Fun f ss,t) \<in> nrrstep R" by simp
  then obtain i u where "t = Fun f (ss[i := u])" and "(ss!i,u) \<in> rstep R" and "i < length ss"
    using nrrstep_imp_pos_term by best
  from \<open>s = Fun f ss\<close> and \<open>t = Fun f (ss[i := u])\<close> have "num_args s = num_args t" by auto
  from \<open>i < length ss\<close> and \<open>s = Fun f ss\<close> have "i < num_args s" by auto
  from \<open>s = Fun f ss\<close> have "s|_[i] = (ss!i)" by auto
  from \<open>t = Fun f (ss[i := u])\<close> and \<open>i < length ss\<close> have "t|_[i] = u" by auto
  from \<open>s = Fun f ss\<close> and \<open>t = Fun f (ss[i := u])\<close>
  have  "\<forall>j. j \<noteq> i \<longrightarrow> s|_[j] = t|_[j]" by auto
  with \<open>(ss!i,u) \<in> rstep R\<close>
    and \<open>i < num_args s\<close>
    and \<open>num_args s = num_args t\<close>
    and \<open>s|_[i] = (ss!i)\<close>[symmetric] and \<open>t|_[i] = u\<close>[symmetric]
  show ?thesis by (auto)
qed

lemma nrrstep_subt: assumes "(s, t) \<in> nrrstep R" shows "\<exists>u\<lhd>s. \<exists>v\<lhd>t. (u, v) \<in> rstep R"
proof -
  from assms obtain l r C \<sigma> where "(l, r) \<in> R" and "C \<noteq> \<box>"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" unfolding nrrstep_def' by best
  from \<open>C \<noteq> \<box>\<close> s have "s \<rhd> l\<cdot>\<sigma>" by auto
  moreover from \<open>C \<noteq> \<box>\<close> t have "t \<rhd> r\<cdot>\<sigma>" by auto
  moreover from \<open>(l, r) \<in> R\<close> have "(l\<cdot>\<sigma>, r\<cdot>\<sigma>) \<in> rstep R" by auto
  ultimately show ?thesis by auto
qed

lemma nrrstep_args:
  assumes "(s, t) \<in> nrrstep R"
  shows "\<exists>f ss ts. s = Fun f ss \<and> t = Fun f ts \<and> length ss = length ts
    \<and> (\<exists>j<length ss. (ss!j, ts!j) \<in> rstep R \<and> (\<forall>i<length ss. i \<noteq> j \<longrightarrow> ss!i = ts!i))"
proof -
  from assms obtain l r C \<sigma> where "(l, r) \<in> R" and "C \<noteq> \<box>"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" unfolding nrrstep_def' by best
  from \<open>C \<noteq> \<box>\<close> obtain f ss1 D ss2 where C: "C = More f ss1 D ss2" by (induct C) auto
  have "s = Fun f (ss1 @ D\<langle>l\<cdot>\<sigma>\<rangle> # ss2)" (is "_ = Fun f ?ss") by (simp add: s C)
  moreover have "t = Fun f (ss1 @ D\<langle>r\<cdot>\<sigma>\<rangle> # ss2)" (is "_ = Fun f ?ts") by (simp add: t C)
  moreover have "length ?ss = length ?ts" by simp
  moreover have "\<exists>j<length ?ss.
    (?ss!j, ?ts!j) \<in> rstep R \<and> (\<forall>i<length ?ss. i \<noteq> j \<longrightarrow> ?ss!i = ?ts!i)"
  proof -
    let ?j = "length ss1"
    have "?j < length ?ss" by simp
    moreover have "(?ss!?j, ?ts!?j) \<in> rstep R"
    proof -
      from \<open>(l, r) \<in> R\<close> have "(D\<langle>l\<cdot>\<sigma>\<rangle>, D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R" by auto
      then show ?thesis by auto
    qed
    moreover have "\<forall>i<length ?ss. i \<noteq> ?j \<longrightarrow> ?ss!i = ?ts!i" (is "\<forall>i<length ?ss. _ \<longrightarrow> ?P i")
    proof (intro allI impI)
      fix i assume "i < length ?ss" and "i \<noteq> ?j"
      then have "i < length ss1 \<or> length ss1 < i" by auto
      then show "?P i"
      proof
        assume "i < length ss1" then show "?P i" by (auto simp: nth_append)
      next
        assume "i > length ss1" then show "?P i"
          using \<open>i < length ?ss\<close> by (auto simp: nth_Cons' nth_append)
      qed
    qed
    ultimately show ?thesis by best
  qed
  ultimately show ?thesis by auto
qed

lemma nrrstep_iff_arg_rstep:
  "(s,t) \<in> nrrstep R \<longleftrightarrow>
   (\<exists>f ss i t'. s = Fun f ss \<and> i < length ss \<and> t = Fun f (ss[i:=t']) \<and> (ss!i,t') \<in> rstep R)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume L: ?L
  from nrrstep_args[OF this]
  obtain f ss ts where "s = Fun f ss" "t = Fun f ts" by auto
  with nrrstep_imp_pos_term[OF L[unfolded this]]
  show ?R by auto
next assume R: ?R
  then obtain f i ss t'
    where s: "s = Fun f ss" and t: "t = Fun f (ss[i:=t'])"
      and i: "i < length ss" and st': "(ss ! i, t') \<in> rstep R" by auto
  from st' obtain C l r \<sigma> where lr: "(l, r) \<in> R" and s': "ss!i = C\<langle>l \<cdot> \<sigma>\<rangle>" and t': "t' = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  let ?D = "More f (take i ss) C (drop (Suc i) ss)"
  have "s = ?D\<langle>l \<cdot> \<sigma>\<rangle>" "t = ?D\<langle>r \<cdot> \<sigma>\<rangle>" unfolding s t
    using id_take_nth_drop[OF i] upd_conv_take_nth_drop[OF i] s' t' by auto
  with lr show ?L apply(rule nrrstepI) using t' by auto
qed


lemma subterms_NF_imp_SN_on_nrrstep:
  assumes "\<forall>s\<lhd>t. s \<in> NF (rstep R)" shows "SN_on (nrrstep R) {t}"
proof
  fix S assume "S 0 \<in> {t}" and "\<forall>i. (S i, S (Suc i)) \<in> nrrstep R"
  then have "(t, S (Suc 0)) \<in> nrrstep R" by auto
  then obtain l r C \<sigma> where "(l, r) \<in> R" and "C \<noteq> \<box>" and t: "t = C\<langle>l\<cdot>\<sigma>\<rangle>" unfolding nrrstep_def' by auto
  then obtain f ss1 D ss2 where C: "C = More f ss1 D ss2" by (induct C) auto
  have "t \<rhd> D\<langle>l\<cdot>\<sigma>\<rangle>" unfolding t C by auto
  moreover have "D\<langle>l\<cdot>\<sigma>\<rangle> \<notin> NF (rstep R)"
  proof -
    from \<open>(l, r) \<in> R\<close> have "(D\<langle>l\<cdot>\<sigma>\<rangle>, D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R" by auto
    then show ?thesis by auto
  qed
  ultimately show False using assms by simp
qed

lemma args_NF_imp_SN_on_nrrstep:
  assumes "\<forall>t\<in>set ts. t \<in> NF (rstep R)" shows "SN_on (nrrstep R) {Fun f ts}"
proof
  fix S assume "S 0 \<in> {Fun f ts}" and "\<forall>i. (S i, S (Suc i)) \<in> nrrstep R"
  then have "(Fun f ts, S (Suc 0)) \<in> nrrstep R"
    unfolding singletonD[OF \<open>S 0 \<in> {Fun f ts}\<close>, symmetric] by simp
  then obtain l r C \<sigma> where "(l, r) \<in> R" and "C \<noteq> \<box>" and "Fun f ts = C\<langle>l\<cdot>\<sigma>\<rangle>"
    unfolding nrrstep_def' by auto
  then obtain ss1 D ss2 where C: "C = More f ss1 D ss2" by (induct C) auto
  with \<open>Fun f ts = C\<langle>l\<cdot>\<sigma>\<rangle>\<close> have "D\<langle>l\<cdot>\<sigma>\<rangle> \<in> set ts" by auto
  moreover have "D\<langle>l\<cdot>\<sigma>\<rangle> \<notin> NF (rstep R)"
  proof -
    from \<open>(l, r) \<in> R\<close> have "(D\<langle>l\<cdot>\<sigma>\<rangle>, D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R" by auto
    then show ?thesis by auto
  qed
  ultimately show False using assms by simp
qed

lemma rrstep_imp_rule_subst:
  assumes "(s,t) \<in> rrstep R"
  shows "\<exists>l r \<sigma>. (l,r) \<in> R \<and> (l\<cdot>\<sigma>) = s \<and> (r\<cdot>\<sigma>) = t"
proof -
  have "ctxt_of_pos_term [] s = Hole" by auto
  obtain l r \<sigma> where "(s,t) \<in> rstep_r_p_s R (l,r) [] \<sigma>" using assms unfolding rrstep_def by best
  then have "let C = ctxt_of_pos_term [] s in [] \<in> poss s \<and> (l,r) \<in> R \<and> C\<langle>l\<cdot>\<sigma>\<rangle> = s \<and> C\<langle>r\<cdot>\<sigma>\<rangle> = t" unfolding rstep_r_p_s_def by simp
  with \<open>ctxt_of_pos_term [] s = Hole\<close> have "(l,r) \<in> R" and "l\<cdot>\<sigma> = s" and "r\<cdot>\<sigma> = t" unfolding Let_def by auto
  then show ?thesis by auto
qed

lemma nrrstep_preserves_root:
  assumes "(Fun f ss,t) \<in> nrrstep R" (is "(?s,t) \<in> nrrstep R") shows "\<exists>ts. t = (Fun f ts)"
  using assms unfolding nrrstep_def rstep_r_p_s_def Let_def by auto

lemma nrrstep_equiv_root: assumes "(s,t) \<in> nrrstep R" shows "\<exists>f ss ts. s = Fun f ss \<and> t = Fun f ts"
proof -
  from assms obtain f ss where "s = Fun f ss" using nrrstep_imp_Fun by best
  with assms obtain ts where "t = Fun f ts" using nrrstep_preserves_root by best
  from \<open>s = Fun f ss\<close> and \<open>t = Fun f ts\<close> show ?thesis by best
qed

lemma nrrstep_reflects_root:
  assumes "(s,Fun g ts) \<in> nrrstep R" (is "(s,?t) \<in> nrrstep R")
  shows "\<exists>ss. s = (Fun g ss)"
proof -
  from assms obtain f ss ts' where "s = Fun f ss" and "Fun g ts = Fun f ts'" using nrrstep_equiv_root by best
  then have "f = g" by simp
  with \<open>s = Fun f ss\<close> have "s = Fun g ss" by simp
  then show ?thesis by auto
qed

lemma nrrsteps_preserve_root:
  assumes "(Fun f ss,t) \<in> (nrrstep R)\<^sup>*"
  shows "\<exists>ts. t = (Fun f ts)"
  using assms by induct (auto simp: nrrstep_preserves_root)

lemma nrrstep_Fun_imp_arg_rsteps:
  assumes "(Fun f ss,Fun f ts) \<in> nrrstep R" (is "(?s,?t) \<in> nrrstep R") and "i < length ss"
  shows "(ss!i,ts!i) \<in> (rstep R)\<^sup>*"
proof -
  from assms have "[i] \<in> poss ?s" using empty_pos_in_poss by simp
  from \<open>(?s,?t) \<in> nrrstep R\<close>
  obtain l r j ps \<sigma>
    where A: "let C = ctxt_of_pos_term (j#ps) ?s in (j#ps) \<in> poss ?s \<and> (l,r) \<in> R \<and> C\<langle>l\<cdot>\<sigma>\<rangle> = ?s \<and> C\<langle>r\<cdot>\<sigma>\<rangle> = ?t" unfolding nrrstep_def rstep_r_p_s_def by force
  let ?C = "ctxt_of_pos_term (j#ps) ?s"
  from A have "(j#ps) \<in> poss ?s" and "(l,r) \<in> R" and "?C\<langle>l\<cdot>\<sigma>\<rangle> = ?s" and "?C\<langle>r\<cdot>\<sigma>\<rangle> = ?t" using Let_def by auto
  have C: "?C = More f (take j ss) (ctxt_of_pos_term ps (ss!j)) (drop (Suc j) ss)" (is "?C = More f ?ss1 ?D ?ss2") by auto
  from \<open>?C\<langle>l\<cdot>\<sigma>\<rangle> = ?s\<close> have "?D\<langle>l\<cdot>\<sigma>\<rangle> = (ss!j)" by (auto simp: take_drop_imp_nth)
  from \<open>(l,r) \<in> R\<close> have "(l\<cdot>\<sigma>,r\<cdot>\<sigma>) \<in> (subst.closure R)" by auto
  then have "(?D\<langle>l\<cdot>\<sigma>\<rangle>,?D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> (ctxt.closure(subst.closure R))"
    and "(?C\<langle>l\<cdot>\<sigma>\<rangle>,?C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> (ctxt.closure(subst.closure R))" by (auto simp only: ctxt.closure.intros)
  then have D_rstep: "(?D\<langle>l\<cdot>\<sigma>\<rangle>,?D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R" and "(?C\<langle>l\<cdot>\<sigma>\<rangle>,?C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R"
    unfolding rstep_eq_closure by auto
  from \<open>?C\<langle>r\<cdot>\<sigma>\<rangle> = ?t\<close> and C have "?t = Fun f (take j ss @ ?D\<langle>r\<cdot>\<sigma>\<rangle> # drop (Suc j) ss)" by auto
  then have ts: "ts = (take j ss @ ?D\<langle>r\<cdot>\<sigma>\<rangle> # drop (Suc j) ss)" by auto
  have "j = i \<or> j \<noteq> i" by simp
  from \<open>j#ps \<in> poss ?s\<close> have "j < length ss" by simp
  then have "(take j ss @ ?D\<langle>r\<cdot>\<sigma>\<rangle> # drop (Suc j) ss) ! j = ?D\<langle>r\<cdot>\<sigma>\<rangle>" by (auto simp: nth_append_take)
  with ts have "ts!j = ?D\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  have "j = i \<or> j \<noteq> i" by simp
  then show "(ss!i,ts!i) \<in> (rstep R)\<^sup>*"
  proof
    assume "j = i"
    with \<open>ts!j = ?D\<langle>r\<cdot>\<sigma>\<rangle>\<close> and \<open>?D\<langle>l\<cdot>\<sigma>\<rangle> = ss!j\<close> and D_rstep show ?thesis by auto
  next
    assume "j \<noteq> i"
    with \<open>i < length ss\<close> and \<open>j < length ss\<close> have "(take j ss @ ?D\<langle>r\<cdot>\<sigma>\<rangle> # drop (Suc j) ss) ! i = ss!i" by (auto simp: nth_append_take_drop_is_nth_conv)
    with ts have "ts!i = ss!i" by auto
    then show ?thesis by auto
  qed
qed

lemma nrrstep_imp_arg_rsteps:
  assumes "(s,t) \<in> nrrstep R" and "i < num_args s" shows "(args s!i,args t!i) \<in> (rstep R)\<^sup>*"
proof (cases s)
  fix x assume "s = Var x" then show ?thesis using assms by auto
next
  fix f ss assume "s = Fun f ss"
  then have "(Fun f ss,t) \<in> nrrstep R" using assms by simp
  then obtain ts where "t = Fun f ts" using nrrstep_preserves_root by best
  with \<open>(s,t) \<in> nrrstep R\<close> and \<open>s = Fun f ss\<close> have "(Fun f ss,Fun f ts) \<in> nrrstep R" by simp
  from  \<open>s = Fun f ss\<close> and \<open>i < num_args s\<close> have "i < length ss" by simp
  with \<open>(Fun f ss,Fun f ts) \<in> nrrstep R\<close>
  have "(ss!i,ts!i) \<in> (rstep R)\<^sup>*" by (rule nrrstep_Fun_imp_arg_rsteps)
  with \<open>s = Fun f ss\<close> and \<open>t = Fun f ts\<close> show ?thesis by simp
qed

lemma nrrsteps_imp_rsteps: "(s,t) \<in> (nrrstep R)\<^sup>* \<Longrightarrow> (s,t) \<in> (rstep R)\<^sup>*"
proof (induct rule: rtrancl.induct)
  case (rtrancl_refl a) then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have IH: "(a,b) \<in> (rstep R)\<^sup>*" and nrrstep: "(b,c) \<in> nrrstep R" by auto
  from nrrstep have "(b,c) \<in> rstep R" using nrrstep_imp_rstep by auto
  with IH show ?case by auto
qed

lemma nrrstep_Fun_preserves_num_args:
  assumes "(Fun f ss,Fun f ts) \<in> nrrstep R" (is "(?s,?t) \<in> nrrstep R")
  shows "length ss = length ts"
proof -
  from assms obtain l r i ps \<sigma>
    where "let C = ctxt_of_pos_term (i#ps) ?s in (i#ps) \<in> poss ?s \<and> (l,r) \<in> R \<and> C\<langle>l\<cdot>\<sigma>\<rangle> = ?s \<and> C\<langle>r\<cdot>\<sigma>\<rangle> = ?t" (is "let C = ?C in _")
    unfolding nrrstep_def rstep_r_p_s_def by force
  then have "(l,r) \<in> R" and Cl: "?C\<langle>l\<cdot>\<sigma>\<rangle> = ?s" and Cr: "?C\<langle>r\<cdot>\<sigma>\<rangle> = ?t" unfolding Let_def by auto
  have C: "?C = More f (take i ss) (ctxt_of_pos_term ps (ss!i)) (drop (Suc i) ss)" (is "?C = More f ?ss1 ?D ?ss2") by simp
  from C and Cl have s: "?s = Fun f (take i ss @ ?D\<langle>l\<cdot>\<sigma>\<rangle> # drop (Suc i) ss)" (is "?s = Fun f ?ss") by simp
  from C and Cr have t: "?t = Fun f (take i ss @ ?D\<langle>r\<cdot>\<sigma>\<rangle> # drop (Suc i) ss)" (is "?t = Fun f ?ts") by simp
  from s and t have ss: "ss = ?ss" and ts: "ts = ?ts" by auto
  have "length ?ss = length ?ts" by auto
  with ss and ts show ?thesis by simp
qed

lemma nrrstep_equiv_num_args:
  assumes "(s,t) \<in> nrrstep R" shows "num_args s = num_args t"
proof -
  from assms obtain f ss ts where s:"s = Fun f ss" and t:"t = Fun f ts" using nrrstep_equiv_root by best
  with assms have "(Fun f ss,Fun f ts) \<in> nrrstep R" by simp
  then have "length ss = length ts" by (rule nrrstep_Fun_preserves_num_args)
  with s and t show ?thesis by auto
qed

lemma nrrsteps_equiv_num_args:
  assumes "(s,t) \<in> (nrrstep R)\<^sup>*" shows "num_args s = num_args t"
  using assms by (induct, auto simp: nrrstep_equiv_num_args)

lemma nrrstep_preserves_num_args:
  assumes "(s,t) \<in> nrrstep R" and "i < num_args s" shows "i < num_args t"
proof (cases s)
  fix x assume "s = Var x" then show ?thesis using assms by auto
next
  fix f ss assume "s = Fun f ss"
  with assms obtain ts where "t = Fun f ts" using nrrstep_preserves_root by best
  from \<open>(s,t) \<in> nrrstep R\<close> have "length ss = length ts" unfolding \<open>s = Fun f ss\<close> and \<open>t = Fun f ts\<close> by (rule nrrstep_Fun_preserves_num_args)
  with assms and \<open>s = Fun f ss\<close> and \<open>t = Fun f ts\<close> show ?thesis by auto
qed

lemma nrrstep_reflects_num_args:
  assumes "(s,t) \<in> nrrstep R" and "i < num_args t" shows "i < num_args s"
proof (cases t)
  fix x assume "t = Var x" then show ?thesis using assms by auto
next
  fix g ts assume "t = Fun g ts"
  with assms obtain ss where "s = Fun g ss" using nrrstep_reflects_root by best
  from \<open>(s,t) \<in> nrrstep R\<close> have "length ss = length ts" unfolding \<open>s = Fun g ss\<close> and \<open>t = Fun g ts\<close> by (rule nrrstep_Fun_preserves_num_args)
  with assms and \<open>s = Fun g ss\<close> and \<open>t = Fun g ts\<close> show ?thesis by auto
qed

lemma nrrsteps_imp_arg_rsteps:
  assumes "(s,t) \<in> (nrrstep R)\<^sup>*" and "i < num_args s"
  shows "(args s!i,args t!i) \<in> (rstep R)\<^sup>*"
  using assms
proof (induct rule: rtrancl.induct)
  case (rtrancl_refl a) then show ?case by auto
next
  case (rtrancl_into_rtrancl a b c)
  then have IH: "(args a!i,args b!i) \<in> (rstep R)\<^sup>*" by auto
  from \<open>(a,b) \<in> (nrrstep R)\<^sup>*\<close> and \<open>i < num_args a\<close> have "i < num_args b" by induct (auto simp: nrrstep_preserves_num_args)
  with \<open>(b,c) \<in> nrrstep R\<close>
  have "(args b!i,args c!i) \<in> (rstep R)\<^sup>*" by (rule nrrstep_imp_arg_rsteps)
  with IH show ?case by simp
qed

lemma nrrsteps_imp_eq_root_arg_rsteps:
  assumes steps: "(s,t) \<in> (nrrstep R)\<^sup>*"
  shows "root s = root t \<and> (\<forall>i<num_args s. (s |_ [i], t |_ [i] ) \<in> (rstep R)\<^sup>*)"
proof (cases s)
  case (Var x)
  have "s = t" using steps unfolding Var
  proof (induct)
    case (step y z)
    from nrrstep_imp_Fun[OF step(2)] step(3) have False by auto
    then show ?case ..
  qed simp
  then show ?thesis by auto
next
  case (Fun f ss)
  from nrrsteps_equiv_num_args[OF steps]
    nrrsteps_imp_arg_rsteps[OF steps]
    nrrsteps_preserve_root[OF steps[unfolded Fun]]
  show ?thesis unfolding Fun by auto
qed

lemma SN_on_imp_SN_on_subt:
  assumes "SN_on (rstep R) {t}" shows "\<forall>s\<unlhd>t. SN_on (rstep R) {s}"
proof (rule ccontr)
  assume "\<not>(\<forall>s\<unlhd>t. SN_on (rstep R) {s})"
  then obtain s where "t \<unrhd> s" and "\<not> SN_on (rstep R) {s}" by auto
  then obtain S where "S 0 = s" and chain: "chain (rstep R) S" by auto
  from \<open>t \<unrhd> s\<close> obtain C where t: "t = C\<langle>s\<rangle>" by auto
  let ?S = "\<lambda>i. C\<langle>S i\<rangle>"
  from \<open>S 0 = s\<close> have "?S 0 = t" by (simp add: t)
  moreover from chain have "chain (rstep R) ?S" by blast
  ultimately have "\<not> SN_on (rstep R) {t}" by best
  with assms show False by simp
qed

lemma not_SN_on_subt_imp_not_SN_on:
  assumes "\<not> SN_on (rstep R) {t}" and "s \<unrhd> t"
  shows "\<not> SN_on (rstep R) {s}"
  using assms SN_on_imp_SN_on_subt by blast

lemma SN_on_instance_imp_SN_on_var:
  assumes "SN_on (rstep R) {t \<cdot> \<sigma>}" and "x \<in> vars_term t"
  shows "SN_on (rstep R) {Var x \<cdot> \<sigma>}"
proof -
  from assms have "t \<unrhd> Var x" by auto
  then have "t\<cdot>\<sigma> \<unrhd> (Var x)\<cdot>\<sigma>" by (rule supteq_subst)
  with SN_on_imp_SN_on_subt and assms show ?thesis by best
qed

lemma var_imp_var_of_arg:
  assumes "x \<in> vars_term (Fun f ss)" (is "x \<in> vars_term ?s")
  shows "\<exists>i < num_args (Fun f ss). x \<in> vars_term (ss!i)"
proof -
  from assms have "x \<in> \<Union>(set (map vars_term ss))" by simp
  then have "x \<in> (\<Union>i<length ss. vars_term(ss!i))" unfolding set_conv_nth by auto
  then have "\<exists>i<length ss. x \<in> vars_term(ss!i)" using UN_iff by best
  then obtain i where "i < length ss" and "x \<in> vars_term(ss!i)" by auto
  then have "i < num_args ?s" by simp
  with \<open>x \<in> vars_term(ss!i)\<close> show ?thesis by auto
qed

lemma subt_instance_and_not_subst_imp_subt:
  "s\<cdot>\<sigma> \<unrhd> t \<Longrightarrow> \<forall>x \<in> vars_term s. \<not>((Var x)\<cdot>\<sigma> \<unrhd> t) \<Longrightarrow> \<exists>u. s \<unrhd> u \<and> t = u\<cdot>\<sigma>"
proof (induct s arbitrary: t rule: term.induct)
  case (Var x) then show ?case by auto
next
  case (Fun f ss)
  from \<open>Fun f ss\<cdot>\<sigma> \<unrhd> t\<close> have "(Fun f ss\<cdot>\<sigma> = t) \<or> (Fun f ss\<cdot>\<sigma> \<rhd> t)" by auto
  then show ?case
  proof
    assume "Fun f ss\<cdot>\<sigma> = t" with Fun show ?thesis by auto
  next
    assume "Fun f ss\<cdot>\<sigma> \<rhd> t"
    then have "Fun f (map (\<lambda>t. t\<cdot>\<sigma>) ss) \<rhd> t" by simp
    then have "\<exists>s \<in> set (map (\<lambda>t. t\<cdot>\<sigma>) ss). s \<unrhd> t" (is "\<exists>s \<in> set ?ss'. s \<unrhd> t") by (rule supt_Fun_imp_arg_supteq)
    then obtain s' where "s' \<in> set ?ss'" and "s' \<unrhd> t" by best
    then have "\<exists>i < length ?ss'. ?ss'!i = s'" using in_set_conv_nth[where ?x = "s'"] by best
    then obtain i where "i < length ?ss'" and "?ss'!i = s'" by best
    then have "?ss'!i = (ss!i)\<cdot>\<sigma>" by auto
    from \<open>?ss'!i = s'\<close> have "s' = (ss!i)\<cdot>\<sigma>" unfolding \<open>?ss'!i = (ss!i)\<cdot>\<sigma>\<close> by simp
    from \<open>s' \<unrhd> t\<close> have "(ss!i)\<cdot>\<sigma> \<unrhd> t" unfolding \<open>s' = (ss!i)\<cdot>\<sigma>\<close> by simp
    with \<open>i < length ?ss'\<close> have "(ss!i) \<in> set ss" by auto
    with \<open>(ss!i)\<cdot>\<sigma> \<unrhd> t\<close> have "\<exists>s \<in> set ss. s\<cdot>\<sigma> \<unrhd> t" by best
    then obtain s where "s \<in> set ss" and "s\<cdot>\<sigma> \<unrhd> t" by best
    with Fun have "\<forall>x \<in> vars_term s. \<not>((Var x)\<cdot>\<sigma> \<unrhd> t)" by force
    from Fun
    have IH: "s \<in> set ss \<longrightarrow> (\<forall>v. s\<cdot>\<sigma> \<unrhd> v \<longrightarrow> (\<forall>x \<in> vars_term s. \<not> Var x\<cdot>\<sigma> \<unrhd> v) \<longrightarrow> (\<exists>u. s \<unrhd> u \<and> v = u\<cdot>\<sigma>))"
      by auto
    with \<open>s \<in> set ss\<close> have "!!v. s\<cdot>\<sigma> \<unrhd> v \<Longrightarrow> (\<forall>x \<in> vars_term s. \<not> Var x\<cdot>\<sigma> \<unrhd> v) \<longrightarrow> (\<exists>u. s \<unrhd> u \<and> v = u\<cdot>\<sigma>)"
      by simp
    with \<open>s\<cdot>\<sigma> \<unrhd> t\<close> have "(\<forall>x \<in> vars_term s. \<not> Var x\<cdot>\<sigma> \<unrhd> t) \<longrightarrow> (\<exists>u. s \<unrhd> u \<and> t = u\<cdot>\<sigma>)" by simp
    with \<open>\<forall>x \<in> vars_term s. \<not> Var x\<cdot>\<sigma> \<unrhd> t\<close> obtain u where "s \<unrhd> u" and "t = u\<cdot>\<sigma>" by best
    with \<open>s \<in> set ss\<close> have "Fun f ss \<unrhd> u" by auto
    with \<open>t = u\<cdot>\<sigma>\<close> show ?thesis by best
  qed
qed

lemma SN_imp_SN_subt:
  "SN_on (rstep R) {s} \<Longrightarrow> s \<unrhd> t \<Longrightarrow> SN_on (rstep R) {t}"
  by (rule ctxt_closed_SN_on_subt[OF ctxt_closed_rstep])

lemma subterm_preserves_SN_gen:
  assumes ctxt: "ctxt.closed R"
    and SN: "SN_on R {t}" and supt: "t \<rhd> s"
  shows "SN_on R {s}"
proof -
  from supt have "t \<unrhd> s" by auto
  then show ?thesis using ctxt_closed_SN_on_subt[OF ctxt SN, of s] by simp
qed

context E_compatible
begin

lemma SN_on_step_E_imp_SN_on: assumes "SN_on R {s}"
  and "(s,t) \<in> E"
shows "SN_on R {t}"
  using assms E(1) unfolding SN_on_all_reducts_SN_on_conv[of _ t] SN_on_all_reducts_SN_on_conv[of _ s]
  by blast

lemma SN_on_step_REs_imp_SN_on:
  assumes R: "ctxt.closed R"
    and st: "(s,t) \<in> (R \<union> E O {\<rhd>} O E)"
    and SN: "SN_on R {s}"
  shows "SN_on R {t}"
proof (cases "(s,t) \<in> R")
  case True
  from step_preserves_SN_on[OF this SN] show ?thesis .
next
  case False
  with st obtain u v where su: "(s,u) \<in> E" and uv: "u \<rhd> v" and vt: "(v,t) \<in> E" by auto
  have u: "SN_on R {u}" by (rule SN_on_step_E_imp_SN_on[OF SN su])
  with uv R have "SN_on R {v}" by (metis subterm_preserves_SN_gen)
  then show ?thesis by (rule SN_on_step_E_imp_SN_on[OF _ vt])
qed

lemma restrict_SN_supt_E_I:
  "ctxt.closed R \<Longrightarrow> SN_on R {s} \<Longrightarrow> (s,t) \<in> R \<union> E O {\<rhd>} O E \<Longrightarrow> (s,t) \<in> restrict_SN_supt_E"
  unfolding restrict_SN_supt_E_def restrict_SN_def
  using SN_on_step_REs_imp_SN_on[of s t] E(2) by auto

lemma ctxt_closed_imp_SN_on_E_supt:
  assumes R: "ctxt.closed R"
    and SN: "SN (E O {\<rhd>} O E)"
  shows "SN_on (R \<union> E O {\<rhd>} O E) {t. SN_on R {t}}"
proof -
  {
    fix f
    assume f0: "SN_on R {f 0}" and f: "\<And> i. (f i, f (Suc i)) \<in> R \<union> E O {\<rhd>} O E"
    from ctxt_closed_imp_SN_restrict_SN_E_supt[OF assms]
    have SN: "SN restrict_SN_supt_E" .
    {
      fix i
      have "SN_on R {f i}"
        by (induct i, rule f0, rule SN_on_step_REs_imp_SN_on[OF R f])
    } note fi = this
    {
      fix i
      from f[of i] fi[of i]
      have "(f i, f (Suc i)) \<in> restrict_SN_supt_E" by (metis restrict_SN_supt_E_I[OF R])
    }
    with SN have False by auto
  }
  then show ?thesis unfolding SN_on_def by blast
qed
end

lemma subterm_preserves_SN:
  "SN_on (rstep R) {t} \<Longrightarrow> t \<rhd> s \<Longrightarrow> SN_on (rstep R) {s}"
  by (rule subterm_preserves_SN_gen[OF ctxt_closed_rstep])

lemma SN_on_r_imp_SN_on_supt_union_r:
  assumes ctxt: "ctxt.closed R"
    and "SN_on R T"
  shows "SN_on (supt \<union> R) T" (is "SN_on ?S T")
proof (rule ccontr)
  assume "\<not> SN_on ?S T"
  then obtain s where ini: "s 0 : T" and chain: "chain ?S s"
    unfolding SN_on_def by auto
  have SN: "\<forall>i. SN_on R {s i}"
  proof
    fix i show "SN_on R {s i}"
    proof (induct i)
      case 0 show ?case using assms using \<open>s 0 \<in> T\<close> and SN_on_subset2[of "{s 0}" T R] by simp
    next
      case (Suc i)
      from chain have "(s i, s (Suc i)) \<in> ?S" by simp
      then show ?case
      proof
        assume "(s i, s (Suc i)) \<in> supt"
        from subterm_preserves_SN_gen[OF ctxt Suc this] show ?thesis .
      next
        assume "(s i, s (Suc i)) \<in> R"
        from step_preserves_SN_on[OF this Suc] show ?thesis .
      qed
    qed
  qed
  have "\<not> (\<exists>S. \<forall>i. (S i, S (Suc i)) \<in> restrict_SN_supt R)"
    using ctxt_closed_imp_SN_restrict_SN_supt[OF ctxt] unfolding SN_defs by auto
  moreover have "\<forall>i. (s i, s (Suc i)) \<in> restrict_SN_supt R"
  proof
    fix i
    from SN have SN: "SN_on R {s i}" by simp
    from chain have "(s i, s (Suc i)) \<in> supt \<union> R" by simp
    then show "(s i, s (Suc i)) \<in> restrict_SN_supt R"
      unfolding restrict_SN_supt_def restrict_SN_def using SN by auto
  qed
  ultimately show False by auto
qed

lemma SN_on_rstep_imp_SN_on_supt_union_rstep:
  "SN_on (rstep R) T \<Longrightarrow> SN_on (supt \<union> rstep R) T"
  by (rule SN_on_r_imp_SN_on_supt_union_r[OF ctxt_closed_rstep])

lemma SN_supt_r_trancl:
  assumes ctxt: "ctxt.closed R"
    and a: "SN R"
  shows "SN ((supt \<union> R)\<^sup>+)"
proof -
  have "SN (supt \<union> R)"
    using SN_on_r_imp_SN_on_supt_union_r[OF ctxt, of UNIV]
      and a by force
  then show "SN ((supt \<union> R)\<^sup>+)" by (rule SN_imp_SN_trancl)
qed

lemma SN_supt_rstep_trancl:
  "SN (rstep R) \<Longrightarrow> SN ((supt \<union> rstep R)\<^sup>+)"
  by (rule SN_supt_r_trancl[OF ctxt_closed_rstep])

lemma SN_imp_SN_arg_gen:
  assumes ctxt: "ctxt.closed R"
    and SN: "SN_on R {Fun f ts}" and arg: "t \<in> set ts" shows "SN_on R {t}"
proof -
  from arg have "Fun f ts \<unrhd> t" by auto
  with SN show ?thesis by (rule ctxt_closed_SN_on_subt[OF ctxt])
qed

lemma SN_imp_SN_arg:
  "SN_on (rstep R) {Fun f ts} \<Longrightarrow> t \<in> set ts \<Longrightarrow> SN_on (rstep R) {t}"
  by (rule SN_imp_SN_arg_gen[OF ctxt_closed_rstep])

lemma SNinstance_imp_SN:
  assumes "SN_on (rstep R) {t \<cdot> \<sigma>}"
  shows "SN_on (rstep R) {t}"
proof
  fix f
  assume prem: "f 0 \<in> {t}" "\<forall>i. (f i, f (Suc i)) \<in> rstep R" 
  let ?g = "\<lambda> i. (f i) \<cdot> \<sigma>"
  from prem have "?g 0 = t \<cdot> \<sigma> \<and> (\<forall> i. (?g i, ?g (Suc i)) \<in> rstep R)" using subst_closed_rstep
    by auto
  then have "\<not> SN_on (rstep R) {t \<cdot> \<sigma>}" by auto
  with assms show False by blast
qed

lemma rstep_imp_C_s_r:
  assumes "(s,t) \<in> rstep R"
  shows "\<exists>C \<sigma> l r. (l,r) \<in> R \<and> s = C\<langle>l\<cdot>\<sigma>\<rangle> \<and> t = C\<langle>r\<cdot>\<sigma>\<rangle>"
proof -
  from assms obtain l r p \<sigma> where step:"(s,t) \<in> rstep_r_p_s R (l,r) p \<sigma>"
    unfolding rstep_iff_rstep_r_p_s by best
  let ?C = "ctxt_of_pos_term p s"
  from step have "p \<in> poss s" and "(l,r) \<in> R" and "?C\<langle>l\<cdot>\<sigma>\<rangle> = s" and "?C\<langle>r\<cdot>\<sigma>\<rangle> = t"
    unfolding rstep_r_p_s_def Let_def by auto
  then have "(l,r) \<in> R \<and> s = ?C\<langle>l\<cdot>\<sigma>\<rangle> \<and> t = ?C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  then show ?thesis by force
qed

fun map_funs_rule :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('g, 'v) rule"
  where
    "map_funs_rule fg lr = (map_funs_term fg (fst lr), map_funs_term fg (snd lr))"

fun map_funs_trs :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('g, 'v) trs"
  where
    "map_funs_trs fg R = map_funs_rule fg ` R"

lemma map_funs_trs_union: "map_funs_trs fg (R \<union> S) = map_funs_trs fg R \<union> map_funs_trs fg S"
  unfolding map_funs_trs.simps by auto

lemma rstep_map_funs_term: assumes R: "\<And> f. f \<in> funs_trs R \<Longrightarrow> h f = f" and step: "(s,t) \<in> rstep R"
  shows "(map_funs_term h s, map_funs_term h t) \<in> rstep R"
proof -
  from step obtain C l r \<sigma> where s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and rule: "(l,r) \<in> R" by auto
  let ?\<sigma> = "map_funs_subst h \<sigma>"
  let ?h = "map_funs_term h"
  note funs_defs = funs_rule_def[abs_def] funs_trs_def
  from rule have lr: "funs_term l \<union> funs_term r \<subseteq> funs_trs R" unfolding funs_defs
    by auto
  have hl: "?h l = l"
    by (rule funs_term_map_funs_term_id[OF R], insert lr, auto)
  have hr: "?h r = r"
    by (rule funs_term_map_funs_term_id[OF R], insert lr, auto)
  show ?thesis unfolding s t
    unfolding map_funs_subst_distrib map_funs_term_ctxt_distrib hl hr
    by (rule rstepI[OF rule refl refl])
qed

lemma wf_trs_map_funs_trs[simp]: "wf_trs (map_funs_trs f R) = wf_trs R"
  unfolding wf_trs_def
proof (rule iffI, intro allI impI)
  fix l r
  assume "\<forall>l r. (l, r) \<in> map_funs_trs f R \<longrightarrow> (\<exists>f ts. l = Fun f ts) \<and> vars_term r \<subseteq> vars_term l" and "(l, r) \<in> R"
  then show "(\<exists>f ts. l = Fun f ts) \<and> vars_term r \<subseteq> vars_term l" by (cases l, force+)
next
  assume ass: " \<forall>l r. (l, r) \<in> R \<longrightarrow> (\<exists>f ts. l = Fun f ts) \<and> vars_term r \<subseteq> vars_term l"
  show "\<forall>l r. (l, r) \<in> map_funs_trs f R \<longrightarrow> (\<exists>f ts. l = Fun f ts) \<and> vars_term r \<subseteq> vars_term l"
  proof (intro allI impI)
    fix l r
    assume "(l, r) \<in> map_funs_trs f R"
    with ass
    show "(\<exists>f ts. l = Fun f ts) \<and> vars_term r \<subseteq> vars_term l"
      by (cases l, force+)
  qed
qed

lemma map_funs_trs_comp: "map_funs_trs fg (map_funs_trs gh R) = map_funs_trs (fg o gh) R"
proof -
  have mr: "map_funs_rule (fg o gh) = map_funs_rule fg o map_funs_rule gh"
    by (rule ext, auto simp: map_funs_term_comp)
  then show ?thesis
    by (auto simp: map_funs_term_comp image_comp mr)
qed

lemma map_funs_trs_mono: assumes "R \<subseteq> R'" shows "map_funs_trs fg R \<subseteq> map_funs_trs fg R'"
  using assms by auto

lemma map_funs_trs_power_mono:
  fixes R R' :: "('f,'v)trs" and fg :: "'f \<Rightarrow> 'f"
  assumes "R \<subseteq> R'" shows "((map_funs_trs fg)^^n) R \<subseteq> ((map_funs_trs fg)^^n) R'"
  using assms by (induct n, simp, auto)

declare map_funs_trs.simps[simp del]

lemma rstep_imp_map_rstep:
  assumes "(s, t) \<in> rstep R"
  shows "(map_funs_term fg s, map_funs_term fg t) \<in> rstep (map_funs_trs fg R)"
  using assms
proof (induct)
  case (IH C \<sigma> l r)
  then have "(map_funs_term fg l, map_funs_term fg r) \<in> map_funs_trs fg R" (is "(?l, ?r) \<in> ?R")
    unfolding map_funs_trs.simps by force
  then have "(?l, ?r) \<in> rstep ?R" ..
  then have "(?l \<cdot> map_funs_subst fg \<sigma>, ?r \<cdot> map_funs_subst fg \<sigma>) \<in> rstep ?R" ..
  then show ?case by auto
qed

lemma rsteps_imp_map_rsteps: assumes "(s,t) \<in> (rstep R)\<^sup>*"
  shows "(map_funs_term fg s, map_funs_term fg t) \<in> (rstep (map_funs_trs fg R))\<^sup>*"
  using assms
proof (induct, clarify)
  case (step y z)
  then have "(map_funs_term fg y, map_funs_term fg z) \<in> rstep (map_funs_trs fg R)" using rstep_imp_map_rstep
    by (auto simp: map_funs_trs.simps)
  with step show ?case by auto
qed

lemma SN_map_imp_SN:
  assumes SN: "SN_on (rstep (map_funs_trs fg R)) {map_funs_term fg t}"
  shows "SN_on (rstep R) {t}"
proof (rule ccontr)
  assume "\<not> SN_on (rstep R) {t}"
  from this obtain f where cond: "f 0 = t \<and> (\<forall> i. (f i, f (Suc i)) \<in> rstep R)"
    unfolding SN_on_def by auto
  obtain g where g: "g = (\<lambda> i. map_funs_term fg (f i))" by auto
  with cond have cond2: "g 0 = map_funs_term fg t \<and> (\<forall> i. (g i, g (Suc i)) \<in> rstep (map_funs_trs fg R))"
    using rstep_imp_map_rstep[where fg = fg] by blast
  from SN
  have "\<not> (\<exists> g. (g 0 = map_funs_term fg t \<and> (\<forall> i. (g i, g (Suc i)) \<in> rstep (map_funs_trs fg R))))"
    unfolding SN_on_def by auto
  with cond2 show False  by auto
qed

lemma rstep_iff_map_rstep:
  assumes "inj fg"
  shows "(s, t) \<in> rstep R \<longleftrightarrow> (map_funs_term fg s, map_funs_term fg t) \<in> rstep (map_funs_trs fg R)"
proof
  assume "(s,t) \<in> rstep R"
  then show "(map_funs_term fg s, map_funs_term fg t) \<in> rstep(map_funs_trs fg R)"
    by (rule rstep_imp_map_rstep)
next
  assume "(map_funs_term fg s, map_funs_term fg t) \<in> rstep (map_funs_trs fg R)"
  then have "(map_funs_term fg s, map_funs_term fg t) \<in> ctxt.closure(subst.closure(map_funs_trs fg R))"
    by (simp add: rstep_eq_closure)
  then obtain C u v where "(u,v) \<in> subst.closure(map_funs_trs fg R)" and "C\<langle>u\<rangle> = map_funs_term fg s"
    and "C\<langle>v\<rangle> = map_funs_term fg t"
    by (cases rule: ctxt.closure.cases) force
  then obtain \<sigma> w x where "(w,x) \<in> map_funs_trs fg R" and "w\<cdot>\<sigma> = u" and "x\<cdot>\<sigma> = v"
    by (cases rule: subst.closure.cases) force
  then obtain l r where "w = map_funs_term fg l" and "x = map_funs_term fg r"
    and "(l,r) \<in> R" by (auto simp: map_funs_trs.simps)
  have ps: "C\<langle>map_funs_term fg l \<cdot> \<sigma>\<rangle> = map_funs_term fg s" and pt: "C\<langle>map_funs_term fg r \<cdot> \<sigma>\<rangle> = map_funs_term fg t"
    unfolding \<open>w = map_funs_term fg l\<close>[symmetric] \<open>x = map_funs_term fg r\<close>[symmetric] \<open>w\<cdot>\<sigma> = u\<close> \<open>x\<cdot>\<sigma> = v\<close>
      \<open>C\<langle>u\<rangle> = map_funs_term fg s\<close> \<open>C\<langle>v\<rangle> = map_funs_term fg t\<close> by auto
  let ?gf = "the_inv fg"
  let ?C = "map_funs_ctxt ?gf C"
  let ?\<sigma> = "map_funs_subst ?gf \<sigma>"
  have gffg: "?gf \<circ> fg = id" using the_inv_f_f[OF assms] by (intro ext, auto)
  from ps and pt have "s = map_funs_term ?gf (C\<langle>map_funs_term fg l \<cdot> \<sigma>\<rangle>)"
    and "t = map_funs_term ?gf (C\<langle>map_funs_term fg r \<cdot> \<sigma>\<rangle>)" by (auto simp: map_funs_term_comp gffg)
  then have s: "s = ?C\<langle>map_funs_term ?gf (map_funs_term fg l \<cdot> \<sigma>)\<rangle>"
    and t: "t = ?C\<langle>map_funs_term ?gf (map_funs_term fg r \<cdot> \<sigma>)\<rangle>" using map_funs_term_ctxt_distrib by auto
  from s have "s = ?C\<langle>l\<cdot>?\<sigma>\<rangle>" by (simp add: map_funs_term_comp gffg)
  from t have "t = ?C\<langle>r\<cdot>?\<sigma>\<rangle>" by (simp add: map_funs_term_comp gffg)
  from \<open>(l, r) \<in> R\<close> have "(l\<cdot>?\<sigma>, r\<cdot>?\<sigma>) \<in> subst.closure R" by blast
  then have "(?C\<langle>l\<cdot>?\<sigma>\<rangle>,?C\<langle>r\<cdot>?\<sigma>\<rangle>) \<in> ctxt.closure(subst.closure R)" by blast
  then show "(s,t) \<in> rstep R" unfolding \<open>s = ?C\<langle>l\<cdot>?\<sigma>\<rangle>\<close> \<open>t = ?C\<langle>r\<cdot>?\<sigma>\<rangle>\<close> by (simp add: rstep_eq_closure)
qed

lemma rstep_map_funs_trs_power_mono:
  fixes R R' :: "('f,'v)trs" and fg :: "'f \<Rightarrow> 'f"
  assumes subset: "R \<subseteq> R'" shows "rstep (((map_funs_trs fg)^^n) R) \<subseteq> rstep (((map_funs_trs fg)^^n) R')"
  by (rule rstep_mono, rule map_funs_trs_power_mono, rule subset)

lemma subsetI3: "(\<And>x y z. (x, y, z) \<in> A \<Longrightarrow> (x, y, z) \<in> B) \<Longrightarrow> A \<subseteq> B" by auto

lemma aux: "(\<Union>a\<in>P. {(x,y,z). x = fst a \<and> y = snd a \<and> Q a z}) = {(x,y,z). (x,y) \<in> P \<and> Q (x,y) z}" (is "?P = ?Q")
proof
  show "?P \<subseteq> ?Q"
  proof
    fix x assume "x \<in> ?P"
    then obtain a where "a \<in> P" and "x \<in> {(x,y,z). x = fst a \<and> y = snd a \<and> Q a z}" by auto
    then obtain b where "Q (fst x, fst (snd x)) (snd (snd x))" and "(fst x, fst (snd x)) = a" and "snd (snd x) = b" by force
    from \<open>a \<in> P\<close> have "(fst a,snd a) \<in> P" unfolding split_def by simp
    from \<open>Q (fst x, fst (snd x)) (snd (snd x))\<close> have "Q a b" unfolding \<open>(fst x, fst (snd x)) = a\<close> \<open>snd (snd x) = b\<close> .
    from \<open>(fst a,snd a) \<in> P\<close> and \<open>Q a b\<close> show "x \<in> ?Q" unfolding split_def \<open>(fst x, fst (snd x)) = a\<close>[symmetric] \<open>snd (snd x) = b\<close>[symmetric] by simp
  qed
next
  show "?Q \<subseteq> ?P"
  proof (rule subsetI3)
    fix x y z assume "(x,y,z) \<in> ?Q"
    then have "(x,y) \<in> P" and "Q (x,y) z" by auto
    then have "x = fst(x,y) \<and> y = snd(x,y) \<and> Q (x,y) z" by auto
    then have "(x,y,z) \<in> {(x,y,z). x = fst(x,y) \<and> y = snd(x,y) \<and> Q (x,y) z}" by auto
    then have "\<exists>p\<in>P. (x,y,z) \<in> {(x,y,z). x = fst p \<and> y = snd p \<and> Q p z}" using \<open>(x,y) \<in> P\<close> by blast
    then show "(x,y,z) \<in> ?P" unfolding UN_iff[symmetric] by simp
  qed
qed

lemma finite_imp_finite_DP_on':
  assumes "finite R"
  shows "finite {(l, r, u).
    \<exists>h us. u = Fun h us \<and> (l, r) \<in> R \<and> r \<unrhd> u \<and> (h, length us) \<in> F \<and> \<not> (l \<rhd> u)}"
proof -
  have "\<And>l r. (l, r) \<in> R \<Longrightarrow> finite {u. r \<unrhd> u}"
  proof -
    fix l r
    assume "(l, r) \<in> R"
    show "finite {u. r \<unrhd> u}" by (rule finite_subterms)
  qed
  with \<open>finite R\<close> have "finite(\<Union>(l, r) \<in> R. {u. r \<unrhd> u})" by auto
  have "finite(\<Union>lr\<in>R. {(l, r, u). l = fst lr \<and> r = snd lr \<and> snd lr \<unrhd> u})"
  proof (rule finite_UN_I)
    show "finite R" by (rule \<open>finite R\<close>)
  next
    fix lr
    assume "lr \<in> R"
    have "finite {u. snd lr \<unrhd> u}" by (rule finite_subterms)
    then show "finite {(l,r,u). l = fst lr \<and> r = snd lr \<and> snd lr \<unrhd> u}" by auto
  qed
  then have "finite {(l,r,u). (l,r) \<in> R \<and> r \<unrhd> u}" unfolding aux by auto
  have "{(l,r,u). (l,r) \<in> R \<and> r \<unrhd> u} \<supseteq> {(l,r,u). (\<exists>h us. u = Fun h us \<and> (l,r) \<in> R \<and> r \<unrhd> u \<and> (h, length us) \<in> F \<and> \<not>(l \<rhd> u))}" by auto
  with \<open>finite {(l,r,u). (l,r) \<in> R \<and> r \<unrhd> u}\<close> show ?thesis using finite_subset by fast
qed

lemma card_image_le':
  assumes "finite S"
  shows "card (\<Union>y\<in>S.{x. x = f y}) \<le> card S"
proof -
  have A:"(\<Union>y\<in>S. {x. x = f y}) = f ` S" by auto
  from assms show ?thesis unfolding A using card_image_le by auto
qed

lemma subteq_of_map_imp_map: "map_funs_term g s \<unrhd> t \<Longrightarrow> \<exists>u. t = map_funs_term g u"
proof (induct s arbitrary: t)
  case (Var x)
  then have "map_funs_term g (Var x) \<rhd> t \<or> map_funs_term g (Var x) = t" by auto
  then show ?case
  proof
    assume "map_funs_term g (Var x) \<rhd> t" then show ?thesis by (cases rule: supt.cases) auto
  next
    assume "map_funs_term g (Var x) = t" then show ?thesis by best
  qed
next
  case (Fun f ss)
  then have "map_funs_term g (Fun f ss) \<rhd> t \<or> map_funs_term g (Fun f ss) = t" by auto
  then show ?case
  proof
    assume "map_funs_term g (Fun f ss) \<rhd> t"
    then show ?case using Fun by (cases rule: supt.cases) (auto simp: supt_supteq_conv)
  next
    assume "map_funs_term g (Fun f ss) = t" then show ?thesis by best
  qed
qed

lemma map_funs_term_inj:
  assumes "inj (fg :: ('f \<Rightarrow> 'g))"
  shows "inj (map_funs_term fg)"
proof -
  {
    fix s t :: "('f,'v)term"
    assume "map_funs_term fg s = map_funs_term fg t"
    then have "s = t"
    proof (induct s arbitrary: t)
      case (Var x) with assms show ?case by (induct t) auto
    next
      case (Fun f ss) then show ?case
      proof (induct t)
        case (Var y) then show ?case by auto
      next
        case (Fun g ts)
        then have A: "map (map_funs_term fg) ss = map (map_funs_term fg) ts" by simp
        then have len_eq:"length ss = length ts" by (rule map_eq_imp_length_eq)
        from A have "!!i. i < length ss \<Longrightarrow> (map (map_funs_term fg) ss)!i = (map (map_funs_term fg) ts)!i" by auto
        with len_eq have eq: "!!i. i < length ss \<Longrightarrow> map_funs_term fg  (ss!i) = map_funs_term fg (ts!i)" using nth_map by auto
        have in_set: "!!i. i < length ss \<Longrightarrow> (ss!i) \<in> set ss" by auto
        from Fun have "\<forall>i < length ss. (ss!i) = (ts!i)" using in_set eq by auto
        with len_eq have "ss = ts" using nth_equalityI[where xs = ss and ys = ts] by simp
        have "f = g" using Fun \<open>inj fg\<close> unfolding inj_on_def by auto
        with \<open>ss = ts\<close> show ?case by simp
      qed
    qed
  }
  then show ?thesis unfolding inj_on_def by auto
qed

lemma rsteps_closed_ctxt:
  assumes "(s, t) \<in> (rstep R)\<^sup>*"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (rstep R)\<^sup>*"
proof -
  from assms obtain n where "(s,t) \<in> (rstep R)^^n"
    using rtrancl_is_UN_relpow by auto
  then show ?thesis
  proof (induct n arbitrary: s)
    case 0 then show ?case by auto
  next
    case (Suc n)
    from relpow_Suc_D2[OF \<open>(s,t) \<in> (rstep R)^^Suc n\<close>] obtain u
      where "(s,u) \<in> (rstep R)" and "(u,t) \<in> (rstep R)^^n" by auto
    from \<open>(s,u) \<in> (rstep R)\<close> have "(C\<langle>s\<rangle>,C\<langle>u\<rangle>) \<in> (rstep R)" ..
    from Suc and \<open>(u,t) \<in> (rstep R)^^n\<close> have "(C\<langle>u\<rangle>,C\<langle>t\<rangle>) \<in> (rstep R)\<^sup>*" by simp
    with \<open>(C\<langle>s\<rangle>,C\<langle>u\<rangle>) \<in> (rstep R)\<close> show ?case by auto
  qed
qed

lemma one_imp_ctxt_closed: assumes one: "\<And> f bef s t aft. (s,t) \<in> r \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> r"
  shows "ctxt.closed r"
proof
  fix s t C
  assume st: "(s,t) \<in> r"
  show "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> r"
  proof (induct C)
    case (More f bef C aft)
    from one[OF More] show ?case by auto
  qed (insert st, auto)
qed

lemma ctxt_closed_nrrstep [intro]: "ctxt.closed (nrrstep R)"
proof (rule one_imp_ctxt_closed)
  fix f bef s t aft
  assume "(s,t) \<in> nrrstep R"
  from this[unfolded nrrstep_def'] obtain l r C \<sigma>
    where lr: "(l,r) \<in> R" and C: "C \<noteq> \<box>"
      and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> nrrstep R"
  proof (rule nrrstepI[OF lr])
    show "More f bef C aft \<noteq> \<box>" by simp
  qed (insert s t, auto)
qed

definition all_ctxt_closed :: "'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "all_ctxt_closed F r \<longleftrightarrow> (\<forall>f ts ss. (f, length ss) \<in> F \<longrightarrow> length ts = length ss \<longrightarrow>
    (\<forall>i. i < length ts \<longrightarrow> (ts ! i, ss ! i) \<in> r) \<longrightarrow> (\<forall> i. i < length ts \<longrightarrow> funas_term (ts ! i) \<union> funas_term (ss ! i) \<subseteq> F) \<longrightarrow> (Fun f ts, Fun f ss) \<in> r) \<and> (\<forall> x. (Var x, Var x) \<in> r)"

lemma all_ctxt_closedD: "all_ctxt_closed F r \<Longrightarrow> (f,length ss) \<in> F \<Longrightarrow> length ts = length ss
  \<Longrightarrow> \<lbrakk>\<And> i. i < length ts \<Longrightarrow> (ts ! i, ss ! i) \<in> r \<rbrakk>
  \<Longrightarrow> \<lbrakk>\<And> i. i < length ts \<Longrightarrow> funas_term (ts ! i) \<subseteq> F \<rbrakk>
  \<Longrightarrow> \<lbrakk>\<And> i. i < length ts \<Longrightarrow> funas_term (ss ! i) \<subseteq> F \<rbrakk>
  \<Longrightarrow> (Fun f ts, Fun f ss) \<in> r"
  unfolding all_ctxt_closed_def by auto

lemma all_ctxt_closed_sig_reflE: assumes all: "all_ctxt_closed F r"
  shows "funas_term t \<subseteq> F \<Longrightarrow> (t,t) \<in> r"
proof (induct t)
  case (Var x)
  from all[unfolded all_ctxt_closed_def] show ?case by auto
next
  case (Fun f ts)
  show ?case
    by (rule all_ctxt_closedD[OF all _ _ Fun(1)], insert Fun(2), force+)
qed

lemma all_ctxt_closed_reflE: assumes all: "all_ctxt_closed UNIV r"
  shows "(t,t) \<in> r"
  by (rule all_ctxt_closed_sig_reflE[OF all], auto)

lemma all_ctxt_closed_relcomp: assumes "all_ctxt_closed UNIV R" "all_ctxt_closed UNIV S"
  shows "all_ctxt_closed UNIV (R O S)"
  unfolding all_ctxt_closed_def
proof (intro allI impI conjI)
  show "(Var x, Var x) \<in> R O S" for x using assms unfolding all_ctxt_closed_def by auto
  fix f ts ss
  assume len: "length ts = length ss" 
    and steps: "\<forall>i<length ts. (ts ! i, ss ! i) \<in> R O S" 
  hence "\<forall> i. \<exists> us. i < length ts \<longrightarrow> (ts ! i, us) \<in> R \<and> (us, ss ! i) \<in> S" by blast
  from choice[OF this] obtain us where steps: "\<And> i. i<length ts \<Longrightarrow> (ts ! i, us i) \<in> R \<and> (us i, ss ! i) \<in> S" 
    by blast
  let ?us = "map us [0..<length ss]" 
  from all_ctxt_closedD[OF assms(2)] steps len have us: "(Fun f ?us, Fun f ss) \<in> S" by auto
  from all_ctxt_closedD[OF assms(1)] steps len have tu: "(Fun f ts, Fun f ?us) \<in> R" by force
  from tu us 
  show "(Fun f ts, Fun f ss) \<in> R O S" by auto
qed

lemma all_ctxt_closed_relpow:
  assumes acc:"all_ctxt_closed UNIV Q"
  shows "all_ctxt_closed UNIV (Q ^^ n)"
proof (induct n)
  case 0
  thus ?case by (auto simp: all_ctxt_closed_def nth_equalityI)
next
  case (Suc n)
  from all_ctxt_closed_relcomp[OF this acc]
  show ?case by simp
qed


lemma all_ctxt_closed_subst_step_sig:
  fixes r :: "('f, 'v) trs" and t :: "('f, 'v) term"
  assumes all: "all_ctxt_closed F r"
    and sig: "funas_term t \<subseteq> F"
    and steps: "\<And> x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> r"
    and sig_subst: "\<And> x. x \<in> vars_term t \<Longrightarrow> funas_term (\<sigma> x) \<union> funas_term (\<tau> x) \<subseteq> F"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> r"
  using sig steps sig_subst
proof (induct t)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ts)
  {
    fix t
    assume t: "t \<in> set ts"
    with Fun(2-3) have "funas_term t \<subseteq> F" "\<And> x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> r" by auto
    from Fun(1)[OF t this Fun(4)] t have step: "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> r" by auto
    from Fun(4) t have "\<And> x. x \<in> vars_term t \<Longrightarrow> funas_term (\<sigma> x) \<union> funas_term (\<tau> x) \<subseteq> F" by auto
    with \<open>funas_term t \<subseteq> F\<close> have "funas_term (t \<cdot> \<sigma>) \<union> funas_term (t \<cdot> \<tau>) \<subseteq> F" unfolding funas_term_subst by auto
    note step this
  }
  then have steps: "\<And> i. i < length ts \<Longrightarrow> (ts ! i \<cdot> \<sigma>, ts ! i \<cdot> \<tau>) \<in> r \<and> funas_term (ts ! i \<cdot> \<sigma>) \<union> funas_term (ts ! i \<cdot> \<tau>) \<subseteq> F" unfolding set_conv_nth by auto
  with all_ctxt_closedD[OF all, of f "map (\<lambda> t. t \<cdot> \<tau>) ts" "map (\<lambda> t. t \<cdot> \<sigma>) ts"] Fun(2)
  show ?case by auto
qed

lemma all_ctxt_closed_subst_step:
  fixes r :: "('f, 'v) trs" and t :: "('f, 'v) term"
  assumes all: "all_ctxt_closed UNIV r"
    and steps: "\<And> x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> r"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> r"
  by (rule all_ctxt_closed_subst_step_sig[OF all _ steps], auto)

lemma all_ctxt_closed_ctxtE: assumes all: "all_ctxt_closed F R"
  and Fs: "funas_term s \<subseteq> F"
  and Ft: "funas_term t \<subseteq> F"
  and step: "(s,t) \<in> R"
shows "funas_ctxt C \<subseteq> F \<Longrightarrow> (C \<langle> s \<rangle>, C \<langle> t \<rangle>) \<in> R"
proof(induct C)
  case Hole
  from step show ?case by auto
next
  case (More f bef C aft)
  let ?n = "length bef"
  let ?m = "Suc (?n + length aft)"
  show ?case unfolding intp_actxt.simps
  proof (rule all_ctxt_closedD[OF all])
    fix i
    let ?t = "\<lambda> s. (bef @ C \<langle> s \<rangle> # aft) ! i"
    assume "i < length (bef @ C\<langle>s\<rangle> # aft)"
    then have i: "i < ?m" by auto
    then have mem: "\<And> s. ?t s \<in> set (bef @ C \<langle> s \<rangle> # aft)" unfolding set_conv_nth by auto
    from mem[of s] More Fs show "funas_term (?t s) \<subseteq> F" by auto
    from mem[of t] More Ft show "funas_term (?t t) \<subseteq> F" by auto
    from More have step: "(C \<langle> s \<rangle>, C \<langle> t \<rangle>) \<in> R" by auto
    {
      fix s
      assume "s \<in> set bef \<union> set aft"
      with More have "funas_term s \<subseteq> F" by auto
      from all_ctxt_closed_sig_reflE[OF all this] have "(s,s) \<in> R" by auto
    } note steps = this
    show "(?t s, ?t t) \<in> R"
    proof (cases "i = ?n")
      case True
      then show ?thesis using step by auto
    next
      case False
      show ?thesis
      proof (cases "i < ?n")
        case True
        then show ?thesis unfolding append_Cons_nth_left[OF True] using steps by auto
      next
        case False
        with \<open>i \<noteq> ?n\<close> i have "\<exists> k. k < length aft \<and> i = Suc ?n + k" by presburger
        then obtain k where k: "k < length aft" and i: "i = Suc ?n + k" by auto
        from k show ?thesis using steps unfolding i by (auto simp: nth_append)
      qed
    qed
  qed (insert More, auto)
qed

lemma trans_ctxt_sig_imp_all_ctxt_closed: assumes tran: "trans r"
  and refl: "\<And> t. funas_term t \<subseteq> F \<Longrightarrow> (t,t) \<in> r"
  and ctxt: "\<And> C s t. funas_ctxt C \<subseteq> F \<Longrightarrow> funas_term s \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow> (s,t) \<in> r \<Longrightarrow> (C \<langle> s \<rangle>, C \<langle> t \<rangle>) \<in> r"
shows "all_ctxt_closed F r"
  unfolding all_ctxt_closed_def
proof (intro conjI, intro allI impI)
  fix f ts ss
  assume f: "(f,length ss) \<in> F" and
    l: "length ts = length ss" and
    steps: "\<forall> i < length ts. (ts ! i, ss ! i) \<in> r" and
    sig: "\<forall> i < length ts. funas_term (ts ! i) \<union>  funas_term (ss ! i) \<subseteq> F"
  from sig have sig_ts: "\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F"  unfolding set_conv_nth by auto
  let ?p = "\<lambda> ss. (Fun f ts, Fun f ss) \<in> r \<and> funas_term (Fun f ss) \<subseteq> F"
  let ?r = "\<lambda> xsi ysi. (xsi, ysi) \<in> r \<and> funas_term ysi \<subseteq> F"
  have init: "?p ts" by (rule conjI[OF refl], insert f sig_ts l, auto)
  have "?p ss"
  proof (rule parallel_list_update[where p = ?p and r = ?r, OF _ HOL.refl init l[symmetric]])
    fix xs i y
    assume len: "length xs = length ts"
      and i: "i < length ts"
      and r: "?r (xs ! i) y"
      and p: "?p xs"
    let ?C = "More f (take i xs) Hole (drop (Suc i) xs)"
    have id1: "Fun f xs = ?C \<langle> xs ! i\<rangle>" using id_take_nth_drop[OF i[folded len]] by simp
    have id2: "Fun f (xs[i := y]) = ?C \<langle> y \<rangle>" using upd_conv_take_nth_drop[OF i[folded len]] by simp
    from p[unfolded id1] have C: "funas_ctxt ?C \<subseteq> F" and xi: "funas_term (xs ! i) \<subseteq> F" by auto
    from r have "funas_term y \<subseteq> F" "(xs ! i, y) \<in> r" by auto
    with ctxt[OF C xi this] C have r: "(Fun f xs, Fun f (xs[i := y])) \<in> r"
      and f: "funas_term (Fun f (xs[i := y])) \<subseteq> F" unfolding id1 id2 by auto
    from p r tran have "(Fun f ts, Fun f (xs[i := y])) \<in> r" unfolding trans_def by auto
    with f
    show "?p (xs[i := y])"  by auto
  qed (insert sig steps, auto)
  then show "(Fun f ts, Fun f ss) \<in> r" ..
qed (insert refl, auto)

lemma trans_ctxt_imp_all_ctxt_closed: assumes tran: "trans r"
  and refl: "refl r"
  and ctxt: "ctxt.closed r"
shows "all_ctxt_closed F r"
  by (rule trans_ctxt_sig_imp_all_ctxt_closed[OF tran _ ctxt.closedD[OF ctxt]], insert refl[unfolded refl_on_def], auto)

lemma all_ctxt_closed_rsteps[intro]: "all_ctxt_closed F ((rstep r)\<^sup>*)"
  by (blast intro: trans_ctxt_imp_all_ctxt_closed trans_rtrancl refl_rtrancl)

lemma subst_rsteps_imp_rsteps:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "\<And> x. x\<in>vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> (rstep R)\<^sup>*"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  by (rule all_ctxt_closed_subst_step)
    (insert assms, auto)

lemma rtrancl_trancl_into_trancl:
  assumes len: "length ts = length ss"
    and steps: "\<forall> i < length ts. (ts ! i, ss ! i) \<in> R\<^sup>*"
    and i: "i < length ts"
    and step: "(ts ! i, ss ! i) \<in> R\<^sup>+"
    and ctxt: "ctxt.closed R"
  shows "(Fun f ts, Fun f ss) \<in> R\<^sup>+"
proof -
  from ctxt have ctxt_rt: "ctxt.closed (R\<^sup>*)" by blast
  from ctxt have ctxt_t: "ctxt.closed (R\<^sup>+)" by blast
  from id_take_nth_drop[OF i] have ts: "ts = take i ts @ ts ! i # drop (Suc i) ts" (is "_ = ?ts") by auto
  from id_take_nth_drop[OF i[simplified len]] have ss: "ss = take i ss @ ss ! i # drop (Suc i) ss" (is "_ = ?ss") by auto
  let ?mid = "take i ss @ ts ! i # drop (Suc i) ss"
  from trans_ctxt_imp_all_ctxt_closed[OF trans_rtrancl refl_rtrancl ctxt_rt] have all: "all_ctxt_closed UNIV (R\<^sup>*)" .
  from ctxt_closed_one[OF ctxt_t step] have "(Fun f ?mid, Fun f ?ss) \<in> R\<^sup>+" .
  then have part1: "(Fun f ?mid, Fun f ss) \<in> R\<^sup>+" unfolding ss[symmetric] .
  from ts have lents: "length ts =  length ?ts" by simp
  have "(Fun f ts, Fun f ?mid) \<in> R\<^sup>*"
  proof (rule all_ctxt_closedD[OF all])
    fix j
    assume jts: "j < length ts"
    from i len have i: "i < length ss" by auto
    show "(ts ! j, ?mid ! j) \<in> R\<^sup>*"
    proof (cases "j < i")
      case True
      with i have j: "j < length ss" by auto
      with True have id: "?mid ! j = ss ! j" by (simp add: nth_append)
      from steps len j have "(ts ! j, ss ! j) \<in> R\<^sup>*" by auto
      then show ?thesis using id by simp
    next
      case False
      show ?thesis
      proof (cases "j = i")
        case True
        then have "?mid ! j = ts ! j" using i by (simp add: nth_append)
        then show ?thesis by simp
      next
        case False
        from i have min: "min (length ss) i = i" by simp
        from False \<open>\<not> j < i\<close> have "j > i" by arith
        then obtain k where k: "j - i = Suc k" by (cases "j - i", auto)
        then have j: "j = Suc (i+k)" by auto
        with jts len have ss: "Suc i + k \<le> length ss" and jlen: "j < length ts" by auto
        then have "?mid ! j = ss ! j" using j i by (simp add: nth_append min \<open>\<not> j < i\<close> nth_drop[OF ss])
        with steps jlen show ?thesis by auto
      qed
    qed
  qed (insert lents[symmetric] len, auto)
  with part1 show ?thesis by auto
qed

lemma SN_ctxt_apply_imp_SN_ctxt_to_term_list_gen:
  assumes ctxt: "ctxt.closed r"
  assumes SN: "SN_on r {C\<langle>t\<rangle>}"
  shows "SN_on r (set (ctxt_to_term_list C))"
proof -
  {
    fix u
    assume "u \<in> set (ctxt_to_term_list C)"
    from ctxt_to_term_list_supt[OF this, of t] have "C\<langle>t\<rangle> \<unrhd> u"
      by (rule supt_imp_supteq)
    from ctxt_closed_SN_on_subt[OF ctxt, OF SN this]
    have "SN_on r {u}" by auto
  }
  then show ?thesis
    unfolding SN_on_def by auto
qed

lemma rstep_subset: "ctxt.closed R' \<Longrightarrow> subst.closed R' \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> rstep R \<subseteq> R'" by fast

lemma trancl_rstep_ctxt:
  "(s,t) \<in> (rstep R)\<^sup>+ \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (rstep R)\<^sup>+"
  by (rule ctxt.closedD, blast)

lemma args_steps_imp_steps_gen:
  assumes ctxt: "\<And> bef s t aft. (s, t) \<in> r (length bef) \<Longrightarrow>
    length ts = Suc (length bef + length aft) \<Longrightarrow>
    (Fun f (bef @ (s :: ('f, 'v) term) # aft), Fun f (bef @ t # aft)) \<in> R\<^sup>*"
    and len: "length ss = length ts"
    and args: "\<And> i. i < length ts \<Longrightarrow> (ss ! i, ts ! i) \<in> (r i)\<^sup>*"
  shows "(Fun f ss, Fun f ts) \<in> R\<^sup>*"
proof -
  let ?tss = "\<lambda>i. take i ts @ drop i ss"
  {
    fix bef :: "('f,'v)term list" and s t and  aft :: "('f,'v)term list"
    assume "(s,t) \<in> (r (length bef))\<^sup>*" and len: "length ts = Suc (length bef + length aft)"
    then have "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> R\<^sup>*"
    proof (induct)
      case (step t u)
      from step(3)[OF len] ctxt[OF step(2) len] show ?case by auto
    qed simp
  }
  note one = this
  have a:"\<forall>i \<le> length ts. (Fun f ss,Fun f (?tss i)) \<in> R\<^sup>*"
  proof (intro allI impI)
    fix i assume "i \<le> length ts" then show "(Fun f ss,Fun f (?tss i)) \<in> R\<^sup>*"
    proof (induct i)
      case 0
      then show ?case by simp
    next
      case (Suc i)
      then have IH: "(Fun f ss,Fun f (?tss i)) \<in> R\<^sup>*"
        and i: "i < length ts" by auto
      have si: "?tss (Suc i) = take i ts @ ts ! i # drop (Suc i) ss"
        unfolding take_Suc_conv_app_nth[OF i] by simp
      have ii: "?tss i = take i ts @ ss ! i # drop (Suc i) ss"
        unfolding Cons_nth_drop_Suc[OF i[unfolded len[symmetric]]] ..
      from i have i': "length (take i ts) < length ts"  and len': "length (take i ts) = i" by auto
      from len i have len'': "length ts = Suc (length (take i ts) + length (drop (Suc i) ss))" by simp
      from one[OF args[OF i'] len''] IH
      show ?case unfolding si ii len' by auto
    qed
  qed
  from this[THEN spec, THEN mp[OF _ le_refl]]
  show ?thesis using len by auto
qed

lemma args_steps_imp_steps:
  assumes ctxt: "ctxt.closed R"
    and len: "length ss = length ts" and args: "\<forall>i<length ss. (ss!i, ts!i) \<in> R\<^sup>*"
  shows "(Fun f ss, Fun f ts) \<in> R\<^sup>*"
proof (rule args_steps_imp_steps_gen[OF _ len])
  fix i
  assume "i < length ts" then show "(ss ! i, ts ! i) \<in> R\<^sup>*" using args len by auto
qed (insert ctxt_closed_one[OF ctxt], auto)

lemmas args_rsteps_imp_rsteps = args_steps_imp_steps [OF ctxt_closed_rstep]

lemma replace_at_subst_steps:
  fixes \<sigma> \<tau> :: "('f, 'v) subst"
  assumes acc: "all_ctxt_closed UNIV r"
    and refl: "refl r"
    and *: "\<And>x. (\<sigma> x, \<tau> x) \<in> r"
    and "p \<in> poss t"
    and "t |_ p = Var x"
  shows "(replace_at (t \<cdot> \<sigma>) p (\<tau> x), t \<cdot> \<tau>) \<in> r"
  using assms(4-)
proof (induction t arbitrary: p)
  case (Var x)
  then show ?case using refl by (simp add: refl_on_def)
next
  case (Fun f ts)
  then obtain i q where [simp]: "p = i # q" and i: "i < length ts"
    and q: "q \<in> poss (ts ! i)" and [simp]: "ts ! i |_ q = Var x" by (cases p) auto
  let ?C = "ctxt_of_pos_term q (ts ! i \<cdot> \<sigma>)"
  let ?ts = "map (\<lambda>t. t \<cdot> \<tau>) ts"
  let ?ss = "take i (map (\<lambda>t. t \<cdot> \<sigma>) ts) @ ?C\<langle>\<tau> x\<rangle> # drop (Suc i) (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
  have "\<forall>j<length ts. (?ss ! j, ?ts ! j) \<in> r"
  proof (intro allI impI)
    fix j
    assume j: "j < length ts"
    moreover
    { assume [simp]: "j = i"
      have "?ss ! j = ?C\<langle>\<tau> x\<rangle>" using i by (simp add: nth_append_take)
      with Fun.IH [of "ts ! i" q]
      have "(?ss ! j, ?ts ! j) \<in> r" using q and i by simp }
    moreover
    { assume "j < i"
      with i have "?ss ! j = ts ! j \<cdot> \<sigma>"
        and "?ts ! j = ts ! j \<cdot> \<tau>" by (simp_all add: nth_append_take_is_nth_conv)
      then have "(?ss ! j, ?ts ! j) \<in> r" by (auto simp: * all_ctxt_closed_subst_step [OF acc]) }
    moreover
    { assume "j > i"
      with i and j have "?ss ! j = ts ! j \<cdot> \<sigma>"
        and "?ts ! j = ts ! j \<cdot> \<tau>" by (simp_all add: nth_append_drop_is_nth_conv)
      then have "(?ss ! j, ?ts ! j) \<in> r" by (auto simp: * all_ctxt_closed_subst_step [OF acc]) }
    ultimately show "(?ss ! j, ?ts ! j) \<in> r" by arith
  qed
  moreover have "i < length ts" by fact
  ultimately show ?case
    by (auto intro: all_ctxt_closedD [OF acc])
qed

lemma replace_at_subst_rsteps:
  fixes \<sigma> \<tau> :: "('f, 'v) subst"
  assumes *: "\<And>x. (\<sigma> x, \<tau> x) \<in> (rstep R)\<^sup>*"
    and "p \<in> poss t"
    and "t |_ p = Var x"
  shows "(replace_at (t \<cdot> \<sigma>) p (\<tau> x), t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  by (intro replace_at_subst_steps[OF _ _ assms], auto simp: refl_on_def)

lemma substs_rsteps:
  assumes "\<And>x. (\<sigma> x, \<tau> x) \<in> (rstep R)\<^sup>*"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
proof (induct t)
  case (Var y)
  show ?case using assms by simp_all
next
  case (Fun f ts)
  then have "\<forall>i<length (map (\<lambda>t. t \<cdot> \<sigma>) ts).
    (map (\<lambda>t. t \<cdot> \<sigma> ) ts ! i, map (\<lambda>t. t \<cdot> \<tau>) ts ! i) \<in> (rstep R)\<^sup>*" by auto
  from args_rsteps_imp_rsteps [OF _ this] show ?case by simp
qed

lemma nrrstep_Fun_imp_arg_rstep:
  fixes ss :: "('f,'v)term list"
  assumes "(Fun f ss,Fun f ts) \<in> nrrstep R" (is "(?s,?t) \<in> nrrstep R")
  shows "\<exists>C i. i < length ss \<and> (ss!i,ts!i) \<in> rstep R \<and> C\<langle>ss!i\<rangle> = Fun f ss \<and> C\<langle>ts!i\<rangle> = Fun f ts"
proof -
  from \<open>(?s,?t) \<in> nrrstep R\<close>
  obtain l r j ps \<sigma> where A: "let C = ctxt_of_pos_term (j#ps) ?s in (j#ps) \<in> poss ?s \<and> (l,r) \<in> R \<and> C\<langle>l\<cdot>\<sigma>\<rangle> = ?s \<and> C\<langle>r\<cdot>\<sigma>\<rangle> = ?t" unfolding nrrstep_def rstep_r_p_s_def by force
  let ?C = "ctxt_of_pos_term (j#ps) ?s"
  from A have "(j#ps) \<in> poss ?s" and "(l,r) \<in> R" and "?C\<langle>l\<cdot>\<sigma>\<rangle> = ?s" and "?C\<langle>r\<cdot>\<sigma>\<rangle> = ?t" using Let_def by auto
  have C: "?C = More f (take j ss) (ctxt_of_pos_term ps (ss!j)) (drop (Suc j) ss)" (is "?C = More f ?ss1 ?D ?ss2") by auto
  from \<open>?C\<langle>l\<cdot>\<sigma>\<rangle> = ?s\<close> have "?D\<langle>l\<cdot>\<sigma>\<rangle> = (ss!j)" by (auto simp: take_drop_imp_nth)
  from \<open>(l,r) \<in> R\<close> have "(l\<cdot>\<sigma>,r\<cdot>\<sigma>) \<in> (subst.closure R)" by auto
  then have "(?D\<langle>l\<cdot>\<sigma>\<rangle>,?D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> (ctxt.closure(subst.closure R))" and "(?C\<langle>l\<cdot>\<sigma>\<rangle>,?C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> (ctxt.closure(subst.closure R))" by (auto simp only: ctxt.closure.intros)
  then have D_rstep: "(?D\<langle>l\<cdot>\<sigma>\<rangle>,?D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R" and "(?C\<langle>l\<cdot>\<sigma>\<rangle>,?C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R"
    by (auto simp: rstep_eq_closure)
  from \<open>?C\<langle>r\<cdot>\<sigma>\<rangle> = ?t\<close> and C have "?t = Fun f (take j ss @ ?D\<langle>r\<cdot>\<sigma>\<rangle> # drop (Suc j) ss)" by auto
  then have ts: "ts = (take j ss @ ?D\<langle>r\<cdot>\<sigma>\<rangle> # drop (Suc j) ss)" by auto
  from \<open>j#ps \<in> poss ?s\<close> have r0: "j < length ss" by simp
  then have "(take j ss @ ?D\<langle>r\<cdot>\<sigma>\<rangle> # drop (Suc j) ss) ! j = ?D\<langle>r\<cdot>\<sigma>\<rangle>" by (auto simp: nth_append_take)
  with ts have "ts!j = ?D\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  let ?C' = "More f (take j ss) \<box> (drop (Suc j) ss)"
  from D_rstep have r1: "(ss!j,ts!j) \<in> rstep R" unfolding \<open>ts!j = ?D\<langle>r\<cdot>\<sigma>\<rangle>\<close> \<open>?D\<langle>l\<cdot>\<sigma>\<rangle> = ss!j\<close> by simp
  have "?s = ?C\<langle>l\<cdot>\<sigma>\<rangle>" unfolding \<open>?C\<langle>l\<cdot>\<sigma>\<rangle> = ?s\<close> by simp
  also have "\<dots> = ?C'\<langle>?D\<langle>l\<cdot>\<sigma>\<rangle>\<rangle>" unfolding C by simp
  finally have r2:"?C'\<langle>ss!j\<rangle> = ?s" unfolding \<open>?D\<langle>l\<cdot>\<sigma>\<rangle> = ss!j\<close> by simp
  have "?t = ?C\<langle>r\<cdot>\<sigma>\<rangle>" unfolding \<open>?C\<langle>r\<cdot>\<sigma>\<rangle> = ?t\<close> by simp
  also have "\<dots> = ?C'\<langle>?D\<langle>r\<cdot>\<sigma>\<rangle>\<rangle>" unfolding C by simp
  finally have r3:"?C'\<langle>ts!j\<rangle> = ?t" unfolding \<open>ts!j = ?D\<langle>r\<cdot>\<sigma>\<rangle>\<close> by simp
  from r0 r1 r2 r3 show ?thesis by best
qed

lemma pair_fun_eq[simp]:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
  shows "((\<lambda>(x,y). (x,f y)) \<circ> (\<lambda>(x,y). (x,g y))) = (\<lambda>(x,y). (x,(f \<circ> g) y))" (is "?f = ?g")
proof (rule ext)
  fix ab :: "'c * 'b"
  obtain a b where "ab = (a,b)" by force
  have "((\<lambda>(x,y). (x,f y))\<circ>(\<lambda>(x,y). (x,g y))) (a,b) = (\<lambda>(x,y). (x,(f\<circ>g) y)) (a,b)" by simp
  then show "?f ab = ?g ab" unfolding \<open>ab = (a,b)\<close> by simp
qed

lemma restrict_singleton:
  assumes "x \<in> subst_domain \<sigma>" shows "\<exists>t. \<sigma> |s {x} = (\<lambda>y. if y = x then t else Var y)"
proof -
  have "\<sigma> |s {x} = (\<lambda>y. if y = x then \<sigma> y else Var y)" by (simp add: subst_restrict_def)
  then have "\<sigma> |s {x} = (\<lambda>y. if y = x then \<sigma> x else Var y)" by (simp cong: if_cong)
  then show ?thesis by (rule exI[of _ "\<sigma> x"])
qed

definition rstep_r_c_s :: "('f,'v)rule \<Rightarrow> ('f,'v)ctxt \<Rightarrow> ('f,'v)subst \<Rightarrow> ('f,'v)term rel"
  where "rstep_r_c_s r C \<sigma> = {(s,t) | s t. s = C\<langle>fst r \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>snd r \<cdot> \<sigma>\<rangle>}"

lemma rstep_iff_rstep_r_c_s: "((s,t) \<in> rstep R) = (\<exists> l r C \<sigma>. (l,r) \<in> R \<and> (s,t) \<in> rstep_r_c_s (l,r) C \<sigma>)" (is "?left = ?right")
proof
  assume ?left
  then obtain l r p \<sigma> where step: "(s,t) \<in> rstep_r_p_s R (l,r) p \<sigma>"
    unfolding rstep_iff_rstep_r_p_s by blast
  obtain D where D: "D = ctxt_of_pos_term p s" by auto
  with step have Rrule: "(l,r) \<in> R" and s: "s = D\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = D\<langle>r \<cdot> \<sigma>\<rangle>"
    unfolding rstep_r_p_s_def by (force simp: Let_def)+
  then show ?right unfolding rstep_r_c_s_def by auto
next
  assume ?right
  from this obtain l r C \<sigma> where "(l,r) \<in> R \<and> (s,t) \<in> rstep_r_c_s (l,r) C \<sigma>" by auto
  then have rule: "(l,r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    unfolding rstep_r_c_s_def by auto
  show ?left unfolding rstep_eq_closure by (auto simp: s t intro: rule)
qed

lemma rstep_subset_characterization:
  "(rstep R \<subseteq> rstep S) = (\<forall> l r. (l,r) \<in> R \<longrightarrow> (\<exists> l' r' C \<sigma> . (l',r') \<in> S \<and> l = C\<langle>l' \<cdot> \<sigma>\<rangle> \<and> r = C\<langle>r' \<cdot> \<sigma>\<rangle>))" (is "?left = ?right")
proof
  assume ?right
  show ?left
  proof 
    fix s t
    assume "(s,t) \<in> rstep R"
    then obtain l r C \<sigma> where step: "(l,r) \<in> R \<and> (s,t) \<in> rstep_r_c_s (l,r) C \<sigma>"
      unfolding rstep_iff_rstep_r_c_s by best
    then have Rrule: "(l,r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      unfolding rstep_r_c_s_def by (force)+
    from Rrule \<open>?right\<close> obtain l' r' C' \<sigma>' where Srule: "(l',r') \<in> S" and l: "l = C'\<langle>l' \<cdot> \<sigma>'\<rangle>" and r: "r = C'\<langle>r' \<cdot> \<sigma>'\<rangle>"
      by (force simp: Let_def)+
    let ?D = "C \<circ>\<^sub>c (C' \<cdot>\<^sub>c \<sigma>)"
    let ?sig = "\<sigma>' \<circ>\<^sub>s \<sigma>"
    have s2: "s = ?D\<langle>l' \<cdot> ?sig\<rangle>" by (simp add: s l)
    have t2: "t = ?D\<langle>r' \<cdot> ?sig\<rangle>" by (simp add: t r)
    from s2 t2 have sStep: "(s,t) \<in> rstep_r_c_s (l',r') ?D ?sig" unfolding rstep_r_c_s_def by force
    with Srule show "(s,t) \<in> rstep S" by (simp only: rstep_iff_rstep_r_c_s, blast)
  qed
next
  assume ?left
  show ?right
  proof (rule ccontr)
    assume "\<not> ?right"
    from this obtain l r where "(l,r) \<in> R" and cond: "\<forall> l' r' C \<sigma>. (l',r') \<in> S \<longrightarrow> (l \<noteq> C\<langle>l' \<cdot> \<sigma>\<rangle> \<or> r \<noteq> C\<langle>r' \<cdot> \<sigma>\<rangle>)" by blast
    then have "(l,r) \<in> rstep R" by blast
    with \<open>?left\<close> have "(l,r) \<in> rstep S" by auto
    with cond show False by (simp only: rstep_iff_rstep_r_c_s, unfold rstep_r_c_s_def, force)
  qed
qed

lemma rstep_preserves_funas_terms_var_cond:
  assumes "funas_trs R \<subseteq> F" and "funas_term s \<subseteq> F" and "(s,t) \<in> rstep R"
    and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "funas_term t \<subseteq> F"
proof -
  from \<open>(s,t) \<in> rstep R\<close> obtain l r C \<sigma> where R: "(l,r) \<in> R"
    and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  from \<open>funas_trs R \<subseteq> F\<close> and R have "funas_term r \<subseteq> F"
    unfolding funas_defs [abs_def] by force
  with wf[OF R] \<open>funas_term s \<subseteq> F\<close> show ?thesis unfolding s t by (force simp: funas_term_subst)
qed

lemma rstep_preserves_funas_terms:
  assumes "funas_trs R \<subseteq> F" and "funas_term s \<subseteq> F" and "(s,t) \<in> rstep R"
    and wf: "wf_trs R"
  shows "funas_term t \<subseteq> F"
  by (rule rstep_preserves_funas_terms_var_cond[OF assms(1-3)], insert wf[unfolded wf_trs_def], auto)

lemma rsteps_preserve_funas_terms_var_cond:
  assumes F: "funas_trs R \<subseteq> F" and s: "funas_term s \<subseteq> F" and steps: "(s,t) \<in> (rstep R)\<^sup>*"
    and wf: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "funas_term t \<subseteq> F"
  using steps
proof (induct)
  case base then show ?case by (rule s)
next
  case (step t u)
  show ?case by (rule rstep_preserves_funas_terms_var_cond[OF F step(3) step(2) wf])
qed

lemma rsteps_preserve_funas_terms:
  assumes F: "funas_trs R \<subseteq> F" and s: "funas_term s \<subseteq> F"
    and steps: "(s,t) \<in> (rstep R)\<^sup>*" and wf: "wf_trs R"
  shows "funas_term t \<subseteq> F"
  by (rule rsteps_preserve_funas_terms_var_cond[OF assms(1-3)], insert wf[unfolded wf_trs_def], auto)

lemma no_Var_rstep [simp]:
  assumes "wf_trs R" and "(Var x, t) \<in> rstep R" shows "False"
  using rstep_imp_Fun[OF assms] by auto

lemma lhs_wf:
  assumes R: "(l, r) \<in> R" and "funas_trs R \<subseteq> F"
  shows "funas_term l \<subseteq>  F"
  using assms by (force simp: funas_trs_def funas_rule_def)

lemma rhs_wf:
  assumes R: "(l, r) \<in> R" and "funas_trs R \<subseteq> F"
  shows "funas_term r \<subseteq> F"
  using assms by (force simp: funas_trs_def funas_rule_def)

lemma supt_map_funs_term [intro]:
  assumes "t \<rhd> s"
  shows "map_funs_term fg t \<rhd> map_funs_term fg s"
  using assms
proof (induct)
  case (arg s ss f)
  then have "map_funs_term fg s \<in> set(map (map_funs_term fg) ss)" by simp
  then show ?case unfolding term.map by (rule supt.arg)
next
  case (subt s ss u f)
  then have "map_funs_term fg s \<in> set(map (map_funs_term fg) ss)" by simp
  with \<open>map_funs_term fg s \<rhd> map_funs_term fg u\<close> show ?case
    unfolding term.map by (metis supt.subt)
qed

lemma nondef_root_imp_arg_step:
  assumes "(Fun f ss, t) \<in> rstep R"
    and wf: "\<forall>(l, r)\<in>R. is_Fun l"
    and ndef: "\<not> defined R (f, length ss)"
  shows "\<exists>i<length ss. (ss ! i, t |_ [i]) \<in> rstep R
    \<and> t = Fun f (take i ss @ (t |_ [i]) # drop (Suc i) ss)"
proof -
  from assms obtain l r p \<sigma>
    where rstep_r_p_s: "(Fun f ss, t) \<in> rstep_r_p_s R (l, r) p \<sigma>"
    unfolding rstep_iff_rstep_r_p_s by auto
  let ?C = "ctxt_of_pos_term p (Fun f ss)"
  from rstep_r_p_s have "p \<in> poss (Fun f ss)" and "(l, r) \<in> R"
    and "?C\<langle>l \<cdot> \<sigma>\<rangle> = Fun f ss" and "?C\<langle>r \<cdot> \<sigma>\<rangle> = t" unfolding rstep_r_p_s_def Let_def by auto
  have "\<exists>i q. p = i#q"
  proof (cases p)
    case Cons then show ?thesis by auto
  next
    case Nil
    have "?C = \<box>" unfolding Nil by simp
    with \<open>?C\<langle>l\<cdot>\<sigma>\<rangle> = Fun f ss\<close> have "l\<cdot>\<sigma> = Fun f ss" by simp
    have "\<forall>(l,r)\<in>R. \<exists>f ss. l = Fun f ss"
    proof (intro ballI impI)
      fix lr assume "lr \<in> R"
      with wf have "\<forall>x. fst lr \<noteq> Var x" by auto
      then have "\<exists>f ss. (fst lr) = Fun f ss" by (cases "fst lr") auto
      then show "(\<lambda>(l,r). \<exists>f ss. l = Fun f ss) lr" by auto
    qed
    with \<open>(l,r) \<in> R\<close> obtain g ts where "l = Fun g ts" unfolding wf_trs_def by best
    with \<open>l\<cdot>\<sigma> = Fun f ss\<close> \<open>l = Fun g ts\<close> and \<open>(l, r) \<in> R\<close> ndef
    show ?thesis unfolding defined_def by auto
  qed
  then obtain i q where "p = i#q" by auto
  from \<open>p \<in> poss(Fun f ss)\<close> have "i < length ss" and "q \<in> poss(ss!i)" unfolding \<open>p = i#q\<close> by auto
  let ?D = "ctxt_of_pos_term q (ss!i)"
  have C: "?C = More f (take i ss) ?D (drop (Suc i) ss)" unfolding \<open>p = i#q\<close> by auto
  from \<open>?C\<langle>l\<cdot>\<sigma>\<rangle> = Fun f ss\<close> have "take i ss@?D\<langle>l\<cdot>\<sigma>\<rangle>#drop (Suc i) ss = ss" unfolding C by auto
  then have "(take i ss@?D\<langle>l\<cdot>\<sigma>\<rangle>#drop (Suc i) ss)!i = ss!i" by simp
  with \<open>i < length ss\<close> have "?D\<langle>l\<cdot>\<sigma>\<rangle> = ss!i" using nth_append_take[where xs = ss and i = i] by auto
  have t: "t = Fun f (take i ss@?D\<langle>r\<cdot>\<sigma>\<rangle>#drop (Suc i) ss)" unfolding \<open>?C\<langle>r\<cdot>\<sigma>\<rangle> = t\<close>[symmetric] C by simp
  from \<open>i < length ss\<close> have "t|_[i] = ?D\<langle>r\<cdot>\<sigma>\<rangle>" unfolding t unfolding subt_at.simps using nth_append_take[where xs = ss and i = i] by auto
  from \<open>q \<in> poss(ss!i)\<close> and \<open>(l,r) \<in> R\<close>
    and \<open>?D\<langle>l\<cdot>\<sigma>\<rangle> = ss!i\<close> and \<open>t|_[i] = ?D\<langle>r\<cdot>\<sigma>\<rangle>\<close>[symmetric]
  have "(ss!i,t|_[i]) \<in> rstep_r_p_s R (l,r) q \<sigma>" unfolding rstep_r_p_s_def Let_def by auto
  then have "(ss!i,t|_[i]) \<in> rstep R" unfolding rstep_iff_rstep_r_p_s by auto
  from \<open>i < length ss\<close> and this and t show ?thesis unfolding \<open>t|_[i] = ?D\<langle>r\<cdot>\<sigma>\<rangle>\<close>[symmetric] by auto
qed

lemma nondef_root_imp_arg_steps:
  assumes "(Fun f ss,t) \<in> (rstep R)\<^sup>*"
    and wf: "\<forall>(l, r)\<in>R. is_Fun l"
    and "\<not> defined R (f,length ss)"
  shows "\<exists>ts. length ts = length ss \<and> t = Fun f ts \<and> (\<forall>i<length ss. (ss!i,ts!i) \<in> (rstep R)\<^sup>*)"
proof -
  from assms obtain n where "(Fun f ss,t) \<in> (rstep R)^^n"
    using rtrancl_imp_relpow by best
  then show ?thesis
  proof (induct n arbitrary: t)
    case 0 then show ?case by auto
  next
    case (Suc n)
    then obtain u where "(Fun f ss,u) \<in> (rstep R)^^n" and "(u,t) \<in> rstep R" by auto
    with Suc obtain ts where IH1: "length ts = length ss" and IH2: "u = Fun f ts" and IH3: "\<forall>i<length ss. (ss!i,ts!i) \<in> (rstep R)\<^sup>*" by auto
    from \<open>(u,t) \<in> rstep R\<close> have "(Fun f ts,t) \<in> rstep R" unfolding \<open>u = Fun f ts\<close> .
    from nondef_root_imp_arg_step[OF this wf \<open>\<not> defined R (f,length ss)\<close>[simplified IH1[symmetric]]]
    obtain j where "j < length ts"
      and "(ts!j,t|_[j]) \<in> rstep R"
      and B: "t = Fun f (take j ts@(t|_[j])#drop (Suc j) ts)" (is "t = Fun f ?ts") by auto
    from \<open>j < length ts\<close> have "length ?ts = length ts" by auto
    then have A: "length ?ts = length ss" unfolding \<open>length ts = length ss\<close> .
    have C: "\<forall>i<length ss. (ss!i,?ts!i) \<in> (rstep R)\<^sup>*"
    proof (intro allI, intro impI)
      fix i assume "i < length ss"
      from \<open>i < length ss\<close> and IH3 have "(ss!i,ts!i) \<in> (rstep R)\<^sup>*" by auto
      have "i = j \<or> i \<noteq> j" by auto
      then show "(ss!i,?ts!i) \<in> (rstep R)\<^sup>*"
      proof
        assume "i = j"
        from \<open>j < length ts\<close> have "j \<le> length ts" by simp
        from nth_append_take[OF this] have "?ts!j = t|_[j]" by simp
        from \<open>(ts!j,t|_[j]) \<in> rstep R\<close> have "(ts!i,t|_[i]) \<in> rstep R" unfolding \<open>i = j\<close> .
        with \<open>(ss!i,ts!i) \<in> (rstep R)\<^sup>*\<close> show ?thesis unfolding \<open>i = j\<close> unfolding \<open>?ts!j = t|_[j]\<close> by auto
      next
        assume "i \<noteq> j"
        from \<open>i < length ss\<close> have "i \<le> length ts" unfolding \<open>length ts = length ss\<close> by simp
        from \<open>j < length ts\<close> have "j \<le> length ts" by simp
        from nth_append_take_drop_is_nth_conv[OF \<open>i \<le> length ts\<close> \<open>j \<le> length ts\<close> \<open>i \<noteq> j\<close>]
        have "?ts!i = ts!i" by simp
        with \<open>(ss!i,ts!i) \<in> (rstep R)\<^sup>*\<close> show ?thesis by auto
      qed
    qed
    from A and B and C show ?case by blast
  qed
qed

lemma rstep_imp_nrrstep:
  assumes "is_Fun s" and "\<not> defined R (the (root s))" and "\<forall>(l,r)\<in>R. is_Fun l"
    and "(s, t) \<in> rstep R"
  shows "(s, t) \<in> nrrstep R"
proof -
  from \<open>is_Fun s\<close> obtain f ss where s: "s = Fun f ss" by (cases s) auto
  with assms have undef: "\<not> defined R (f, length ss)" by simp
  from assms have non_var: "\<forall>(l, r)\<in>R. is_Fun l" by auto
  from nondef_root_imp_arg_step[OF \<open>(s, t) \<in> rstep R\<close>[unfolded s] non_var undef]
  obtain i where "i < length ss" and step: "(ss ! i, t |_ [i]) \<in> rstep R"
    and t: "t = Fun f (take i ss @ (t |_ [i]) # drop (Suc i) ss)" by auto
  from step obtain C l r \<sigma> where "(l, r) \<in> R" and lhs: "ss ! i = C\<langle>l \<cdot> \<sigma>\<rangle>"
    and rhs: "t |_ [i] = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  let ?C = "More f (take i ss) C (drop (Suc i) ss)"
  have "(l, r) \<in> R" by fact
  moreover have "?C \<noteq> \<box>" by simp
  moreover have "s = ?C\<langle>l \<cdot> \<sigma>\<rangle>"
  proof -
    have "s = Fun f (take i ss @ ss!i # drop (Suc i) ss)"
      using id_take_nth_drop[OF \<open>i < length ss\<close>] unfolding s by simp
    also have "\<dots> = ?C\<langle>l \<cdot> \<sigma>\<rangle>" by (simp add: lhs)
    finally show ?thesis .
  qed
  moreover have "t = ?C\<langle>r \<cdot> \<sigma>\<rangle>"
  proof -
    have "t = Fun f (take i ss @ t |_ [i] # drop (Suc i) ss)" by fact
    also have "\<dots> = Fun f (take i ss @ C\<langle>r \<cdot> \<sigma>\<rangle> # drop (Suc i) ss)" by (simp add: rhs)
    finally show ?thesis by simp
  qed
  ultimately show "(s, t) \<in> nrrstep R" unfolding nrrstep_def' by blast
qed

lemma rsteps_imp_nrrsteps:
  assumes "is_Fun s" and "\<not> defined R (the (root s))"
    and no_vars: "\<forall>(l, r)\<in>R. is_Fun l"
    and "(s, t) \<in> (rstep R)\<^sup>*"
  shows "(s, t) \<in> (nrrstep R)\<^sup>*"
  using \<open>(s, t) \<in> (rstep R)\<^sup>*\<close>
proof (induct)
  case base show ?case by simp
next
  case (step u v)
  from assms obtain f ss where s: "s = Fun f ss" by (induct s) auto
  from nrrsteps_preserve_root[OF \<open>(s, u) \<in> (nrrstep R)\<^sup>*\<close>[unfolded s]]
  obtain ts where u: "u = Fun f ts" by auto
  from nrrsteps_equiv_num_args[OF \<open>(s, u) \<in> (nrrstep R)\<^sup>*\<close>[unfolded s]]
  have len: "length ss = length ts" unfolding u by simp
  have "is_Fun u" by (simp add: u)
  have undef: "\<not> defined R (the (root u))"
    using \<open>\<not> defined R (the (root s))\<close>
    unfolding s u by (simp add: len)
  have "(u, v) \<in> nrrstep R"
    using rstep_imp_nrrstep[OF \<open>is_Fun u\<close> undef no_vars] step
    by simp
  with step show ?case by auto
qed

lemma left_var_imp_not_SN:
  fixes R :: "('f,'v)trs" and t :: "('f, 'v) term"
  assumes "(Var y, r) \<in> R" (is "(?y, _) \<in> _")
  shows "\<not> (SN_on (rstep R) {t})"
proof (rule steps_imp_not_SN_on)
  fix t :: "('f,'v)term"
  let ?yt = "subst y t"
  show "(t, r \<cdot> ?yt) \<in> rstep R"
    by (rule rstepI[OF assms, where C = \<box> and \<sigma> = ?yt], auto simp: subst_def)
qed

lemma not_SN_subt_imp_not_SN:
  assumes ctxt: "ctxt.closed R" and SN: "\<not> SN_on R {t}" and sub: "s \<unrhd> t"
  shows "\<not> SN_on R {s}"
  using ctxt_closed_SN_on_subt[OF ctxt _ sub] SN
  by auto

lemma root_Some:
  assumes "root t = Some fn"
  obtains ss where "length ss = snd fn" and "t = Fun (fst fn) ss"
  using assms by (induct t) auto

lemma map_funs_rule_power:
  fixes f :: "'f \<Rightarrow> 'f"
  shows "((map_funs_rule f) ^^ n) = map_funs_rule (f ^^ n)"
proof (rule sym, intro ext, clarify)
  fix  l r :: "('f,'v)term"
  show "map_funs_rule (f ^^ n) (l,r) = (map_funs_rule f ^^ n) (l,r)"
  proof (induct n)
    case 0
    show ?case by (simp add: term.map_ident)
  next
    case (Suc n)
    have "map_funs_rule (f ^^ Suc n) (l,r) = map_funs_rule f (map_funs_rule (f ^^ n) (l,r))"
      by (simp add: map_funs_term_comp)
    also have "\<dots> = map_funs_rule f ((map_funs_rule f ^^ n) (l,r))" unfolding Suc ..
    also have "\<dots> = (map_funs_rule f ^^ (Suc n)) (l,r)" by simp
    finally show ?case .
  qed
qed

lemma map_funs_trs_power:
  fixes f :: "'f \<Rightarrow> 'f"
  shows "map_funs_trs f ^^ n = map_funs_trs (f ^^ n)"
proof
  fix R :: "('f, 'v) trs"
  have "map_funs_rule (f ^^ n) ` R = (map_funs_rule f ^^ n) ` R" unfolding map_funs_rule_power ..
  also have "\<dots> = ((\<lambda> R. map_funs_trs f R) ^^ n) R" unfolding map_funs_trs.simps
    apply (induct n)
     apply simp
    by (metis comp_apply funpow.simps(2) image_comp)
  finally have "map_funs_rule (f ^^ n) ` R = (map_funs_trs f ^^ n) R" .
  then show "(map_funs_trs f ^^ n) R = map_funs_trs (f ^^ n) R"
    by (simp add: map_funs_trs.simps)
qed

text \<open>The set of minimally nonterminating terms with respect to a relation @{term "R"}.\<close>
definition Tinf :: "('f, 'v) trs \<Rightarrow> ('f, 'v) terms"
  where
    "Tinf R = {t. \<not> SN_on R {t} \<and> (\<forall>s \<lhd> t. SN_on R {s})}"

lemma not_SN_imp_subt_Tinf:
  assumes "\<not> SN_on R {s}" shows "\<exists>t\<unlhd>s. t \<in> Tinf R"
proof -
  let ?S = "{t | t. s \<unrhd> t \<and> \<not> SN_on R {t}}"
  from assms have s: "s \<in> ?S" by auto
  from mp[OF spec[OF spec[OF SN_imp_minimal[OF SN_supt]]] s]
  obtain t where st: "s \<unrhd> t" and nSN: "\<not> SN_on R {t}"
    and min: "\<forall> u. (t,u) \<in> supt \<longrightarrow> u \<notin> ?S" by auto
  have "t \<in> Tinf R" unfolding Tinf_def
  proof (intro CollectI allI impI conjI nSN)
    fix u
    assume u: "t \<rhd> u"
    from u st have "s \<rhd> u" using supteq_supt_trans by auto
    with min u show "SN_on R {u}" by auto
  qed
  with st show ?thesis by auto
qed

lemma not_SN_imp_Tinf:
  assumes "\<not> SN R" shows "\<exists>t. t \<in> Tinf R"
  using assms not_SN_imp_subt_Tinf unfolding SN_on_def by blast

lemma ctxt_of_pos_term_map_funs_term_conv [iff]:
  assumes "p \<in> poss s"
  shows "map_funs_ctxt fg (ctxt_of_pos_term p s) = (ctxt_of_pos_term p (map_funs_term fg s))"
  using assms
proof (induct s arbitrary: p)
  case (Var x) then show ?case by simp
next
  case (Fun f ss) then show ?case
  proof (cases p)
    case Nil then show ?thesis by simp
  next
    case (Cons i q)
    with \<open>p \<in> poss(Fun f ss)\<close> have "i < length ss" and "q \<in> poss(ss!i)" unfolding Cons poss.simps by auto
    then have "ss!i \<in> set ss" by simp
    with Fun and \<open>q \<in> poss(ss!i)\<close>
    have IH: "map_funs_ctxt fg(ctxt_of_pos_term q (ss!i)) = ctxt_of_pos_term q (map_funs_term fg (ss!i))" by simp
    have "map_funs_ctxt fg(ctxt_of_pos_term p (Fun f ss)) = map_funs_ctxt fg(ctxt_of_pos_term (i#q) (Fun f ss))" unfolding Cons by simp
    also have "\<dots> = map_funs_ctxt fg(More f (take i ss) (ctxt_of_pos_term q (ss!i)) (drop (Suc i) ss))" by simp
    also have "\<dots> = More (fg f) (map (map_funs_term fg) (take i ss)) (map_funs_ctxt fg(ctxt_of_pos_term q (ss!i))) (map (map_funs_term fg) (drop (Suc i) ss))" by simp
    also have "\<dots> = More (fg f) (map (map_funs_term fg) (take i ss)) (ctxt_of_pos_term q (map_funs_term fg (ss!i))) (map (map_funs_term fg) (drop (Suc i) ss))" unfolding IH by simp
    also have "\<dots> = More (fg f) (take i (map (map_funs_term fg) ss)) (ctxt_of_pos_term q (map (map_funs_term fg) ss!i)) (drop (Suc i) (map (map_funs_term fg) ss))" unfolding nth_map[OF \<open>i < length ss\<close>,symmetric] take_map drop_map nth_map by simp
    finally show ?thesis unfolding Cons by simp
  qed
qed

lemma var_rewrite_imp_not_SN:
  assumes sn: "SN_on (rstep R) {u}" and step: "(t, s) \<in> rstep R"
  shows "is_Fun t"
  using assms
proof (cases t)
  case (Fun f ts) then show ?thesis by simp
next
  case (Var x)
  from step obtain l r p \<sigma> where "(Var x, s) \<in> rstep_r_p_s R (l,r) p \<sigma>" unfolding Var rstep_iff_rstep_r_p_s by best
  then have "l \<cdot> \<sigma> = Var x" and rule: "(l,r) \<in> R" unfolding rstep_r_p_s_def by (auto simp: Let_def)
  from this obtain y where "l = Var y" (is "_ = ?y") by (cases l, auto)
  with rule have "(?y, r) \<in> R" by auto
  then have "\<not> (SN_on (rstep R) {u})" by (rule left_var_imp_not_SN)
  with sn show ?thesis by blast
qed

lemma rstep_id: "rstep Id = Id" by auto

lemma map_funs_rule_id [simp]: "map_funs_rule id = id"
  by (intro ext, auto)

lemma map_funs_trs_id [simp]: "map_funs_trs id = id"
  by (intro ext, auto simp: map_funs_trs.simps)

definition sig_step :: "'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs" where
  "sig_step F R = {(a, b). (a, b) \<in> R \<and> funas_term a \<subseteq> F \<and> funas_term b \<subseteq> F}"

lemma sig_step_union: "sig_step F (R \<union> S) = sig_step F R \<union> sig_step F S"
  unfolding sig_step_def by auto

lemma sig_step_UNIV: "sig_step UNIV R = R" unfolding sig_step_def by simp

lemma sig_stepI[intro]: "(a,b) \<in> R \<Longrightarrow> funas_term a \<subseteq> F \<Longrightarrow> funas_term b \<subseteq> F \<Longrightarrow> (a,b) \<in> sig_step F R" unfolding sig_step_def by auto

lemma sig_stepE[elim,consumes 1]: "(a,b) \<in> sig_step F R \<Longrightarrow> \<lbrakk>(a,b) \<in> R \<Longrightarrow> funas_term a \<subseteq> F \<Longrightarrow> funas_term b \<subseteq> F \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" unfolding sig_step_def by auto

lemma all_ctxt_closed_sig_rsteps [intro]:
  fixes R :: "('f, 'v) trs"
  shows "all_ctxt_closed F ((sig_step F (rstep R))\<^sup>*)" (is "all_ctxt_closed _ (?R\<^sup>*)")
proof (rule trans_ctxt_sig_imp_all_ctxt_closed)
  fix C :: "('f,'v)ctxt" and s t :: "('f,'v)term"
  assume C: "funas_ctxt C \<subseteq> F"
    and s: "funas_term s \<subseteq> F"
    and t: "funas_term t \<subseteq> F"
    and steps: "(s,t) \<in> ?R\<^sup>*"
  from steps
  show "(C \<langle> s \<rangle>, C \<langle> t \<rangle>) \<in> ?R\<^sup>*"
  proof (induct)
    case (step t u)
    from step(2) have tu: "(t,u) \<in> rstep R" and t: "funas_term t \<subseteq> F" and u: "funas_term u \<subseteq> F" by auto
    have "(C \<langle> t \<rangle>, C \<langle> u \<rangle>) \<in> ?R" by (rule sig_stepI[OF rstep_ctxt[OF tu]], insert C t u, auto)
    with step(3) show ?case by auto
  qed auto
qed (auto intro: trans_rtrancl)

lemma wf_loop_imp_sig_ctxt_rel_not_SN:
  assumes R: "(l,C\<langle>l\<rangle>) \<in> R" and wf_l: "funas_term l \<subseteq> F"
    and wf_C: "funas_ctxt C \<subseteq> F"
    and ctxt: "ctxt.closed R"
  shows "\<not> SN_on (sig_step F R) {l}"
proof -
  let ?t = "\<lambda> i. (C^i)\<langle>l\<rangle>"
  have "\<forall>i. funas_term (?t i) \<subseteq> F"
  proof
    fix i show "funas_term (?t i) \<subseteq> F" unfolding funas_term_ctxt_apply
      by (rule Un_least[OF _ wf_l], induct i, insert wf_C, auto)
  qed
  moreover have "\<forall>i. (?t i,?t(Suc i)) \<in> R"
  proof
    fix i
    show "(?t i, ?t (Suc i)) \<in> R"
    proof (induct i)
      case 0 with R show ?case by auto
    next
      case (Suc i)
      from ctxt.closedD[OF ctxt Suc, of C]
      show ?case by simp
    qed
  qed
  ultimately have steps: "\<forall>i. (?t i,?t(Suc i)) \<in> sig_step F R" unfolding sig_step_def by blast
  show ?thesis unfolding SN_defs
    by (simp, intro exI[of _ ?t], simp only: steps, simp)
qed

lemma lhs_var_imp_sig_step_not_SN_on:
  assumes x: "(Var x, r) \<in> R" and F: "funas_trs R \<subseteq> F"
  shows "\<not> SN_on (sig_step F (rstep R)) {Var x}"
proof -
  let ?\<sigma> = "(\<lambda>x. r)"
  let ?t = "\<lambda>i. (?\<sigma> ^^ i) x"
  obtain t where t: "t = ?t" by auto
  from rhs_wf[OF x F] have wf_r: "funas_term r \<subseteq> F" .
  {
    fix i
    have "funas_term (?t i) \<subseteq> F"
    proof (induct i)
      case 0 show ?case using wf_r by auto
    next
      case (Suc i)
      have "?t (Suc i) = ?t i \<cdot> ?\<sigma>" unfolding subst_power_Suc subst_compose_def by simp
      also have "funas_term ... \<subseteq> F" unfolding funas_term_subst[of "?t i"]
        using Suc wf_r by auto
      finally show ?case .
    qed
  } note wf_t = this
  {
    fix i
    have "(t i, t (Suc i)) \<in> (sig_step F (rstep R))" unfolding t
      by (rule sig_stepI[OF rstepI[OF x, of _ \<box> "?\<sigma> ^^ i"] wf_t wf_t], auto simp: subst_compose_def)
  } note steps = this
  have x: "t 0 = Var x" unfolding t by simp
  with steps show ?thesis unfolding SN_defs not_not
    by (intro exI[of _ t], auto)
qed

lemma rhs_free_vars_imp_sig_step_not_SN:
  assumes R: "(l,r) \<in> R" and free: "\<not> vars_term r \<subseteq> vars_term l"
    and F: "funas_trs R \<subseteq> F"
  shows "\<not> SN_on (sig_step F (rstep R)) {l}"
proof -
  from free obtain x where x: "x \<in> vars_term r - vars_term l" by auto
  then have "x \<in> vars_term r" by simp
  from supteq_Var[OF this] have "r \<unrhd> Var x" .
  then obtain C where r: "C\<langle>Var x\<rangle> = r" by auto
  let ?\<sigma> = "\<lambda>y. if y = x then l else Var y"
  let ?t = "\<lambda>i. ((C \<cdot>\<^sub>c ?\<sigma>)^i)\<langle>l\<rangle>"
  from rhs_wf[OF R] F have wf_r: "funas_term r \<subseteq> F" by fast
  from lhs_wf[OF R] F have wf_l: "funas_term l \<subseteq> F" by fast
  from wf_r[unfolded r[symmetric]]
  have wf_C: "funas_ctxt C \<subseteq> F" by simp
  from x have neq: "\<forall>y\<in>vars_term l. y \<noteq> x" by auto
  have "l\<cdot>?\<sigma> = l \<cdot> Var"
    by (rule term_subst_eq, insert neq, auto)
  then have l: "l \<cdot> ?\<sigma> = l" by simp
  have wf_C: "funas_ctxt (C \<cdot>\<^sub>c ?\<sigma>) \<subseteq> F" using wf_C wf_l
    by simp
  have rsigma: "r\<cdot>?\<sigma> = (C \<cdot>\<^sub>c ?\<sigma>)\<langle>l\<rangle>" unfolding r[symmetric] by simp
  from R have lr: "(l \<cdot> ?\<sigma>, r \<cdot> ?\<sigma>) \<in> rstep R" by auto
  then have lr: "(l,(C \<cdot>\<^sub>c ?\<sigma>)\<langle>l\<rangle>) \<in> rstep R" unfolding l unfolding rsigma .
  show ?thesis
    by (rule wf_loop_imp_sig_ctxt_rel_not_SN[OF lr wf_l wf_C ctxt_closed_rstep])
qed

lemma lhs_var_imp_rstep_not_SN: assumes "(Var x,r) \<in> R" shows "\<not> SN(rstep R)"
  using lhs_var_imp_sig_step_not_SN_on[OF assms subset_refl] unfolding sig_step_def SN_defs by blast

lemma rhs_free_vars_imp_rstep_not_SN:
  assumes "(l,r) \<in> R" and "\<not> vars_term r \<subseteq> vars_term l"
  shows "\<not> SN_on (rstep R) {l}"
  using rhs_free_vars_imp_sig_step_not_SN[OF assms subset_refl] unfolding sig_step_def SN_defs by blast

lemma free_right_rewrite_imp_not_SN:
  assumes step: "(t,s) \<in> rstep_r_p_s R (l,r) p \<sigma>"
    and vars: "\<not> vars_term l \<supseteq> vars_term r"
  shows "\<not> SN_on (rstep R) {t}"
proof
  assume SN: "SN_on (rstep R) {t}"
  let ?C = "ctxt_of_pos_term p t"
  from step have left: "?C\<langle>l \<cdot> \<sigma>\<rangle> = t" (is "?t = t") and right: "?C\<langle>r \<cdot> \<sigma>\<rangle> = s" and pos: "p \<in> poss t"
    and rule: "(l,r) \<in> R"
    unfolding rstep_r_p_s_def by (auto simp: Let_def)
  from rhs_free_vars_imp_rstep_not_SN[OF rule vars] have nSN:"\<not> SN_on (rstep R) {l}" by simp
  from SN_imp_SN_subt[OF SN ctxt_imp_supteq[of ?C "l \<cdot> \<sigma>", simplified left]]
  have SN: "SN_on (rstep R) {l \<cdot> \<sigma>}" .
  from SNinstance_imp_SN[OF SN] nSN show False by simp
qed

lemma not_SN_on_rstep_subst_apply_term[intro]:
  assumes "\<not> SN_on (rstep R) {t}" shows "\<not> SN_on (rstep R) {t \<cdot> \<sigma>}"
  using assms unfolding SN_on_def by best

lemma SN_rstep_imp_wf_trs: assumes "SN (rstep R)" shows "wf_trs R"
proof (rule ccontr)
  assume "\<not> wf_trs R"
  then obtain l r where R: "(l,r) \<in> R"
    and not_wf: "(\<forall>f ts. l \<noteq> Fun f ts) \<or> \<not>(vars_term r \<subseteq> vars_term l)" unfolding wf_trs_def
    by auto
  from not_wf have "\<not> SN (rstep R)"
  proof
    assume free: "\<not> vars_term r \<subseteq> vars_term l"
    from rhs_free_vars_imp_rstep_not_SN[OF R free] show ?thesis unfolding SN_defs by auto
  next
    assume "\<forall>f ts. l \<noteq> Fun f ts"
    then obtain x where l:"l = Var x" by (cases l) auto
    with R have "(Var x,r) \<in> R" unfolding l by simp
    from lhs_var_imp_rstep_not_SN[OF this] show ?thesis by simp
  qed
  with assms show False by blast
qed

lemma SN_sig_step_imp_wf_trs: assumes SN: "SN (sig_step F (rstep R))" and F: "funas_trs R \<subseteq> F" shows "wf_trs R"
proof (rule ccontr)
  assume "\<not> wf_trs R"
  then obtain l r where R: "(l,r) \<in> R"
    and not_wf: "(\<forall>f ts. l \<noteq> Fun f ts) \<or> \<not>(vars_term r \<subseteq> vars_term l)" unfolding wf_trs_def
    by auto
  from not_wf have "\<not> SN (sig_step F (rstep R))"
  proof
    assume free: "\<not> vars_term r \<subseteq> vars_term l"
    from rhs_free_vars_imp_sig_step_not_SN[OF R free F] show ?thesis unfolding SN_on_def by auto
  next
    assume "\<forall>f ts. l \<noteq> Fun f ts"
    then obtain x where l:"l = Var x" by (cases l) auto
    with R have "(Var x,r) \<in> R" unfolding l by simp
    from lhs_var_imp_sig_step_not_SN_on[OF this F] show ?thesis
      unfolding SN_on_def by auto
  qed
  with assms show False by blast
qed

lemma rhs_free_vars_imp_rstep_not_SN':
  assumes "(l, r) \<in> R" and "\<not> vars_term r \<subseteq> vars_term l"
  shows "\<not> SN (rstep R)"
  using rhs_free_vars_imp_rstep_not_SN [OF assms] by (auto simp: SN_defs)

lemma SN_imp_variable_condition:
  assumes "SN (rstep R)"
  shows "\<forall>(l, r) \<in> R. vars_term r \<subseteq> vars_term l"
  using assms and rhs_free_vars_imp_rstep_not_SN' [of _ _ R] by blast

lemma rstep_cases'[consumes 1, case_names root nonroot]:
  assumes rstep: "(s, t) \<in> rstep R"
    and root: "\<And>l r \<sigma>. (l, r) \<in> R \<Longrightarrow> l \<cdot> \<sigma> = s \<Longrightarrow> r \<cdot> \<sigma> = t \<Longrightarrow> P"
    and nonroot: "\<And>f ss1 u ss2 v. s = Fun f (ss1 @ u # ss2) \<Longrightarrow> t = Fun f (ss1 @ v # ss2) \<Longrightarrow> (u, v) \<in> rstep R \<Longrightarrow> P"
  shows "P"
proof -
  from rstep_imp_C_s_r[OF rstep] obtain C \<sigma> l r
    where R: "(l,r) \<in> R" and s: "C\<langle>l\<cdot>\<sigma>\<rangle> = s" and t: "C\<langle>r\<cdot>\<sigma>\<rangle> = t" by fast
  show ?thesis proof (cases C)
    case Hole
    from s t have "l\<cdot>\<sigma> = s" and "r\<cdot>\<sigma> = t" by (auto simp: Hole)
    with R show ?thesis by (rule root)
  next
    case (More f ss1 D ss2)
    let ?u = "D\<langle>l\<cdot>\<sigma>\<rangle>"
    let ?v  = "D\<langle>r\<cdot>\<sigma>\<rangle>"
    have "s = Fun f (ss1 @ ?u # ss2)" by (simp add: More s[symmetric])
    moreover have "t = Fun f (ss1 @ ?v # ss2)" by (simp add: More t[symmetric])
    moreover have "(?u,?v) \<in> rstep R" using R by auto
    ultimately show ?thesis by (rule nonroot)
  qed
qed

lemma NF_Var: assumes wf: "wf_trs R" shows "(Var x, t) \<notin> rstep R"
proof
  assume "(Var x, t) \<in> rstep R"
  from rstep_imp_C_s_r[OF this] obtain C l r \<sigma>
    where R: "(l,r) \<in> R" and lhs: "Var x = C\<langle>l\<cdot>\<sigma>\<rangle>" by fast
  from lhs have "Var x = l\<cdot>\<sigma>" by (induct C) auto
  then obtain y where l: "l = Var y" by (induct l) auto
  from wf R obtain f ss where "l = Fun f ss" unfolding wf_trs_def by best
  with l show False by simp
qed

lemma rstep_cases_Fun'[consumes 2, case_names root nonroot]:
  assumes wf: "wf_trs R"
    and rstep: "(Fun f ss,t) \<in> rstep R"
    and root': "\<And>ls r \<sigma>. (Fun f ls,r) \<in> R \<Longrightarrow> map (\<lambda>t. t\<cdot>\<sigma>) ls = ss \<Longrightarrow> r\<cdot>\<sigma> = t \<Longrightarrow> P"
    and nonroot': "\<And>i u. i < length ss \<Longrightarrow> t = Fun f (take i ss@u#drop (Suc i) ss) \<Longrightarrow> (ss!i,u) \<in> rstep R \<Longrightarrow> P"
  shows "P"
  using rstep proof (cases rule: rstep_cases')
  case (root l r \<sigma>)
  with wf obtain g ls where l: "l = Fun g ls" unfolding wf_trs_def by best
  from root have [simp]: "g = f" unfolding l by simp
  from root have "(Fun f ls,r) \<in> R" and "map (\<lambda>t. t\<cdot>\<sigma>) ls = ss" and "r\<cdot>\<sigma> = t" unfolding l by auto
  then show ?thesis by (rule root')
next
  case (nonroot g ss1 u ss2 v)
  then have [simp]: "g = f" and args: "ss = ss1 @ u # ss2" by auto
  let ?i = "length ss1"
  from args have ss1: "take ?i ss = ss1" by simp
  from args have "drop ?i ss = u # ss2" by simp
  then have "drop (Suc 0) (drop ?i ss) = ss2" by simp
  then have ss2: "drop (Suc ?i) ss = ss2" by simp
  from args have len: "?i < length ss" by simp
  from id_take_nth_drop[OF len] have "ss = take ?i ss @ ss!?i # drop (Suc ?i) ss" by simp
  then have u: "ss!?i = u" unfolding args unfolding ss1[unfolded args] ss2[unfolded args] by simp
  from nonroot have "t = Fun f (take ?i ss@v#drop (Suc ?i) ss)" unfolding ss1 ss2 by simp
  moreover from nonroot have "(ss!?i,v) \<in> rstep R" unfolding u by simp
  ultimately show ?thesis by (rule nonroot'[OF len])
qed

lemma rstep_preserves_undefined_root:
  assumes "wf_trs R" and "\<not> defined R (f, length ss)" and "(Fun f ss, t) \<in> rstep R"
  shows "\<exists>ts. length ts = length ss \<and> t = Fun f ts"
proof -
  from \<open>wf_trs R\<close> and \<open>(Fun f ss, t) \<in> rstep R\<close> show ?thesis
  proof (cases rule: rstep_cases_Fun')
    case (root ls r \<sigma>)
    then have "defined R (f, length ss)" by (auto simp: defined_def)
    with \<open>\<not> defined R (f, length ss)\<close> show ?thesis by simp
  next
    case (nonroot i u) then show ?thesis by simp
  qed
qed

lemma rstep_ctxt_imp_nrrstep: assumes step: "(s,t) \<in> rstep R" and C: "C \<noteq> \<box>" shows "(C\<langle>s\<rangle>,C\<langle>t\<rangle>) \<in> nrrstep R"
proof -
  from step obtain l r D \<sigma> where "(l,r) \<in> R" "s = D\<langle>l \<cdot> \<sigma>\<rangle>" "t = D\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  thus ?thesis unfolding nrrstep_def' using C
    by (intro CollectI, unfold split, intro exI[of _ "C \<circ>\<^sub>c D"] exI conjI, auto) (cases C, auto)
qed

lemma rsteps_ctxt_imp_nrrsteps: assumes steps: "(s,t) \<in> (rstep R)\<^sup>*" and C: "C \<noteq> \<box>" shows "(C\<langle>s\<rangle>,C\<langle>t\<rangle>) \<in> (nrrstep R)\<^sup>*"
  using steps 
proof (induct)
  case (step t u)
  from rstep_ctxt_imp_nrrstep[OF step(2) C] step(3) show ?case by simp
qed simp

lemma nrrstep_mono:
  assumes "R \<subseteq> R'"
  shows "nrrstep R \<subseteq> nrrstep R'"
  using assms by (force simp: nrrstep_def rstep_r_p_s_def Let_def)

lemma rrstepE:
  assumes "(s, t) \<in> rrstep R"
  obtains l and r and \<sigma> where "(l, r) \<in> R" and "s = l \<cdot> \<sigma>" and "t = r \<cdot> \<sigma>"
  using assms by (auto simp: rrstep_def rstep_r_p_s_def)

lemma nrrstepE:
  assumes "(s, t) \<in> nrrstep R"
  obtains C and l and r and \<sigma> where "C \<noteq> \<box>" and "(l, r) \<in> R"
    and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
  using assms by (auto simp: nrrstep_def rstep_r_p_s_def Let_def)
    (metis ctxt.cop_nil list.discI poss_Cons_poss replace_at_subt_at subt_at_id_imp_eps)


lemma singleton_subst_restrict [simp]:
  "subst x s |s {x} = subst x s"
  unfolding subst_def subst_restrict_def by (rule ext) simp

lemma singleton_subst_map [simp]:
  "f \<circ> subst x s = (f \<circ> Var)(x := f s)" by (intro ext, auto simp: subst_def)

lemma subst_restrict_vars [simp]:
  "(\<lambda>z. if z \<in> V then f z else g z) |s V = f |s V"
  unfolding subst_restrict_def
proof (intro ext)
  fix x
  show "(if x \<in> V then if x \<in> V then f x else g x else Var x)
    = (if x \<in> V then f x else Var x)" by simp
qed

lemma subst_restrict_restrict [simp]:
  assumes "V \<inter> W = {}"
  shows "((\<lambda>z. if z \<in> V then f z else g z) |s W) = g |s W"
  unfolding subst_restrict_def
proof (intro ext)
  fix x
  show "(if x \<in> W then if x \<in> V then f x else g x else Var x)
    = (if x \<in> W then g x else Var x)" using assms by auto
qed

lemma rstep_rstep: "rstep (rstep R) = rstep R"
proof -
  have "ctxt.closure (subst.closure (rstep R)) = rstep R" by (simp only: subst_closure_rstep_eq ctxt_closure_rstep_eq)
  then show ?thesis unfolding rstep_eq_closure .
qed

lemma rstep_trancl_distrib: "rstep (R\<^sup>+) \<subseteq> (rstep R)\<^sup>+"
proof
  fix s t
  assume "(s,t) \<in> rstep (R\<^sup>+)"
  then show "(s,t) \<in> (rstep R)\<^sup>+"
  proof
    fix l r C \<sigma>
    presume lr: "(l,r) \<in> R\<^sup>+" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    from lr have "(C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> (rstep R)\<^sup>+"
    proof(induct)
      case (base r)
      then show ?case by auto
    next
      case (step r rr)
      from step(2) have "(C\<langle>r \<cdot> \<sigma>\<rangle>, C\<langle>rr \<cdot> \<sigma>\<rangle>) \<in> (rstep R)" by auto
      with step(3) show ?case by auto
    qed
    then show "(s,t) \<in> (rstep R)\<^sup>+" unfolding s t .
  qed auto
qed

lemma rsteps_closed_subst:
  assumes "(s, t) \<in> (rstep R)\<^sup>*"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*"
  using assms and subst.closed_rtrancl [OF subst_closed_rstep] by (auto simp: subst.closed_def)

lemma join_subst:
  "subst.closed r \<Longrightarrow> (s, t) \<in> r\<^sup>\<down> \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> r\<^sup>\<down>"
  by (simp add: join_def subst.closedD subst.closed_comp subst.closed_converse subst.closed_rtrancl)


lemma join_subst_rstep [intro]:
  "(s, t) \<in> (rstep R)\<^sup>\<down> \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<down>"
  by (intro join_subst, auto)

lemma join_ctxt [intro]:
  assumes "(s, t) \<in> (rstep R)\<^sup>\<down>"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (rstep R)\<^sup>\<down>"
proof -
  from assms obtain u where "(s, u) \<in> (rstep R)\<^sup>*" and "(t, u) \<in> (rstep R)\<^sup>*" by auto
  then have "(C\<langle>s\<rangle>, C\<langle>u\<rangle>) \<in> (rstep R)\<^sup>*" and "(C\<langle>t\<rangle>, C\<langle>u\<rangle>) \<in> (rstep R)\<^sup>*" by (auto intro: rsteps_closed_ctxt)
  then show ?thesis by blast
qed

lemma rstep_simps:
  "rstep (R\<^sup>=) = (rstep R)\<^sup>="
  "rstep (rstep R) = rstep R"
  "rstep (R \<union> S) = rstep R \<union> rstep S"
  "rstep Id = Id"
  "rstep (R\<^sup>\<leftrightarrow>) = (rstep R)\<^sup>\<leftrightarrow>"
  by auto

lemma rstep_rtrancl_idemp [simp]:
  "rstep ((rstep R)\<^sup>*) = (rstep R)\<^sup>*"
proof -
  { fix s t
    assume "(s, t) \<in> rstep ((rstep R)\<^sup>*)"
    then have "(s, t) \<in> (rstep R)\<^sup>*"
      by (induct) (metis rsteps_closed_ctxt rsteps_closed_subst) }
  then show ?thesis by auto
qed

lemma all_ctxt_closed_rstep_conversion: 
  "all_ctxt_closed UNIV ((rstep R)\<^sup>\<leftrightarrow>\<^sup>*)" 
  unfolding conversion_def rstep_simps(5)[symmetric] by blast


definition instance_rule :: "('f, 'v) rule \<Rightarrow> ('f, 'w) rule \<Rightarrow> bool" where
  [code del]: "instance_rule lr st \<longleftrightarrow> (\<exists> \<sigma>. fst lr = fst st \<cdot> \<sigma> \<and> snd lr = snd st \<cdot> \<sigma>)"
  (* instance rule has implementation in Substitution.thy *)

definition eq_rule_mod_vars :: "('f, 'v) rule \<Rightarrow> ('f, 'v) rule \<Rightarrow> bool" where
  "eq_rule_mod_vars lr st \<longleftrightarrow> instance_rule lr st \<and> instance_rule st lr"

notation eq_rule_mod_vars ("(_/ =\<^sub>v _)" [51,51] 50)

lemma instance_rule_var_cond: assumes eq: "instance_rule (s,t) (l,r)"
  and vars: "vars_term r \<subseteq> vars_term l"
shows "vars_term t \<subseteq> vars_term s"
proof -
  from eq[unfolded instance_rule_def]
  obtain \<tau> where s: "s = l \<cdot> \<tau>" and t: "t = r \<cdot> \<tau>" by auto
  show ?thesis
  proof
    fix x
    assume "x \<in> vars_term t"
    from this[unfolded t] have "x \<in> vars_term (l \<cdot> \<tau>)" using vars unfolding vars_term_subst by auto
    then show "x \<in> vars_term s" unfolding s by auto
  qed
qed

lemma instance_rule_rstep: assumes step: "(s,t) \<in> rstep {lr}"
  and bex: "Bex R (instance_rule lr)"
shows "(s,t) \<in> rstep R"
proof -
  from bex obtain lr' where inst: "instance_rule lr lr'" and R: "lr' \<in> R" by auto
  obtain l r where lr: "lr = (l,r)" by force
  obtain l' r' where lr': "lr' = (l',r')" by force
  note inst = inst[unfolded lr lr']
  note R = R[unfolded lr']
  from inst[unfolded instance_rule_def] obtain \<sigma> where l: "l = l' \<cdot> \<sigma>" and r: "r = r' \<cdot> \<sigma>" by auto
  from step[unfolded lr] obtain C \<tau> where "s = C \<langle>l \<cdot> \<tau>\<rangle>" "t = C \<langle>r \<cdot> \<tau>\<rangle>" by auto
  with l r have s: "s = C\<langle>l' \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)\<rangle>" and t: "t = C\<langle>r' \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)\<rangle>" by auto
  from rstepI[OF R s t] show ?thesis .
qed

lemma eq_rule_mod_vars_var_cond: assumes eq: "(l,r) =\<^sub>v (s,t)"
  and vars: "vars_term r \<subseteq> vars_term l"
shows "vars_term t \<subseteq> vars_term s"
  by (rule instance_rule_var_cond[OF _ vars], insert eq[unfolded eq_rule_mod_vars_def], auto)

lemma eq_rule_mod_varsE[elim]: fixes l :: "('f,'v)term" 
  assumes "(l,r) =\<^sub>v (s,t)"
  shows "\<exists> \<sigma> \<tau>. l = s \<cdot> \<sigma> \<and> r = t \<cdot> \<sigma> \<and> s = l \<cdot> \<tau> \<and> t = r \<cdot> \<tau> \<and> range \<sigma> \<subseteq> range Var \<and> range \<tau> \<subseteq> range Var"
proof -
  from assms[unfolded eq_rule_mod_vars_def instance_rule_def fst_conv snd_conv]
  obtain \<sigma> \<tau> where l: "l = s \<cdot> \<sigma>" and r: "r = t \<cdot> \<sigma>" and s: "s = l \<cdot> \<tau>" and t: "t = r \<cdot> \<tau>" by blast+
  obtain f :: 'f where True by auto
  let ?vst = "vars_term (Fun f [s,t])"
  let ?vlr = "vars_term (Fun f [l,r])"
  define \<sigma>' where "\<sigma>' \<equiv> \<lambda> x. if x \<in> ?vst then \<sigma> x else Var x"
  define \<tau>' where "\<tau>' \<equiv> \<lambda> x. if x \<in> ?vlr then \<tau> x else Var x"
  show ?thesis
  proof (intro exI conjI)
    show l: "l = s \<cdot> \<sigma>'" unfolding l \<sigma>'_def
      by (rule term_subst_eq, auto)
    show r: "r = t \<cdot> \<sigma>'" unfolding r \<sigma>'_def
      by (rule term_subst_eq, auto)
    show s: "s = l \<cdot> \<tau>'" unfolding s \<tau>'_def
      by (rule term_subst_eq, auto)
    show t: "t = r \<cdot> \<tau>'" unfolding t \<tau>'_def
      by (rule term_subst_eq, auto)
    have "Fun f [s,t] \<cdot> Var = Fun f [l, r] \<cdot> \<tau>'" unfolding s t by simp
    also have "\<dots> = Fun f [s,t] \<cdot> (\<sigma>' \<circ>\<^sub>s \<tau>')" unfolding l r by simp
    finally have "Fun f [s,t] \<cdot> (\<sigma>' \<circ>\<^sub>s \<tau>') = Fun f [s,t] \<cdot> Var" by simp
    from term_subst_eq_rev[OF this] have vst: "\<And> x. x \<in> ?vst \<Longrightarrow> \<sigma>' x \<cdot> \<tau>' = Var x" unfolding subst_compose_def by auto
    have "Fun f [l,r] \<cdot> Var = Fun f [s, t] \<cdot> \<sigma>'" unfolding l r by simp
    also have "\<dots> = Fun f [l,r] \<cdot> (\<tau>' \<circ>\<^sub>s \<sigma>')" unfolding s t by simp
    finally have "Fun f [l,r] \<cdot> (\<tau>' \<circ>\<^sub>s \<sigma>') = Fun f [l,r] \<cdot> Var" by simp
    from term_subst_eq_rev[OF this] have vlr: "\<And> x. x \<in> ?vlr \<Longrightarrow> \<tau>' x \<cdot> \<sigma>' = Var x" unfolding subst_compose_def by auto
    {
      fix x
      have "\<sigma>' x \<in> range Var"
      proof (cases "x \<in> ?vst")
        case True
        from vst[OF this] show ?thesis by (cases "\<sigma>' x", auto)
      next
        case False
        then show ?thesis unfolding \<sigma>'_def by auto
      qed
    }
    then show "range \<sigma>' \<subseteq> range Var" by auto
    {
      fix x
      have "\<tau>' x \<in> range Var"
      proof (cases "x \<in> ?vlr")
        case True
        from vlr[OF this] show ?thesis by (cases "\<tau>' x", auto)
      next
        case False
        then show ?thesis unfolding \<tau>'_def by auto
      qed
    }
    then show "range \<tau>' \<subseteq> range Var" by auto
  qed
qed

subsection\<open>Linear and Left-Linear TRSs\<close>

definition
  linear_trs :: "('f, 'v) trs \<Rightarrow> bool"
  where
    "linear_trs R \<equiv> \<forall>(l, r)\<in>R. linear_term l \<and> linear_term r"

lemma linear_trsE[elim,consumes 1]: "linear_trs R \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> linear_term l \<and> linear_term r"
  unfolding linear_trs_def by auto

lemma linear_trsI[intro]: "\<lbrakk> \<And> l r. (l,r) \<in> R \<Longrightarrow> linear_term l \<and> linear_term r\<rbrakk> \<Longrightarrow> linear_trs R"
  unfolding linear_trs_def by auto

definition
  left_linear_trs :: "('f, 'v) trs \<Rightarrow> bool"
  where
    "left_linear_trs R \<longleftrightarrow> (\<forall>(l, r)\<in>R. linear_term l)"

lemma left_linear_trs_union: "left_linear_trs (R \<union> S) = (left_linear_trs R \<and> left_linear_trs S)"
  unfolding left_linear_trs_def by auto

lemma left_linear_mono: assumes "left_linear_trs S" and "R \<subseteq> S" shows "left_linear_trs R"
  using assms unfolding left_linear_trs_def by auto

lemma left_linear_map_funs_trs[simp]:  "left_linear_trs (map_funs_trs f R) = left_linear_trs R"
  unfolding left_linear_trs_def by (auto simp: map_funs_trs.simps)

lemma left_linear_weak_match_rstep:
  assumes rstep: "(u, v) \<in> rstep R"
    and weak_match: "weak_match s u"
    and ll: "left_linear_trs R"
  shows "\<exists>t. (s, t) \<in> rstep R \<and> weak_match t v"
  using weak_match
proof (induct rule: rstep_induct_rule [OF rstep])
  case (1 C sig l r)
  from 1(2) show ?case
  proof (induct C arbitrary: s)
    case (More f bef C aft s)
    let ?n = "Suc (length bef + length aft)"
    let ?m = "length bef"
    from More(2) obtain ss where s: "s = Fun f ss" and lss: "?n = length ss" and wm: "(\<forall>i<length ss. weak_match (ss ! i) ((bef @ C\<langle>l \<cdot> sig\<rangle> # aft) ! i))"  by (cases s, auto)
    from lss wm[THEN spec, of ?m] have "weak_match (ss ! ?m) C\<langle>l \<cdot> sig\<rangle>" by auto
    from More(1)[OF this] obtain t where wmt:  "weak_match t C\<langle>r \<cdot> sig\<rangle>" and step: "(ss ! ?m,t) \<in> rstep R" by auto
    from lss have mss: "?m < length ss" by simp
    let ?tsi = "\<lambda> t. take ?m ss @ t # drop (Suc ?m) ss"
    let ?ts = "?tsi t"
    let ?ss = "?tsi (ss ! ?m)"
    from id_take_nth_drop[OF mss]
    have lts: "length ?ts = ?n" using lss by auto
    show ?case
    proof (rule exI[of _ "Fun f ?ts"], intro conjI)
      have "weak_match (Fun f ?ts) (More f bef C aft)\<langle>r \<cdot> sig\<rangle> =
        weak_match (Fun f ?ts) (Fun f (bef @ C\<langle>r \<cdot> sig\<rangle> # aft))" by simp
      also have "\<dots>" proof (unfold weak_match.simps lts, intro conjI refl allI impI)
        fix i
        assume i: "i < ?n"
        show "weak_match (?ts ! i) ((bef @ C\<langle>r \<cdot> sig\<rangle> # aft) ! i)"
        proof (cases "i = ?m")
          case True
          have "weak_match (?ts ! i) ((bef @ C\<langle>r \<cdot> sig\<rangle> # aft) ! i) = weak_match t C\<langle>r \<cdot> sig\<rangle>"
            using True mss by (simp add: nth_append)
          then show ?thesis using wmt by simp
        next
          case False
          have eq: "?ts ! i = ss ! i \<and> (bef @ C\<langle>r \<cdot> sig\<rangle> # aft) ! i = (bef @ C\<langle>l \<cdot> sig\<rangle> # aft) ! i"
          proof (cases "i < ?m")
            case True
            then show ?thesis by (simp add: nth_append lss[symmetric])
          next
            case False
            with \<open>i \<noteq> ?m\<close> i have "\<exists> j. i = Suc (?m + j) \<and> j < length aft" by presburger
            then obtain j where i: "i = Suc (?m + j)" and j: "j < length aft" by auto
            then have id: " (Suc (length bef + j) - min (Suc (length bef + length aft)) (length bef)) = Suc j" by simp
            from j show ?thesis by (simp add: nth_append i id lss[symmetric])
          qed
          then show ?thesis using wm[THEN spec, of i] i[unfolded lss] by (simp)
        qed
      qed simp
      finally show "weak_match (Fun f ?ts) (More f bef C aft)\<langle>r \<cdot> sig\<rangle>" by simp
    next
      have "s = Fun f ?ss" unfolding s using id_take_nth_drop[OF mss, symmetric] by simp
      also have "\<dots> = (More f (take ?m ss) \<box> (drop (Suc ?m) ss))\<langle>(ss ! ?m)\<rangle>" (is "_ = ?C\<langle>_\<rangle>") by simp
      finally have s: "s = ?C\<langle>ss ! ?m\<rangle>" .
      have t: "Fun f ?ts = ?C\<langle>t\<rangle>" by simp
      from rstep_ctxt[OF step]
      show "(s, Fun f ?ts) \<in> rstep R"
        unfolding s t .
    qed
  next
    case (Hole s)
    from ll 1(1) have "linear_term l" unfolding left_linear_trs_def by auto
    from linear_weak_match[OF this Hole[simplified] refl] obtain \<tau> where
      "s = l \<cdot> \<tau>" and "(\<forall> x \<in> vars_term l . weak_match (Var x \<cdot> \<tau>) (Var x \<cdot> sig))"
      by auto
    then obtain tau where s: "s = l \<cdot> tau" and wm: "(\<forall> x \<in> vars_term l . weak_match (tau x) (Var x \<cdot> sig))"
      by (auto)
    let ?delta = "(\<lambda> x. if x \<in> vars_term l then tau x else Var x \<cdot> sig)"
    show ?case
    proof (rule exI[of _ "r \<cdot> ?delta"], rule conjI)
      have "s = l \<cdot> (tau |s (vars_term l))" unfolding s by (rule coincidence_lemma)
      also have "\<dots> = l \<cdot> (?delta  |s (vars_term l))" by simp
      also have "\<dots> = l \<cdot> ?delta" by (rule coincidence_lemma[symmetric])
      finally have s: "s = l \<cdot> ?delta" .
      from 1(1) have step: "(l \<cdot> ?delta, r \<cdot> ?delta) \<in> rstep R" by auto
      then show "(s, r \<cdot> ?delta) \<in> rstep R" unfolding s .
    next
      have "weak_match (r \<cdot> ?delta) (r \<cdot> sig)"
      proof (induct r)
        case (Fun f ss)
        from this[unfolded set_conv_nth]
        show ?case by (force)
      next
        case (Var x)
        show ?case
        proof (cases "x \<in> vars_term l")
          case True
          with wm Var show ?thesis by simp
        next
          case False
          show ?thesis by (simp add: Var False weak_match_refl)
        qed
      qed
      then show "weak_match (r \<cdot> ?delta) (\<box> \<langle>(r \<cdot> sig)\<rangle>)" by simp
    qed
  qed
qed

context
begin

private fun S where
  "S R s t 0 = s"
| "S R s t (Suc i) = (SOME u. (S R s t i,u) \<in> rstep R \<and> weak_match u (t(Suc i)))"

lemma weak_match_SN:
  assumes wm: "weak_match s t"
    and ll: "left_linear_trs R"
    and SN: "SN_on (rstep R) {s}"
  shows "SN_on (rstep R) {t}"
proof
  fix f
  assume t0: "f 0 \<in> {t}" and chain: "chain (rstep R) f"
  let ?s = "S R s f"
  let ?P = "\<lambda>i u. (?s i, u) \<in> rstep R \<and> weak_match u (f (Suc i))"
  have "\<forall>i. (?s i, ?s (Suc i)) \<in> rstep R \<and> weak_match (?s (Suc i)) (f (Suc i))"
  proof
    fix i show "(?s i, ?s (Suc i)) \<in> rstep R \<and> weak_match (?s (Suc i)) (f (Suc i))"
    proof (induct i)
      case 0
      from chain have ini: "(f 0, f (Suc 0)) \<in> rstep R" by simp
      then have "(t, f (Suc 0)) \<in> rstep R" unfolding singletonD[OF t0, symmetric] .
      from someI_ex[OF left_linear_weak_match_rstep[OF this wm ll]]
      show ?case by simp
    next
      case (Suc i)
      then have IH1: "(?s i, ?s (Suc i)) \<in> rstep R"
        and IH2: "weak_match (?s (Suc i)) (f (Suc i))" by auto
      from chain have nxt: "(f (Suc i), f (Suc (Suc i))) \<in> rstep R" by simp
      from someI_ex[OF left_linear_weak_match_rstep[OF this IH2 ll]]
      have "\<exists>u. ?P (Suc i) u" by auto
      from someI_ex[OF this]
      show ?case by simp
    qed
  qed
  moreover have "?s 0 = s" by simp
  ultimately have "\<not> SN_on (rstep R) {s}" by best
  with SN show False by simp
qed
end

lemma lhs_notin_NF_rstep: "(l, r) \<in> R \<Longrightarrow> l \<notin> NF (rstep R)" by auto

lemma NF_instance:
  assumes "(t \<cdot> \<sigma>) \<in> NF (rstep R)" shows "t \<in> NF (rstep R)"
  using assms by auto

lemma NF_subterm:
  assumes "t \<in> NF (rstep R)" and "t \<unrhd> s"
  shows "s \<in> NF (rstep R)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain u where "(s, u) \<in> rstep R" by auto
  from \<open>t \<unrhd> s\<close> obtain C where "t = C\<langle>s\<rangle>" by auto
  with \<open>(s, u) \<in> rstep R\<close> have "(t, C\<langle>u\<rangle>) \<in> rstep R" by auto
  then have "t \<notin> NF (rstep R)" by auto
  with assms show False by simp
qed

abbreviation
  lhss :: "('f, 'v) trs \<Rightarrow> ('f, 'v) terms"
  where
    "lhss R \<equiv> fst ` R"

abbreviation
  rhss :: "('f, 'v) trs \<Rightarrow> ('f, 'v) terms"
  where
    "rhss R \<equiv> snd ` R"


definition map_funs_trs_wa :: "('f \<times> nat \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('g, 'v) trs" where
  "map_funs_trs_wa fg R = (\<lambda>(l, r). (map_funs_term_wa fg l, map_funs_term_wa fg r)) ` R"

lemma map_funs_trs_wa_union: "map_funs_trs_wa fg (R \<union> S) = map_funs_trs_wa fg R \<union> map_funs_trs_wa fg S"
  unfolding map_funs_trs_wa_def by auto

lemma map_funs_term_wa_compose: "map_funs_term_wa gh (map_funs_term_wa fg t) = map_funs_term_wa (\<lambda> (f,n). gh (fg (f,n), n)) t"
  by (induct t, auto)

lemma map_funs_trs_wa_compose: "map_funs_trs_wa gh (map_funs_trs_wa fg R) = map_funs_trs_wa (\<lambda> (f,n). gh (fg (f,n), n)) R" (is "?L = map_funs_trs_wa ?fgh R")
proof -
  have "map_funs_trs_wa ?fgh R = {(map_funs_term_wa ?fgh l, map_funs_term_wa ?fgh r)| l r. (l,r) \<in> R}" unfolding map_funs_trs_wa_def by auto
  also have "\<dots> = {(map_funs_term_wa gh (map_funs_term_wa fg l), map_funs_term_wa gh (map_funs_term_wa fg r)) | l r. (l,r) \<in> R}" unfolding map_funs_term_wa_compose ..
  finally show ?thesis unfolding map_funs_trs_wa_def by force
qed

lemma map_funs_trs_wa_funas_trs_id: assumes R: "funas_trs R \<subseteq> F"
  and id: "\<And> g n. (g,n) \<in> F \<Longrightarrow> f (g,n) = g"
shows "map_funs_trs_wa f R = R"
proof -
  {
    fix l r
    assume "(l,r) \<in> R"
    with R have l: "funas_term l \<subseteq> F" and r: "funas_term r \<subseteq> F" unfolding funas_trs_def
      by (force simp: funas_rule_def)+
    from map_funs_term_wa_funas_term_id[OF l id] map_funs_term_wa_funas_term_id[OF r id]
    have "map_funs_term_wa f l = l" "map_funs_term_wa f r = r" by auto
  } note main = this
  have "map_funs_trs_wa f R = {(map_funs_term_wa f l, map_funs_term_wa f r) | l r. (l,r) \<in> R}"
    unfolding map_funs_trs_wa_def by force
  also have "\<dots> = R" using main by force
  finally show ?thesis .
qed

lemma map_funs_trs_wa_rstep: assumes step:"(s,t) \<in> rstep R"
  shows "(map_funs_term_wa fg s,map_funs_term_wa fg t) \<in> rstep (map_funs_trs_wa fg R)"
  using step
proof (induct)
  case (IH C \<sigma> l r)
  show ?case unfolding map_funs_trs_wa_def
    by (rule rstepI[where l = "map_funs_term_wa fg l" and r = "map_funs_term_wa fg r" and C = "map_funs_ctxt_wa fg C"], auto simp: IH)
qed

lemma map_funs_trs_wa_rsteps: assumes step:"(s,t) \<in> (rstep R)\<^sup>*"
  shows "(map_funs_term_wa fg s,map_funs_term_wa fg t) \<in> (rstep (map_funs_trs_wa fg R))\<^sup>*"
  using step
proof (induct)
  case (step a b)
  from map_funs_trs_wa_rstep[OF step(2), of fg] step(3) show ?case by auto
qed auto

lemma rstep_ground:
  assumes wf_trs: "\<And>l r. (l, r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    and ground: "ground s"
    and step: "(s, t) \<in> rstep R"
  shows "ground t"
  using step ground
proof (induct)
  case (IH C \<sigma> l r)
  from wf_trs[OF IH(1)] IH(2)
  show ?case by auto
qed

lemma rsteps_ground:
  assumes wf_trs: "\<And>l r. (l, r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    and ground: "ground s"
    and steps: "(s, t) \<in> (rstep R)\<^sup>*"
  shows "ground t"
  using steps ground
  by (induct, insert rstep_ground[OF wf_trs], auto)

definition locally_terminating :: "('f,'v)trs \<Rightarrow> bool"
  where "locally_terminating R \<equiv> \<forall> F. finite F \<longrightarrow> SN (sig_step F (rstep R))"

definition "non_collapsing R \<longleftrightarrow> (\<forall> lr \<in> R. is_Fun (snd lr))"

lemma supt_rstep_stable:
  assumes "(s, t) \<in> {\<rhd>} \<union> rstep R"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> {\<rhd>} \<union> rstep R"
  using assms proof
  assume "s \<rhd> t" show ?thesis
  proof (rule UnI1)
    from \<open>s \<rhd> t\<close> show "s \<cdot> \<sigma> \<rhd> t \<cdot> \<sigma>" by (rule supt_subst)
  qed
next
  assume "(s, t) \<in> rstep R" show ?thesis
  proof (rule UnI2)
    from \<open>(s, t) \<in> rstep R\<close> show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep R" ..
  qed
qed

lemma supt_rstep_trancl_stable:
  assumes "(s, t) \<in> ({\<rhd>} \<union> rstep R)\<^sup>+"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ({\<rhd>} \<union> rstep R)\<^sup>+"
  using assms proof (induct)
  case (base u)
  then have "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> {\<rhd>} \<union> rstep R" by (rule supt_rstep_stable)
  then show ?case ..
next
  case (step u v)
  from \<open>(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> ({\<rhd>} \<union> rstep R)\<^sup>+\<close>
    and supt_rstep_stable[OF \<open>(u, v) \<in> {\<rhd>} \<union> rstep R\<close>, of "\<sigma>"]
  show ?case ..
qed

lemma supt_rsteps_stable:
  assumes "(s, t) \<in> ({\<rhd>} \<union> rstep R)\<^sup>*"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ({\<rhd>} \<union> rstep R)\<^sup>*"
  using assms
proof (induct)
  case base then show ?case ..
next
  case (step u v)
  from \<open>(s, u) \<in> ({\<rhd>} \<union> rstep R)\<^sup>*\<close> and \<open>(u, v) \<in> {\<rhd>} \<union> rstep R\<close>
  have "(s, v) \<in> ({\<rhd>} \<union> rstep R)\<^sup>+" by (rule rtrancl_into_trancl1)
  from trancl_into_rtrancl[OF supt_rstep_trancl_stable[OF this]]
  show ?case .
qed

lemma eq_rule_mod_vars_refl[simp]: "r =\<^sub>v r"
proof (cases r)
  case (Pair l r)
  {
    have "fst (l, r) = fst (l, r) \<cdot> Var \<and> snd (l, r) = snd (l, r) \<cdot> Var" by auto
  }
  then show ?thesis unfolding Pair eq_rule_mod_vars_def instance_rule_def by best
qed

lemma instance_rule_refl[simp]: "instance_rule r r"
  using eq_rule_mod_vars_refl[of r] unfolding eq_rule_mod_vars_def by simp

lemma is_Fun_Fun_conv: "is_Fun t = (\<exists>f ts. t = Fun f ts)" by auto

lemma wf_trs_def':
  "wf_trs R = (\<forall>(l, r)\<in>R. is_Fun l \<and> vars_term r \<subseteq> vars_term l)"
  by (rule iffI) (auto simp: wf_trs_def is_Fun_Fun_conv)

definition wf_rule :: "('f, 'v) rule \<Rightarrow> bool" where
  "wf_rule r \<longleftrightarrow> is_Fun (fst r) \<and> vars_term (snd r) \<subseteq> vars_term (fst r)"

definition wf_rules :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs" where
  "wf_rules R = {r. r \<in> R \<and> wf_rule r}"

lemma wf_trs_wf_rules[simp]: "wf_trs (wf_rules R)"
  unfolding wf_trs_def' wf_rules_def wf_rule_def split_def by simp

lemma wf_rules_subset[simp]: "wf_rules R \<subseteq> R"
  unfolding wf_rules_def by auto

fun wf_reltrs :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs  \<Rightarrow> bool" where
  "wf_reltrs R S = (
    wf_trs R \<and> (R \<noteq> {} \<longrightarrow> (\<forall>l r. (l, r) \<in> S \<longrightarrow> vars_term r \<subseteq> vars_term l)))"

lemma SN_rel_imp_wf_reltrs:
  assumes SN_rel: "SN_rel (rstep R) (rstep S)"
  shows "wf_reltrs R S"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain l r where "\<not> wf_trs R \<or> R \<noteq> {} \<and> (l,r) \<in> S \<and> \<not> vars_term r \<subseteq> vars_term l" (is "_ \<or> ?two") by auto
  then show False
  proof
    assume "\<not> wf_trs R"
    with SN_rstep_imp_wf_trs[OF SN_rel_imp_SN[OF assms]]
    show False by simp
  next
    assume ?two
    then obtain ll rr x where lr: "(l,r) \<in> S" and llrr: "(ll,rr) \<in> R" and x: "x \<in> vars_term r" and nx: "x \<notin> vars_term l" by auto
    obtain f and \<sigma>
      where sigma: "\<sigma> = (\<lambda>y. if x = y then Fun f [ll,l] else Var y)" by auto
    have id: "\<sigma> |s (vars_term l) = Var" unfolding sigma
      by (simp add: subst_restrict_def, rule ext, auto simp: nx)
    have l: "l = l \<cdot> \<sigma>"  by (simp add: coincidence_lemma[of l \<sigma>] id)
    have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep S" using lr by auto
    with l have sstep: "(l, r \<cdot> \<sigma>) \<in> rstep S" by simp
    from supteq_subst[OF supteq_Var[OF x], of \<sigma>] have
      "r \<cdot> \<sigma> \<unrhd> Fun f [ll,l]" unfolding sigma by auto
    then obtain C where "C\<langle>Fun f [ll, l]\<rangle> = r \<cdot> \<sigma>" by auto
    with sstep have sstep: "(l,C\<langle>Fun f [ll, l]\<rangle>) \<in> rstep S" by simp
    obtain r where r: "r = relto (rstep R) (rstep S) \<union> {\<rhd>}" by auto
    have "(C\<langle>Fun f [ll,l]\<rangle>, C\<langle>Fun f [rr,l]\<rangle>) \<in> rstep R"
      by (intro rstepI[OF llrr, of _ "C \<circ>\<^sub>c More f [] \<box> [l]" Var], auto)
    with sstep have relto: "(l,C\<langle>Fun f [rr,l]\<rangle>) \<in> r" unfolding  r by auto
    have "C\<langle>Fun f [rr,l]\<rangle> \<unrhd> Fun f [rr,l]" using ctxt_imp_supteq by auto
    also have "Fun f [rr,l] \<rhd> l" by auto
    finally have supt: "C\<langle>Fun f [rr,l]\<rangle> \<rhd> l" unfolding supt_def by simp
    then have "(C\<langle>Fun f [rr,l]\<rangle>, l) \<in> r" unfolding r by auto
    with relto have loop: "(l, l) \<in> r\<^sup>+" by auto
    have "SN r" unfolding r
      by (rule SN_imp_SN_union_supt[OF SN_rel[unfolded SN_rel_defs]], blast)
    then have "SN (r\<^sup>+)" by (rule SN_imp_SN_trancl)
    with loop show False unfolding SN_on_def by auto
  qed
qed

lemmas rstep_wf_rules_subset = rstep_mono[OF wf_rules_subset]

definition map_vars_trs :: "('v \<Rightarrow> 'w) \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'w) trs" where
  "map_vars_trs f R = (\<lambda> (l, r). (map_vars_term f l, map_vars_term f r)) ` R"

lemma map_vars_trs_rstep:
  assumes "(s, t) \<in> rstep (map_vars_trs f R)" (is "_ \<in> rstep ?R")
  shows "(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> rstep R"
  using assms
proof
  fix ml mr C \<sigma>
  presume mem: "(ml,mr) \<in> ?R" and s: "s = C\<langle>ml \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>mr \<cdot> \<sigma>\<rangle>"
  let ?m = "map_vars_term f"
  from mem obtain l r where mem: "(l,r) \<in> R" and id: "ml = ?m l" "mr = ?m r"
    unfolding map_vars_trs_def by auto
  have id: "s \<cdot> \<tau> = (C \<cdot>\<^sub>c \<tau>)\<langle>?m l \<cdot> \<sigma> \<circ>\<^sub>s \<tau>\<rangle>" "t \<cdot> \<tau> = (C \<cdot>\<^sub>c \<tau>)\<langle>?m r \<cdot> \<sigma> \<circ>\<^sub>s \<tau>\<rangle>" by (auto simp: s t id)
  then show "(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> rstep R"
    unfolding id apply_subst_map_vars_term
    using mem by auto
qed auto

lemma map_vars_rsteps:
  assumes "(s,t) \<in> (rstep (map_vars_trs f R))\<^sup>*" (is "_ \<in> (rstep ?R)\<^sup>*")
  shows "(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  using assms
proof (induct)
  case base then show ?case by simp
next
  case (step t u)
  from map_vars_trs_rstep[OF step(2), of \<tau>] step(3) show ?case by auto
qed

lemma rsteps_subst_closed: "(s,t) \<in> (rstep R)\<^sup>+ \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>+"
proof -
  let ?R = "rstep R"
  assume steps: "(s,t) \<in> ?R\<^sup>+"
  have subst: "subst.closed (?R\<^sup>+)" by (rule subst.closed_trancl[OF subst_closed_rstep])
  from this[unfolded subst.closed_def] steps show ?thesis by auto
qed

lemma supteq_rtrancl_supt:
  "(R\<^sup>+ O {\<unrhd>}) \<subseteq> ({\<rhd>} \<union> R)\<^sup>+" (is "?l \<subseteq> ?r")
proof
  fix x z
  assume "(x,z) \<in> ?l"
  then obtain y where xy: "(x,y) \<in> R\<^sup>+" and yz: "y \<unrhd> z" by auto
  from xy have xy: "(x,y) \<in> ?r" by (rule trancl_mono, simp)
  show "(x,z) \<in> ?r"
  proof (cases "y = z")
    case True
    with xy show ?thesis by simp
  next
    case False
    with yz have yz: "(y,z) \<in> {\<rhd>} \<union> R" by auto
    with xy have xz: "(x,z) \<in> ?r O ({\<rhd>} \<union> R)" by auto
    then show ?thesis by (metis UnCI trancl_unfold)
  qed
qed

lemma rrstepI[intro]: "(l, r) \<in> R \<Longrightarrow> s = l \<cdot> \<sigma> \<Longrightarrow> t = r \<cdot> \<sigma> \<Longrightarrow> (s, t) \<in> rrstep R"
  unfolding rrstep_def' by auto

lemma CS_rrstep_conv: "subst.closure = rrstep"
  apply (intro ext)
  apply (unfold rrstep_def')
  apply (intro subset_antisym)
  by (insert subst.closure.cases, blast, auto)

text \<open>Rewrite steps at a fixed position\<close>

inductive_set rstep_pos :: "('f, 'v) trs \<Rightarrow> pos \<Rightarrow> ('f, 'v) term rel" for R and p
  where
    rule [intro]:"(l, r) \<in> R \<Longrightarrow> p \<in> poss s \<Longrightarrow> s |_ p = l \<cdot> \<sigma> \<Longrightarrow>
    (s, replace_at s p (r \<cdot> \<sigma>)) \<in> rstep_pos R p"

lemma rstep_pos_subst:
  assumes "(s, t) \<in> rstep_pos R p"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep_pos R p"
  using assms
proof (cases)
  case (rule l r \<sigma>')
  with rstep_pos.intros [OF this(2), of p "s \<cdot> \<sigma>" "\<sigma>' \<circ>\<^sub>s \<sigma>"]
  show ?thesis by (auto simp: ctxt_of_pos_term_subst)
qed

lemma rstep_pos_rule:
  assumes "(l, r) \<in> R"
  shows "(l, r) \<in> rstep_pos R []"
  using rstep_pos.intros [OF assms, of "[]" l Var] by simp

lemma rstep_pos_rstep_r_p_s_conv:
  "rstep_pos R p = {(s, t) | s t r \<sigma>. (s, t) \<in> rstep_r_p_s R r p \<sigma>}"
  by (auto simp: rstep_r_p_s_def Let_def subt_at_ctxt_of_pos_term
      intro: replace_at_ident
      elim!: rstep_pos.cases)

lemma rstep_rstep_pos_conv:
  "rstep R = {(s, t) | s t p. (s, t) \<in> rstep_pos R p}"
  by (force simp: rstep_pos_rstep_r_p_s_conv rstep_iff_rstep_r_p_s)

lemma rstep_pos_supt:
  assumes "(s, t) \<in> rstep_pos R p"
    and q: "q \<in> poss u" and u: "u |_ q = s"
  shows "(u, (ctxt_of_pos_term q u)\<langle>t\<rangle>) \<in> rstep_pos R (q @ p)"
  using assms
proof (cases)
  case (rule l r \<sigma>)
  with q and u have "(q @ p) \<in> poss u" and "u |_ (q @ p) = l \<cdot> \<sigma>" by auto
  with rstep_pos.rule [OF rule(2) this] show ?thesis
    unfolding rule by (auto simp: ctxt_of_pos_term_append u)
qed

lemma rrstep_rstep_pos_conv:
  "rrstep R = rstep_pos R []"
  by (auto simp: rrstep_def rstep_pos_rstep_r_p_s_conv)

lemma rrstep_imp_rstep:
  assumes "(s, t) \<in> rrstep R"
  shows "(s, t) \<in> rstep R"
  using assms by (auto simp: rrstep_def rstep_iff_rstep_r_p_s)

lemma not_NF_rstep_imp_subteq_not_NF_rrstep:
  assumes "s \<notin> NF (rstep R)"
  shows "\<exists>t \<unlhd> s. t \<notin> NF (rrstep R)"
proof -
  from assms obtain u where "(s, u) \<in> rstep R" by auto
  then obtain l r C \<sigma> where "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and u: "u = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
  then have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rrstep R" and "l \<cdot> \<sigma> \<unlhd> s" by auto
  then show ?thesis by blast
qed

lemma all_subt_NF_rrstep_iff_all_subt_NF_rstep:
  "(\<forall>s \<lhd> t. s \<in> NF (rrstep R)) \<longleftrightarrow> (\<forall>s \<lhd> t. s \<in> NF (rstep R))"
  by (auto dest: rrstep_imp_rstep supt_supteq_trans not_NF_rstep_imp_subteq_not_NF_rrstep)

lemma not_in_poss_imp_NF_rstep_pos [simp]:
  assumes "p \<notin> poss s"
  shows "s \<in> NF (rstep_pos R p)"
  using assms by (auto simp: NF_def elim: rstep_pos.cases)

lemma Var_rstep_imp_rstep_pos_Empty:
  assumes "(Var x, t) \<in> rstep R"
  shows "(Var x, t) \<in> rstep_pos R []"
  using assms by (metis Var_supt nrrstep_subt rrstep_rstep_pos_conv rstep_cases)

lemma rstep_args_NF_imp_rrstep:
  assumes "(s, t) \<in> rstep R"
    and "\<forall>u \<lhd> s. u \<in> NF (rstep R)"
  shows "(s, t) \<in> rrstep R"
  using assms by (metis NF_iff_no_step nrrstep_subt rstep_cases)

lemma rstep_pos_imp_rstep_pos_Empty:
  assumes "(s, t) \<in> rstep_pos R p"
  shows "(s |_ p, t |_ p) \<in> rstep_pos R []"
  using assms by (cases) (auto simp: replace_at_subt_at intro: rstep_pos_rule rstep_pos_subst)

lemma rstep_pos_arg:
  assumes "(s, t) \<in> rstep_pos R p"
    and "i < length ss" and "ss ! i = s"
  shows "(Fun f ss, (ctxt_of_pos_term [i] (Fun f ss))\<langle>t\<rangle>) \<in> rstep_pos R (i # p)"
  using assms
  by cases (auto simp: rstep_pos.simps)

lemma rstep_imp_max_pos:
  assumes "(s, t) \<in> rstep R"
  shows "\<exists>u. \<exists>p\<in>poss s. (s, u) \<in> rstep_pos R p \<and> (\<forall>v \<lhd> s |_ p. v \<in> NF (rstep R))"
  using assms
proof (induction s arbitrary: t)
  case (Var x)
  from Var_rstep_imp_rstep_pos_Empty [OF this] show ?case by auto
next
  case (Fun f ss)
  show ?case
  proof (cases "\<forall>v \<lhd> Fun f ss |_ []. v \<in> NF (rstep R)")
    case True
    moreover with Fun.prems
    have "(Fun f ss, t) \<in> rstep_pos R []"
      by (auto dest: rstep_args_NF_imp_rrstep simp: rrstep_rstep_pos_conv)
    ultimately show ?thesis by auto
  next
    case False
    then obtain v where "v \<lhd> Fun f ss" and "v \<notin> NF (rstep R)" by auto
    then obtain s and w where "s \<in> set ss" and "s \<unrhd> v" and "(s, w) \<in> rstep R"
      by (auto simp: NF_def) (metis NF_iff_no_step NF_subterm supt_Fun_imp_arg_supteq)
    from Fun.IH [OF this(1, 3)] obtain u and p
      where "p \<in> poss s" and *: "(s, u) \<in> rstep_pos R p"
        and **: "\<forall>v \<lhd> s |_ p. v \<in> NF (rstep R)" by blast
    from \<open>s \<in> set ss\<close> obtain i
      where "i < length ss" and [simp]:"ss ! i = s" by (auto simp: in_set_conv_nth)
    with \<open>p \<in> poss s\<close> have "i # p \<in> poss (Fun f ss)" by auto
    moreover with ** have "\<forall>v \<lhd> Fun f ss |_ (i # p). v \<in> NF (rstep R)" by auto
    moreover from rstep_pos_arg [OF * \<open>i < length ss\<close> \<open>ss ! i = s\<close>]
    have "(Fun f ss, (ctxt_of_pos_term [i] (Fun f ss))\<langle>u\<rangle>) \<in> rstep_pos R (i # p)" .
    ultimately show ?thesis by blast
  qed
qed

subsection\<open>Normal Forms\<close>

abbreviation NF_trs :: "('f, 'v) trs \<Rightarrow> ('f, 'v) terms" where
  "NF_trs R \<equiv> NF (rstep R)"

lemma NF_trs_mono: "r \<subseteq> s \<Longrightarrow> NF_trs s \<subseteq> NF_trs r"
  by (rule NF_anti_mono[OF rstep_mono])

lemma NF_trs_union: "NF_trs (R \<union> S) = NF_trs R \<inter> NF_trs S"
  unfolding rstep_union using NF_anti_mono[of _ "rstep R \<union> rstep S"] by auto

abbreviation NF_terms :: "('f, 'v) terms \<Rightarrow> ('f, 'v) terms" where
  "NF_terms Q \<equiv> NF (rstep (Id_on Q))"

lemma NF_terms_anti_mono:
  "Q \<subseteq> Q' \<Longrightarrow> NF_terms Q' \<subseteq> NF_terms Q"
  by (rule NF_trs_mono, auto)

lemma lhs_var_not_NF:
  assumes "l \<in> T" and "is_Var l" shows "t \<notin> NF_terms T"
proof -
  from assms obtain x where l: "l = Var x" by (cases l, auto)
  let ?\<sigma> = "subst x t"
  from assms have "l \<notin> NF_terms T" by auto
  with NF_instance[of l "?\<sigma>" "Id_on T"]
  have "l \<cdot> ?\<sigma> \<notin> NF_terms T" by auto
  then show ?thesis by (simp add: l subst_def)
qed

lemma not_NF_termsE[elim]:
  assumes "s \<notin> NF_terms Q"
  obtains l C \<sigma> where "l \<in> Q" and "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
proof -
  from assms obtain t where "(s, t) \<in> rstep (Id_on Q)" by auto
  with \<open>\<And>l C \<sigma>. \<lbrakk>l \<in> Q; s = C\<langle>l \<cdot> \<sigma>\<rangle>\<rbrakk> \<Longrightarrow> thesis\<close> show ?thesis by auto
qed

lemma notin_NF_E [elim]:
  fixes R :: "('f, 'v) trs"
  assumes "t \<notin> NF_trs R"
  obtains C l and \<sigma> :: "('f, 'v) subst" where "l \<in> lhss R" and "t = C\<langle>l \<cdot> \<sigma>\<rangle>"
proof -
  assume 1: "\<And>l C (\<sigma>::('f, 'v) subst). l \<in> lhss R \<Longrightarrow> t = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> thesis"
  from assms obtain u where "(t, u) \<in> rstep R" by (auto simp: NF_def)
  then obtain C \<sigma> l r where "(l, r) \<in> R" and "t = C\<langle>l \<cdot> \<sigma>\<rangle>" by blast
  with 1 show ?thesis by force
qed

lemma NF_ctxt_subst: "NF_terms Q = {t. \<not> (\<exists> C q \<sigma>. t = C\<langle>q\<cdot>\<sigma>\<rangle> \<and> q \<in> Q)}" (is "_ = ?R")
proof -
  {
    fix t
    assume "t \<notin> ?R"
    then obtain C q \<sigma> where t: "t = C\<langle>q\<cdot>\<sigma>\<rangle>" and q: "q \<in> Q" by auto
    have "(t,t) \<in> rstep (Id_on Q)"
      unfolding t using q by auto
    then have "t \<notin> NF_terms Q" by auto
  }
  moreover
  {
    fix t
    assume "t \<notin> NF_terms Q"
    then obtain C q \<sigma> where t: "t = C\<langle>q\<cdot>\<sigma>\<rangle>" and q: "q \<in> Q" by auto
    then have "t \<notin> ?R" by auto
  }
  ultimately show ?thesis by auto
qed

lemma some_NF_imp_no_Var:
  assumes "t \<in> NF_terms Q"
  shows "Var x \<notin> Q"
proof
  assume "Var x \<in> Q"
  with assms[unfolded NF_ctxt_subst] have "\<And> \<sigma> C. t \<noteq> C \<langle> \<sigma> x \<rangle>" by force
  from this[of Hole "\<lambda> _. t"] show False by simp
qed

lemma NF_map_vars_term_inj:
  assumes inj: "\<And> x. n (m x) = x" and NF: "t \<in> NF_terms Q"
  shows "(map_vars_term m t) \<in> NF_terms (map_vars_term m ` Q)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain u where "(map_vars_term m t, u) \<in> rstep (Id_on (map_vars_term m ` Q))" by blast
  then obtain ml mr C \<sigma> where in_mR: "(ml, mr) \<in> Id_on (map_vars_term m ` Q)"
    and mt: "map_vars_term m t = C\<langle>ml \<cdot> \<sigma>\<rangle>" by best
  let ?m = n
  from in_mR obtain l r where "(l, r) \<in> Id_on Q" and ml: "ml = map_vars_term m l" by auto
  have "t = map_vars_term ?m (map_vars_term m t)" by (simp add: map_vars_term_inj_compose[of n m, OF inj])
  also have "\<dots> = map_vars_term ?m (C\<langle>ml \<cdot> \<sigma>\<rangle>)" by (simp add: mt)
  also have "\<dots> = (map_vars_ctxt ?m C)\<langle>map_vars_term ?m (map_vars_term m l \<cdot> \<sigma>)\<rangle>"
    by (simp add: map_vars_term_ctxt_commute ml)
  also have "\<dots> = (map_vars_ctxt ?m C)\<langle>l \<cdot> (map_vars_subst_ran ?m (\<sigma> \<circ> m))\<rangle>"
    by (simp add: apply_subst_map_vars_term map_vars_subst_ran)
  finally show False using NF and \<open>(l, r) \<in> Id_on Q\<close> by auto
qed

lemma notin_NF_terms: "t \<in> Q \<Longrightarrow> t \<notin> NF_terms Q"
  using lhs_notin_NF_rstep[of t t "Id_on Q"] by (simp add: Id_on_iff)

lemma NF_termsI [intro]:
  assumes NF: "\<And> C l \<sigma>. t = C \<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> l \<in> Q \<Longrightarrow> False"
  shows "t \<in> NF_terms Q"
  by (rule ccontr, rule not_NF_termsE [OF _ NF])

lemma NF_args_imp_NF:
  assumes ss: "\<And> s. s \<in> set ss \<Longrightarrow> s \<in> NF_terms Q"
    and someNF: "t \<in> NF_terms Q"
    and root: "Some (f,length ss) \<notin> root ` Q"
  shows "(Fun f ss) \<in> NF_terms Q"
proof
  fix C l \<sigma>
  assume id: "Fun f ss = C \<langle> l \<cdot> \<sigma> \<rangle>" and l: "l \<in> Q"
  show False
  proof (cases C)
    case Hole
    with id have id: "Fun f ss = l \<cdot> \<sigma>" by simp
    show False
    proof (cases l)
      case (Fun g ls)
      with id have fg: "f = g" and ss: "ss = map (\<lambda> s. s \<cdot> \<sigma>) ls" by auto
      from arg_cong[OF ss, of length] have len: "length ss = length ls" by simp
      from l[unfolded Fun] root[unfolded fg len] show False by force
    next
      case (Var x)
      from some_NF_imp_no_Var[OF someNF] Var l show False by auto
    qed
  next
    case (More g bef D aft)
    note id = id[unfolded More]
    from id have NF: "ss ! length bef = D \<langle>l \<cdot> \<sigma>\<rangle>" by auto
    from id have mem: "ss ! length bef \<in> set ss" by auto
    from ss[OF mem, unfolded NF_ctxt_subst NF] l show False by auto
  qed
qed

lemma NF_Var_is_Fun:
  assumes Q: "Ball Q is_Fun"
  shows "Var x \<in> NF_terms Q"
proof
  fix C l \<sigma>
  assume x: "Var x = C \<langle> l \<cdot> \<sigma> \<rangle>" and l: "l \<in> Q"
  from l Q obtain f ls where l: "l = Fun f ls" by (cases l, auto)
  then show False using x by (cases C, auto)
qed

lemma NF_terms_lhss [simp]: "NF_terms (lhss R) = NF (rstep R)"
proof
  show "NF (rstep R) \<subseteq> NF_terms (lhss R)" by force
next
  show "NF_terms (lhss R) \<subseteq> NF (rstep R)"
  proof
    fix s assume NF: "s \<in> NF_terms (lhss R)"
    show "s \<in> NF (rstep R)"
    proof (rule ccontr)
      assume "s \<notin> NF (rstep R)"
      then obtain t where "(s, t) \<in> rstep R" by auto
      then obtain l r C \<sigma> where "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" by auto
      then have "(l, l) \<in> Id_on (lhss R)" by force
      then have "(s, s) \<in> rstep (Id_on (lhss R))" unfolding s by auto
      with NF show False by auto
    qed
  qed
qed

subsection\<open>Relative Rewrite Steps\<close>

abbreviation "relstep R E \<equiv> relto (rstep R) (rstep E)"

lemma args_SN_on_relstep_nrrstep_imp_args_SN_on:
  assumes SN: "\<And> u. s \<rhd> u \<Longrightarrow> SN_on (relstep R E) {u}"
    and st: "(s,t) \<in> nrrstep (R \<union> E)"
    and supt: "t \<rhd> u"
  shows "SN_on (relstep R E) {u}"
proof -
  from nrrstepE[OF st] obtain C l r \<sigma> where "C \<noteq> \<box>" and lr: "(l,r) \<in> R \<union> E"
    and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
  then obtain f bef C aft where s: "s = Fun f (bef @ C\<langle>l \<cdot> \<sigma>\<rangle> # aft)" and t: "t = Fun f (bef @ C\<langle>r \<cdot> \<sigma>\<rangle> # aft)"
    by (cases C, auto)
  let ?ts = "bef @ C\<langle>r \<cdot> \<sigma>\<rangle> # aft"
  let ?ss = "bef @ C\<langle>l \<cdot> \<sigma>\<rangle> # aft"
  from supt obtain D where "t = D\<langle>u\<rangle>" and "D \<noteq> \<box>" by auto
  then obtain bef' aft' D where t': "t = Fun f (bef' @ D\<langle>u\<rangle> # aft')" unfolding t by (cases D, auto)
  have "D\<langle>u\<rangle> \<unrhd> u" by auto
  then have supt: "\<And> s. s \<rhd> D\<langle>u\<rangle> \<Longrightarrow> s \<rhd> u" by (metis supt_supteq_trans)
  show "SN_on (relstep R E) {u}"
  proof (cases "D\<langle>u\<rangle> \<in> set ?ss")
    case True
    then have "s \<rhd> D\<langle>u\<rangle>" unfolding s by auto
    then have "s \<rhd> u" by (rule supt)
    with SN show ?thesis by auto
  next
    case False
    have "D\<langle>u\<rangle> \<in> set ?ts" using arg_cong[OF t'[unfolded t], of args] by auto
    with False have Du: "D\<langle>u\<rangle> = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
    have "s \<rhd> C\<langle>l \<cdot> \<sigma>\<rangle>" unfolding s by auto
    with SN have "SN_on (relstep R E) {C\<langle>l \<cdot> \<sigma>\<rangle>}" by auto
    from step_preserves_SN_on_relto[OF _ this, of "C\<langle>r \<cdot> \<sigma>\<rangle>"] lr
    have SN: "SN_on (relstep R E) {D\<langle>u\<rangle>}" using Du by auto
    show ?thesis
      by (rule ctxt_closed_SN_on_subt[OF ctxt.closed_relto SN], auto)
  qed
qed

lemma Tinf_nrrstep:
  assumes tinf: "s \<in> Tinf (relstep R E)" and st: "(s,t) \<in> nrrstep (R \<union> E)"
    and t: "\<not> SN_on (relstep R E) {t}"
  shows "t \<in> Tinf (relstep R E)"
  unfolding Tinf_def
  by (intro CollectI conjI[OF t] allI impI)
    (rule args_SN_on_relstep_nrrstep_imp_args_SN_on[OF _ st],
      insert tinf[unfolded Tinf_def], auto)

lemma subterm_preserves_SN_on_relstep:
  "SN_on (relstep R E) {s} \<Longrightarrow> s \<unrhd> t \<Longrightarrow> SN_on (relstep R E) {t}"
  using SN_imp_SN_subt [of "rstep (rstep ((rstep E)\<^sup>*) O rstep R O rstep ((rstep E)\<^sup>*))"]
  by (simp only: rstep_relcomp_idemp2) (simp only: rstep_rtrancl_idemp)

inductive_set rstep_rule :: "('f, 'v) rule \<Rightarrow> ('f, 'v) term rel" for \<rho>
  where
    rule: "s = C\<langle>fst \<rho> \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>snd \<rho> \<cdot> \<sigma>\<rangle> \<Longrightarrow> (s, t) \<in> rstep_rule \<rho>"

lemma rstep_ruleI [intro]:
  "s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> (s, t) \<in> rstep_rule (l, r)"
  by (auto simp: rstep_rule.simps)

lemma rstep_rule_ctxt:
  "(s, t) \<in> rstep_rule \<rho> \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> rstep_rule \<rho>"
  using rstep_rule.rule [of "C\<langle>s\<rangle>" "C \<circ>\<^sub>c D" \<rho> _ "C\<langle>t\<rangle>" for D]
  by (auto elim: rstep_rule.cases simp: ctxt_of_pos_term_append)

lemma rstep_rule_subst:
  assumes "(s, t) \<in> rstep_rule \<rho>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep_rule \<rho>"
  using assms
proof (cases)
  case (rule C \<tau>)
  then show ?thesis
    using rstep_rule.rule [of "s \<cdot> \<sigma>" _ "\<rho>" "\<tau> \<circ>\<^sub>s \<sigma>"]
    by (auto elim!: rstep_rule.cases simp: ctxt_of_pos_term_subst)
qed

lemma rstep_rule_imp_rstep:
  "\<rho> \<in> R \<Longrightarrow> (s, t) \<in> rstep_rule \<rho> \<Longrightarrow> (s, t) \<in> rstep R"
  by (force elim: rstep_rule.cases)

lemma rstep_imp_rstep_rule:
  assumes "(s, t) \<in> rstep R"
  obtains l r where "(l, r) \<in> R" and "(s, t) \<in> rstep_rule (l, r)"
  using assms by blast

lemma term_subst_rstep:
  assumes "\<And>x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> rstep R"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  using assms
proof (induct t)
  case (Fun f ts)
  { fix t\<^sub>i
    assume t\<^sub>i: "t\<^sub>i \<in> set ts"
    with Fun(2) have "\<And>x. x \<in> vars_term t\<^sub>i \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> rstep R" by auto
    from Fun(1) [OF t\<^sub>i this] have "(t\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<tau>) \<in> (rstep R)\<^sup>*" by blast
  }
  then show ?case by (simp add: args_rsteps_imp_rsteps)
qed (auto)

lemma term_subst_rsteps:
  assumes "\<And>x. x \<in> vars_term t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> (rstep R)\<^sup>*"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (rstep R)\<^sup>*"
  by (metis assms rstep_rtrancl_idemp rtrancl_idemp term_subst_rstep)

lemma term_subst_rsteps_join:
  assumes "\<And>y. y \<in> vars_term u \<Longrightarrow> (\<sigma>\<^sub>1 y, \<sigma>\<^sub>2 y) \<in> (rstep R)\<^sup>\<down>"
  shows "(u \<cdot> \<sigma>\<^sub>1, u \<cdot> \<sigma>\<^sub>2) \<in> (rstep R)\<^sup>\<down>"
  using assms
proof -
  { fix x
    assume "x \<in> vars_term u"
    from assms [OF this] have "\<exists>\<sigma>. (\<sigma>\<^sub>1 x, \<sigma> x) \<in> (rstep R)\<^sup>* \<and> (\<sigma>\<^sub>2 x, \<sigma> x) \<in> (rstep R)\<^sup>*" by auto
  }
  then have "\<forall>x \<in> vars_term u. \<exists>\<sigma>. (\<sigma>\<^sub>1 x, \<sigma> x) \<in> (rstep R)\<^sup>* \<and> (\<sigma>\<^sub>2 x, \<sigma> x) \<in> (rstep R)\<^sup>*" by blast
  then obtain s where "\<forall>x \<in> vars_term u. (\<sigma>\<^sub>1 x, (s x) x) \<in> (rstep R)\<^sup>* \<and> (\<sigma>\<^sub>2 x, (s x) x) \<in> (rstep R)\<^sup>*" by metis
  then obtain \<sigma> where "\<forall>x \<in> vars_term u. (\<sigma>\<^sub>1 x, \<sigma> x) \<in> (rstep R)\<^sup>* \<and> (\<sigma>\<^sub>2 x, \<sigma> x) \<in> (rstep R)\<^sup>*" by fast
  then have "(u \<cdot> \<sigma>\<^sub>1, u \<cdot> \<sigma>) \<in> (rstep R)\<^sup>* \<and> (u \<cdot> \<sigma>\<^sub>2, u \<cdot> \<sigma>) \<in> (rstep R)\<^sup>*" using term_subst_rsteps by metis
  then show ?thesis by blast
qed

lemma funas_trs_converse [simp]: "funas_trs (R\<inverse>) = funas_trs R"
  by (auto simp: funas_defs)

lemma rstep_rev: assumes "(s, t) \<in> rstep_pos {(l,r)} p" shows "((t, s) \<in> rstep_pos {(r,l)} p)"
proof-
  from assms obtain \<sigma> where step:"t = (ctxt_of_pos_term p s)\<langle>r \<cdot> \<sigma>\<rangle>" "p \<in> poss s" "s |_ p = l \<cdot> \<sigma>"
    unfolding rstep_pos.simps by auto
  with replace_at_below_poss[of p s p] have pt:"p \<in> poss t" by auto
  with step ctxt_supt_id[OF step(2)] have "s = (ctxt_of_pos_term p t)\<langle>l \<cdot> \<sigma>\<rangle>"
    by (simp add: ctxt_of_pos_term_replace_at_below)
  with step ctxt_supt_id[OF pt] show ?thesis unfolding rstep_pos.simps
    by (metis pt replace_at_subt_at singletonI)
qed

lemma conversion_ctxt_closed: "(s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  using rsteps_closed_ctxt unfolding conversion_def
  by (simp only: rstep_simps(5)[symmetric])

lemma conversion_subst_closed:
  "(s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> (s \<cdot> \<sigma>,  t \<cdot> \<sigma>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  using rsteps_closed_subst unfolding conversion_def
  by (simp only: rstep_simps(5)[symmetric])

lemma rstep_simulate_conv:
  assumes "\<And> l r. (l, r) \<in> S \<Longrightarrow> (l, r) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(rstep S) \<subseteq> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
proof
  fix s t
  assume "(s, t) \<in> rstep S"
  then obtain l r C \<sigma> where s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>" and lr: "(l, r) \<in> S"
    unfolding rstep_iff_rstep_r_c_s rstep_r_c_s_def by auto
  with assms have "(l, r) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" by auto
  then show "(s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using conversion_ctxt_closed conversion_subst_closed s t by metis
qed

lemma symcl_simulate_conv:
  assumes "\<And> l r. (l, r) \<in> S \<Longrightarrow> (l, r) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(rstep S)\<^sup>\<leftrightarrow> \<subseteq> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  using rstep_simulate_conv[OF assms]
  by auto (metis conversion_inv subset_iff)

lemma conv_union_simulate:
  assumes "\<And> l r. (l, r) \<in> S \<Longrightarrow> (l, r) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(rstep (R \<union> S))\<^sup>\<leftrightarrow>\<^sup>* = (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
proof
  show "(rstep (R \<union> S))\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def
  proof
    fix s t
    assume "(s, t) \<in> ((rstep (R \<union> S))\<^sup>\<leftrightarrow>)\<^sup>*"
    then show "(s, t) \<in> ((rstep R)\<^sup>\<leftrightarrow>)\<^sup>*"
    proof (induct rule: rtrancl_induct)
      case (step u t)
      then have "(u, t) \<in> (rstep R)\<^sup>\<leftrightarrow> \<or> (u, t) \<in> (rstep S)\<^sup>\<leftrightarrow>" by auto
      then show ?case
      proof
        assume "(u, t) \<in> (rstep R)\<^sup>\<leftrightarrow>"
        with step show ?thesis using rtrancl_into_rtrancl by metis
      next
        assume "(u, t) \<in> (rstep S)\<^sup>\<leftrightarrow>"
        with symcl_simulate_conv[OF assms] have "(u, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" by auto
        with step show ?thesis by auto
      qed
    qed simp
  qed
next
  show "(rstep R)\<^sup>\<leftrightarrow>\<^sup>* \<subseteq> (rstep (R \<union> S))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def
    using rstep_union rtrancl_mono sup.cobounded1 symcl_Un
    by metis
qed

definition "suptrel R = (relto {\<rhd>} (rstep R))\<^sup>+"
end