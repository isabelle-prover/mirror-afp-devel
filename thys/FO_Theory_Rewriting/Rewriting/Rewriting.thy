section \<open>Rewriting\<close>

theory Rewriting
  imports Regular_Tree_Relations.Term_Context
    Regular_Tree_Relations.Ground_Terms
    Utils
begin

subsection \<open>Type definitions and rewrite relation definitions\<close>
type_synonym 'f sig = "('f \<times> nat) set"
type_synonym ('f, 'v) rule = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) trs  = "('f, 'v) rule set"


definition "sig_step \<F> \<R> = {(s, t). funas_term s \<subseteq> \<F> \<and> funas_term t \<subseteq> \<F> \<and> (s, t) \<in> \<R>}"

inductive_set rstep :: "_ \<Rightarrow> ('f, 'v) term rel" for R :: "('f, 'v) trs"
  where
    rstep: "\<And>C \<sigma> l r. (l, r) \<in> R \<Longrightarrow> s = C\<langle>l \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<Longrightarrow> (s, t) \<in> rstep R"

definition rstep_r_p_s :: "('f, 'v) trs \<Rightarrow> ('f, 'v) rule \<Rightarrow> pos \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) trs" where
  "rstep_r_p_s R r p \<sigma> = {(s, t). p \<in> poss s \<and> p \<in> poss t \<and> r \<in> R \<and> ctxt_at_pos s p = ctxt_at_pos t p \<and>
     s[p \<leftarrow> (fst r \<cdot> \<sigma>)] = s \<and> t[p \<leftarrow> (snd r \<cdot> \<sigma>)] = t}"

text \<open>Rewriting steps below the root position.\<close>
definition nrrstep :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs" where
  "nrrstep R = {(s,t). \<exists>r i ps \<sigma>. (s,t) \<in> rstep_r_p_s R r (i#ps) \<sigma>}"

text \<open>Rewriting step at the root position.\<close>
definition rrstep :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs" where
  "rrstep R = {(s,t). \<exists>r \<sigma>. (s,t) \<in> rstep_r_p_s R r [] \<sigma>}"

text \<open>the parallel rewrite relation\<close>
inductive_set par_rstep :: "('f,'v)trs \<Rightarrow> ('f,'v)trs" for R :: "('f,'v)trs"
  where root_step[intro]: "(s,t) \<in> R \<Longrightarrow> (s \<cdot> \<sigma>,t \<cdot> \<sigma>) \<in> par_rstep R"
     |  par_step_fun[intro]: "\<lbrakk>\<And> i. i < length ts \<Longrightarrow> (ss ! i,ts ! i) \<in> par_rstep R\<rbrakk> \<Longrightarrow> length ss = length ts
             \<Longrightarrow> (Fun f ss, Fun f ts) \<in> par_rstep R"
     |  par_step_var[intro]: "(Var x, Var x) \<in> par_rstep R"


subsection \<open>Ground variants connecting to FORT\<close>

definition grrstep :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "grrstep \<R> = inv_image (rrstep \<R>) term_of_gterm"

definition gnrrstep :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "gnrrstep \<R> = inv_image (nrrstep \<R>) term_of_gterm"

definition grstep :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "grstep \<R> = inv_image (rstep \<R>) term_of_gterm"

definition gpar_rstep :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "gpar_rstep \<R> = inv_image (par_rstep \<R>) term_of_gterm"


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

lemma nrrstep_def':
  "nrrstep R = {(s, t). \<exists>l r C \<sigma>. (l, r) \<in> R \<and> C \<noteq> \<box> \<and> s = C\<langle>l\<cdot>\<sigma>\<rangle> \<and> t = C\<langle>r\<cdot>\<sigma>\<rangle>}" (is "?Ls = ?Rs")
proof
  show "?Ls \<subseteq> ?Rs"
  proof (rule subrelI)
    fix s t assume "(s, t) \<in> ?Ls"
    then obtain l r i ps \<sigma> where step: "(s, t) \<in> rstep_r_p_s R (l, r) (i # ps) \<sigma>"
          unfolding nrrstep_def by best
    let ?C = "ctxt_at_pos s (i # ps)"
    from step have"i # ps \<in> poss s" and "(l, r) \<in> R" and "s = ?C\<langle>l\<cdot>\<sigma>\<rangle>" and "t = ?C\<langle>r\<cdot>\<sigma>\<rangle>"
      unfolding rstep_r_p_s_def Let_def by (auto simp flip: replace_term_at_replace_at_conv)
    moreover from \<open>i # ps \<in> poss s\<close> have "?C \<noteq> \<box>" by (induct s) auto
    ultimately show "(s, t) \<in> ?Rs" by auto
  qed
next
  show "?Rs \<subseteq> ?Ls"
  proof (rule subrelI)
    fix s t assume "(s, t) \<in> ?Rs"
    then obtain l r C \<sigma> where in_R: "(l, r) \<in> R" and "C \<noteq> \<box>"
      and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
    from \<open>C \<noteq> \<box>\<close> obtain i p where ip: "hole_pos C = i # p" by (induct C) auto
    have "i # p \<in> poss s" unfolding s ip[symmetric] by simp
    then have C: "C = ctxt_at_pos s (i # p) "
      unfolding s ip[symmetric] by simp
    from \<open>i # p \<in> poss s\<close> in_R s t have "(s, t) \<in> rstep_r_p_s R (l, r) (i # p) \<sigma>"
      unfolding rstep_r_p_s_def C[symmetric] ip[symmetric] by simp
    then show "(s, t) \<in> nrrstep R" unfolding nrrstep_def by best
  qed
qed

lemma rrstep_def': "rrstep R = {(s, t). \<exists>l r \<sigma>. (l, r) \<in> R \<and> s = l\<cdot>\<sigma> \<and> t = r\<cdot>\<sigma>}"
  by (auto simp: rrstep_def rstep_r_p_s_def)


lemma rstep_imp_C_s_r:
  assumes "(s,t) \<in> rstep R"
  shows "\<exists>C \<sigma> l r. (l,r) \<in> R \<and> s = C\<langle>l\<cdot>\<sigma>\<rangle> \<and> t = C\<langle>r\<cdot>\<sigma>\<rangle>" using assms
  by (induct) auto

lemma rhs_wf:
  assumes R: "(l, r) \<in> R" and "funas_trs R \<subseteq> F"
  shows "funas_term r \<subseteq> F"
  using assms by (force simp: funas_trs_def)

abbreviation "linear_sys \<R> \<equiv> (\<forall> (l, r) \<in> \<R>. linear_term l \<and> linear_term r)"
abbreviation "const_subt c \<equiv> \<lambda> x. Fun c []"



end