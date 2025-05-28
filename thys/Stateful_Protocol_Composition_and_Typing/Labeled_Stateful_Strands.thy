(*  Title:      Labeled_Stateful_Strands.thy
    Author:     Andreas Viktor Hess, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section \<open>Labeled Stateful Strands\<close>
theory Labeled_Stateful_Strands
imports Stateful_Strands Labeled_Strands
begin

subsection \<open>Definitions\<close>
text\<open>Syntax for stateful strand labels\<close>
abbreviation Star_step (\<open>\<langle>\<star>, _\<rangle>\<close>) where
  "\<langle>\<star>, (s::('a,'b) stateful_strand_step)\<rangle> \<equiv> (\<star>, s)"

abbreviation LabelN_step (\<open>\<langle>_, _\<rangle>\<close>) where
  "\<langle>(l::'a), (s::('b,'c) stateful_strand_step)\<rangle> \<equiv> (ln l, s)"


text\<open>Database projection\<close>
definition dbproj where "dbproj l D \<equiv> filter (\<lambda>d. fst d = l) D"

text\<open>The type of labeled stateful strands\<close>
type_synonym ('a,'b,'c) labeled_stateful_strand_step = "'c strand_label \<times> ('a,'b) stateful_strand_step"
type_synonym ('a,'b,'c) labeled_stateful_strand = "('a,'b,'c) labeled_stateful_strand_step list"

text\<open>Dual strands\<close>
fun dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p::"('a,'b,'c) labeled_stateful_strand_step \<Rightarrow> ('a,'b,'c) labeled_stateful_strand_step"
where
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l,send\<langle>t\<rangle>) = (l,receive\<langle>t\<rangle>)"
| "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l,receive\<langle>t\<rangle>) = (l,send\<langle>t\<rangle>)"
| "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p x = x"

definition dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t::"('a,'b,'c) labeled_stateful_strand \<Rightarrow> ('a,'b,'c) labeled_stateful_strand"
where
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<equiv> map dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p"

text\<open>Substitution application\<close>
fun subst_apply_labeled_stateful_strand_step::
  "('a,'b,'c) labeled_stateful_strand_step \<Rightarrow> ('a,'b) subst \<Rightarrow>
   ('a,'b,'c) labeled_stateful_strand_step"
  (infix \<open>\<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p\<close> 51) where
  "(l,s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>  = (l,s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)"

definition subst_apply_labeled_stateful_strand::
  "('a,'b,'c) labeled_stateful_strand \<Rightarrow> ('a,'b) subst \<Rightarrow> ('a,'b,'c) labeled_stateful_strand"
  (infix \<open>\<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<close> 51) where
  "S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta> \<equiv> map (\<lambda>x. x \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) S"

text\<open>Definitions lifted from stateful strands\<close>
abbreviation wfrestrictedvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "wfrestrictedvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> wfrestrictedvars\<^sub>s\<^sub>s\<^sub>t (unlabel S)"

abbreviation ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> ik\<^sub>s\<^sub>s\<^sub>t (unlabel S)"

abbreviation db\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> db\<^sub>s\<^sub>s\<^sub>t (unlabel S)"
abbreviation db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> db'\<^sub>s\<^sub>s\<^sub>t (unlabel S)"

abbreviation trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> trms\<^sub>s\<^sub>s\<^sub>t (unlabel S)"
abbreviation trms_proj\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "trms_proj\<^sub>l\<^sub>s\<^sub>s\<^sub>t n S \<equiv> trms\<^sub>s\<^sub>s\<^sub>t (proj_unl n S)"

abbreviation vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> vars\<^sub>s\<^sub>s\<^sub>t (unlabel S)"
abbreviation vars_proj\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "vars_proj\<^sub>l\<^sub>s\<^sub>s\<^sub>t n S \<equiv> vars\<^sub>s\<^sub>s\<^sub>t (proj_unl n S)"

abbreviation bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel S)"
abbreviation fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t where "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> fv\<^sub>s\<^sub>s\<^sub>t (unlabel S)"

text\<open>Labeled set-operations\<close>
fun setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p where
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,insert\<langle>t,s\<rangle>) = {(i,t,s)}"
| "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,delete\<langle>t,s\<rangle>) = {(i,t,s)}"
| "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,\<langle>_: t \<in> s\<rangle>) = {(i,t,s)}"
| "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (i,\<forall>_\<langle>\<or>\<noteq>: _ \<or>\<notin>: F'\<rangle>) = ((\<lambda>(t,s). (i,t,s)) ` set F')"
| "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p _ = {}"

definition setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t where
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<equiv> \<Union>(setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ` set S)"


subsection \<open>Minor Lemmata\<close>
lemma in_ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t_iff: "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<longleftrightarrow> (\<exists>l ts. (l,receive\<langle>ts\<rangle>) \<in> set A \<and> t \<in> set ts)"
unfolding unlabel_def ik\<^sub>s\<^sub>s\<^sub>t_def by force

lemma ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t_concat: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (concat xs) = \<Union>(ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ` set xs)"
by (induct xs) auto

lemma ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t_Cons[simp]:
  "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,send\<langle>ts\<rangle>)#A) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?A)
  "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,receive\<langle>ts\<rangle>)#A) = set ts \<union> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?B)
  "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,\<langle>ac: t \<doteq> s\<rangle>)#A) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?C)
  "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,insert\<langle>t,s\<rangle>)#A) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?D)
  "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,delete\<langle>t,s\<rangle>)#A) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?E)
  "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,\<langle>ac: t \<in> s\<rangle>)#A) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?F)
  "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>)#A) = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" (is ?G)
proof -
  note 0 = ik\<^sub>s\<^sub>s\<^sub>t_append[of _ "unlabel A"]
  note 1 = in_ik\<^sub>s\<^sub>s\<^sub>t_iff
  show ?A using 0[of "[send\<langle>ts\<rangle>]"] 1[of _ "[send\<langle>ts\<rangle>]"] by auto
  show ?B using 0[of "[receive\<langle>ts\<rangle>]"] 1[of _ "[receive\<langle>ts\<rangle>]"] by auto
  show ?C using 0[of "[\<langle>ac: t \<doteq> s\<rangle>]"] 1[of _ "[\<langle>ac: t \<doteq> s\<rangle>]"] by auto
  show ?D using 0[of "[insert\<langle>t,s\<rangle>]"] 1[of _ "[insert\<langle>t,s\<rangle>]"] by auto
  show ?E using 0[of "[delete\<langle>t,s\<rangle>]"] 1[of _ "[delete\<langle>t,s\<rangle>]"] by auto
  show ?F using 0[of "[\<langle>ac: t \<in> s\<rangle>]"] 1[of _ "[\<langle>ac: t \<in> s\<rangle>]"] by auto
  show ?G using 0[of "[\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>]"] 1[of _ "[\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>]"] by auto
qed

lemma subst_lsstp_fst_eq:
  "fst (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = fst a"
by (cases a) auto

lemma subst_lsst_map_fst_eq:
  "map fst (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = map fst S"
using subst_lsstp_fst_eq unfolding subst_apply_labeled_stateful_strand_def by auto

lemma subst_lsst_nil[simp]: "[] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = []"
by (simp add: subst_apply_labeled_stateful_strand_def)

lemma subst_lsst_cons: "a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)#(A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
by (simp add: subst_apply_labeled_stateful_strand_def)

lemma subst_lsstp_id_subst: "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p Var = a"
proof -
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  show ?thesis unfolding a by (cases b) auto
qed

lemma subst_lsst_id_subst: "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t Var = A"
by (induct A) (simp, metis subst_lsstp_id_subst subst_lsst_cons)

lemma subst_lsst_singleton: "[(l,s)] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = [(l,s \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)]"
by (simp add: subst_apply_labeled_stateful_strand_def)

lemma subst_lsst_append: "A@B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)@(B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
by (simp add: subst_apply_labeled_stateful_strand_def)

lemma subst_lsst_append_inv:
  assumes "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = B1@B2"
  shows "\<exists>A1 A2. A = A1@A2 \<and> A1 \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = B1 \<and> A2 \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = B2"
using assms
proof (induction A arbitrary: B1 B2)
  case (Cons a A)
  note prems = Cons.prems
  note IH = Cons.IH
  show ?case
  proof (cases B1)
    case Nil
    then obtain b B3 where "B2 = b#B3" "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> = b" "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = B3"
      using prems subst_lsst_cons by fastforce
    thus ?thesis by (simp add: Nil subst_apply_labeled_stateful_strand_def)
  next
    case (Cons b B3)
    hence "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> = b" "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> = B3@B2"
      using prems by (simp_all add: subst_lsst_cons)
    thus ?thesis by (metis Cons_eq_appendI Cons IH subst_lsst_cons) 
  qed
qed (metis append_is_Nil_conv subst_lsst_nil)

lemma subst_lsst_memI[intro]: "x \<in> set A \<Longrightarrow> x \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<in> set (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
by (metis image_eqI set_map subst_apply_labeled_stateful_strand_def)

lemma subst_lsstpD:
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,send\<langle>ts\<rangle>) \<Longrightarrow> \<exists>ts'. ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma> \<and> a = (n,send\<langle>ts'\<rangle>)"
    (is "?A \<Longrightarrow> ?A'")
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,receive\<langle>ts\<rangle>) \<Longrightarrow> \<exists>ts'. ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma> \<and> a = (n,receive\<langle>ts'\<rangle>)"
    (is "?B \<Longrightarrow> ?B'")
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,\<langle>c: t \<doteq> s\<rangle>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = (n,\<langle>c: t' \<doteq> s'\<rangle>)"
    (is "?C \<Longrightarrow> ?C'")
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,insert\<langle>t,s\<rangle>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = (n,insert\<langle>t',s'\<rangle>)"
    (is "?D \<Longrightarrow> ?D'")
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,delete\<langle>t,s\<rangle>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = (n,delete\<langle>t',s'\<rangle>)"
    (is "?E \<Longrightarrow> ?E'")
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,\<langle>c: t \<in> s\<rangle>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = (n,\<langle>c: t' \<in> s'\<rangle>)"
    (is "?F \<Longrightarrow> ?F'")
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<Longrightarrow>
    \<exists>F' G'. F = F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<sigma> \<and> G = G' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<sigma> \<and>
            a = (n,\<forall>X\<langle>\<or>\<noteq>: F' \<or>\<notin>: G'\<rangle>)"
    (is "?G \<Longrightarrow> ?G'")
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,\<langle>t != s\<rangle>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = (n,\<langle>t' != s'\<rangle>)"
    (is "?H \<Longrightarrow> ?H'")
  "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma> = (n,\<langle>t not in s\<rangle>) \<Longrightarrow> \<exists>t' s'. t = t' \<cdot> \<sigma> \<and> s = s' \<cdot> \<sigma> \<and> a = (n,\<langle>t' not in s'\<rangle>)"
    (is "?I \<Longrightarrow> ?I'")
proof -
  obtain m b where a: "a = (m,b)" by (metis surj_pair)
  show "?A \<Longrightarrow> ?A'" "?B \<Longrightarrow> ?B'" "?C \<Longrightarrow> ?C'" "?D \<Longrightarrow> ?D'" "?E \<Longrightarrow> ?E'" "?F \<Longrightarrow> ?F'" "?G \<Longrightarrow> ?G'"
       "?H \<Longrightarrow> ?H'" "?I \<Longrightarrow> ?I'"
    by (cases b; auto simp add: a subst_apply_pairs_def; fail)+
qed

lemma subst_lsst_memD:
  "(n,receive\<langle>ts\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>us. (n,receive\<langle>us\<rangle>) \<in> set S \<and> ts = us \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>"
  "(n,send\<langle>ts\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>us. (n,send\<langle>us\<rangle>) \<in> set S \<and> ts = us \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>"
  "(n,\<langle>ac: t \<doteq> s\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>u v. (n,\<langle>ac: u \<doteq> v\<rangle>) \<in> set S \<and> t = u \<cdot> \<sigma> \<and> s = v \<cdot> \<sigma>"
  "(n,insert\<langle>t, s\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>u v. (n,insert\<langle>u, v\<rangle>) \<in> set S \<and> t = u \<cdot> \<sigma> \<and> s = v \<cdot> \<sigma>"
  "(n,delete\<langle>t, s\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>u v. (n,delete\<langle>u, v\<rangle>) \<in> set S \<and> t = u \<cdot> \<sigma> \<and> s = v \<cdot> \<sigma>"
  "(n,\<langle>ac: t \<in> s\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>u v. (n,\<langle>ac: u \<in> v\<rangle>) \<in> set S \<and> t = u \<cdot> \<sigma> \<and> s = v \<cdot> \<sigma>"
  "(n,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>F' G'. (n,\<forall>X\<langle>\<or>\<noteq>: F' \<or>\<notin>: G'\<rangle>) \<in> set S \<and>
            F = F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<sigma> \<and>
            G = G' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<sigma>"
  "(n,\<langle>t != s\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>u v. (n,\<langle>u != v\<rangle>) \<in> set S \<and> t = u \<cdot> \<sigma> \<and> s = v \<cdot> \<sigma>"
  "(n,\<langle>t not in s\<rangle>) \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) \<Longrightarrow>
    \<exists>u v. (n,\<langle>u not in v\<rangle>) \<in> set S \<and> t = u \<cdot> \<sigma> \<and> s = v \<cdot> \<sigma>"
proof (induction S)
  case (Cons b S)
  obtain m a where a: "b = (m,a)" by (metis surj_pair)
  have *: "x \<in> set (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>)"
    when "x \<in> set (b#S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>)" "x \<noteq> b \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>" for x
    using that by (simp add: subst_apply_labeled_stateful_strand_def)

  { case 1 thus ?case using Cons.IH(1)[OF *] a by (cases a) auto }
  { case 2 thus ?case using Cons.IH(2)[OF *] a by (cases a) auto }
  { case 3 thus ?case using Cons.IH(3)[OF *] a by (cases a) auto }
  { case 4 thus ?case using Cons.IH(4)[OF *] a by (cases a) auto }
  { case 5 thus ?case using Cons.IH(5)[OF *] a by (cases a) auto }
  { case 6 thus ?case using Cons.IH(6)[OF *] a by (cases a) auto }
  { case 7 thus ?case using Cons.IH(7)[OF *] a by (cases a) auto }
  { case 8 show ?case
    proof (cases a)
      case (NegChecks Y F' G') thus ?thesis
      proof (cases "(n,\<langle>t != s\<rangle>) = b \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>")
        case True thus ?thesis using subst_lsstpD(8)[of b \<sigma> n t s] by auto
      qed (use 8 Cons.IH(8)[OF *] a in auto)
    qed (use 8 Cons.IH(8)[OF *] a in simp_all)
  }
  { case 9 show ?case
    proof (cases a)
      case (NegChecks Y F' G') thus ?thesis
      proof (cases "(n,\<langle>t not in s\<rangle>) = b \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>")
        case True thus ?thesis using subst_lsstpD(9)[of b \<sigma> n t s] by auto
      qed (use 9 Cons.IH(9)[OF *] a in auto)
    qed (use 9 Cons.IH(9)[OF *] a in simp_all)
  }
qed simp_all

lemma subst_lsst_unlabel_cons: "unlabel ((l,b)#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>)#(unlabel (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"
by (simp add: subst_apply_labeled_stateful_strand_def)

lemma subst_lsst_unlabel: "unlabel (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = unlabel A \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>"
proof (induction A)
  case (Cons a A)
  then obtain l b where "a = (l,b)" by (metis surj_pair)
  thus ?case
    using Cons
    by (simp add: subst_apply_labeled_stateful_strand_def subst_apply_stateful_strand_def)
qed simp

lemma subst_lsst_unlabel_member[intro]:
  assumes "x \<in> set (unlabel A)"
  shows "x \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<in> set (unlabel (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>))"
proof -
  obtain l where x: "(l,x) \<in> set A" using assms unfolding unlabel_def by atomize_elim auto
  thus ?thesis
    using subst_lsst_memI
    by (metis unlabel_def in_set_zipE subst_apply_labeled_stateful_strand_step.simps zip_map_fst_snd)
qed

lemma subst_lsst_prefix:
  assumes "prefix B (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
  shows "\<exists>C. C \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta> = B \<and> prefix C A"
using assms
proof (induction A rule: List.rev_induct)
  case (snoc a A) thus ?case
  proof (cases "B = A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>")
    case False thus ?thesis
      using snoc by (auto simp add: subst_lsst_append[of A] subst_lsst_cons)
  qed auto
qed simp

lemma subst_lsst_tl:
  "tl (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = tl S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"
by (metis map_tl subst_apply_labeled_stateful_strand_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_tl:
  "tl (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (tl S)"
by (metis map_tl dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_fst_eq:
  "fst (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a) = fst a"
proof -
  obtain l b where "a = (l,b)" by (metis surj_pair)
  thus ?thesis by (cases b) auto
qed

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_map_fst_eq:
  "map fst (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) = map fst S"
using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_fst_eq unfolding dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_nil[simp]: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t [] = []"
by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_Cons[simp]:
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,send\<langle>ts\<rangle>)#A) = (l,receive\<langle>ts\<rangle>)#(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,receive\<langle>ts\<rangle>)#A) = (l,send\<langle>ts\<rangle>)#(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,\<langle>a: t \<doteq> s\<rangle>)#A) = (l,\<langle>a: t \<doteq> s\<rangle>)#(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,insert\<langle>t,s\<rangle>)#A) = (l,insert\<langle>t,s\<rangle>)#(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,delete\<langle>t,s\<rangle>)#A) = (l,delete\<langle>t,s\<rangle>)#(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,\<langle>a: t \<in> s\<rangle>)#A) = (l,\<langle>a: t \<in> s\<rangle>)#(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>)#A) = (l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>)#(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
by (simp_all add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append[simp]: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t B"
by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (s \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p s) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>"
proof -
  obtain l x  where s: "s = (l,x)" by atomize_elim auto
  thus ?thesis by (cases x) (auto simp add: subst_apply_labeled_stateful_strand_def)
qed

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"
proof (induction S)
  case (Cons s S) thus ?case
    using Cons dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst[of s \<delta>]
    by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def subst_apply_labeled_stateful_strand_def)
qed (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def subst_apply_labeled_stateful_strand_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_unlabel: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)) = unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta>" 
by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst subst_lsst_unlabel)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_cons: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) = (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>)#(dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>))"
by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst list.simps(9) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def subst_apply_labeled_stateful_strand_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_append: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) = (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t B) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>"
by (metis (no_types) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_snoc: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>) = (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>)@[dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>]"
by (metis dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_cons list.map(1) map_append
          subst_apply_labeled_stateful_strand_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_memberD:
  assumes "(l,a) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  shows "\<exists>b. (l,b) \<in> set A \<and> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l,b) = (l,a)"
  using assms
proof (induction A)
  case (Cons c A)
  hence "(l,a) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<or> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p c = (l,a)" unfolding dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by force
  thus ?case
  proof
    assume "(l,a) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" thus ?case using Cons.IH by auto
  next
    assume a: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p c = (l,a)"
    obtain i b where b: "c = (i,b)" by (metis surj_pair)
    thus ?case using a by (cases b) auto
  qed
qed simp

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_memberD':
  assumes a: "a \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  obtains b where "b \<in> set A" "a = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" "fst a = fst b"
proof -
  obtain l a' where a': "a = (l,a')" by (metis surj_pair)
  then obtain b' where b': "(l,b') \<in> set A" "(l,a') = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,b') \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
    using a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst[of A \<delta>] dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_memberD[of l a' "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"]
    unfolding subst_apply_labeled_stateful_strand_def by auto

  show thesis
    using that[OF b'(1) b'(2)[unfolded dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst[of "(l,b')" \<delta>] a'[symmetric]], unfolded a']
    by auto
qed

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_inv:
  assumes "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l, a) = (k, b)"
  shows "l = k"
    and "a = receive\<langle>t\<rangle> \<Longrightarrow> b = send\<langle>t\<rangle>"
    and "a = send\<langle>t\<rangle> \<Longrightarrow> b = receive\<langle>t\<rangle>"
    and "(\<nexists>t. a = receive\<langle>t\<rangle> \<or> a = send\<langle>t\<rangle>) \<Longrightarrow> b = a"
proof -
  show "l = k" using assms by (cases a) auto
  show "a = receive\<langle>t\<rangle> \<Longrightarrow> b = send\<langle>t\<rangle>" using assms by (cases a) auto
  show "a = send\<langle>t\<rangle> \<Longrightarrow> b = receive\<langle>t\<rangle>" using assms by (cases a) auto
  show "(\<nexists>t. a = receive\<langle>t\<rangle> \<or> a = send\<langle>t\<rangle>) \<Longrightarrow> b = a" using assms by (cases a) auto
qed

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_self_inverse: "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = A"
proof (induction A)
  case (Cons a A)
  obtain l b where "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons by (cases b) auto
qed simp

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_cong:
  assumes "unlabel S = unlabel S'"
  shows "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) = unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S')"
using assms
proof (induction S arbitrary: S')
  case (Cons x S S')
  obtain y S'' where y: "S' = y#S''" using Cons.prems unfolding unlabel_def by force
  hence IH: "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) = unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S'')" using Cons by (simp add: unlabel_def)

  have "snd x = snd y" using Cons y by simp
  then obtain lx ly a where a: "x = (lx,a)" "y = (ly,a)" by (metis prod.exhaust_sel)

  have "snd (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p x) = snd (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p y)" unfolding a by (cases a) simp_all
  thus ?case using IH unfolding unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def y by force
qed (simp add: unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma vars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq: "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof (induction A)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons.IH by (cases b) auto
qed simp

lemma fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq: "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof (induction A)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons.IH by (cases b) auto
qed simp

lemma bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof (induction A)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons.IH by (cases b) simp+
qed simp

lemma vars\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons: "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,b)#A) = vars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<union> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
by (metis unlabel_Cons(1) vars\<^sub>s\<^sub>s\<^sub>t_Cons)

lemma fv\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons: "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,b)#A) = fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
by (metis unlabel_Cons(1) fv\<^sub>s\<^sub>s\<^sub>t_Cons)

lemma bvars\<^sub>s\<^sub>s\<^sub>t_unlabel_Cons: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,b)#A) = set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p b) \<union> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
by (metis unlabel_Cons(1) bvars\<^sub>s\<^sub>s\<^sub>t_Cons)

lemma bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
by (metis subst_lsst_unlabel bvars\<^sub>s\<^sub>s\<^sub>t_subst)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_member:
  assumes "(l,x) \<in> set A"
    and "\<not>is_Receive x" "\<not>is_Send x"
  shows "(l,x) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
using assms
proof (induction A)
  case (Cons a A) thus ?case using assms(2,3) by (cases x) (auto simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)
qed simp

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_member:
  assumes "x \<in> set (unlabel A)"
    and "\<not>is_Receive x" "\<not>is_Send x"
  shows "x \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
using assms dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_member[of _ _ A]
  by (meson unlabel_in unlabel_mem_has_label)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff:
  "(l,send\<langle>ts\<rangle>) \<in> set A \<longleftrightarrow> (l,receive\<langle>ts\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "(l,receive\<langle>ts\<rangle>) \<in> set A \<longleftrightarrow> (l,send\<langle>ts\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "(l,\<langle>c: t \<doteq> s\<rangle>) \<in> set A \<longleftrightarrow> (l,\<langle>c: t \<doteq> s\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "(l,insert\<langle>t,s\<rangle>) \<in> set A \<longleftrightarrow> (l,insert\<langle>t,s\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "(l,delete\<langle>t,s\<rangle>) \<in> set A \<longleftrightarrow> (l,delete\<langle>t,s\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "(l,\<langle>c: t \<in> s\<rangle>) \<in> set A \<longleftrightarrow> (l,\<langle>c: t \<in> s\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
  "(l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<in> set A \<longleftrightarrow> (l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle>) \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
proof (induction A)
  case (Cons a A)
  obtain j b where a: "a = (j,b)" by (metis surj_pair)
  { case 1 thus ?case by (cases b) (simp_all add: Cons.IH(1) a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 2 thus ?case by (cases b) (simp_all add: Cons.IH(2) a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 3 thus ?case by (cases b) (simp_all add: Cons.IH(3) a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 4 thus ?case by (cases b) (simp_all add: Cons.IH(4) a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 5 thus ?case by (cases b) (simp_all add: Cons.IH(5) a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 6 thus ?case by (cases b) (simp_all add: Cons.IH(6) a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 7 thus ?case by (cases b) (simp_all add: Cons.IH(7) a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def) }
qed (simp_all add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff:
  "send\<langle>ts\<rangle> \<in> set (unlabel A) \<longleftrightarrow> receive\<langle>ts\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "receive\<langle>ts\<rangle> \<in> set (unlabel A) \<longleftrightarrow> send\<langle>ts\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "\<langle>c: t \<doteq> s\<rangle> \<in> set (unlabel A) \<longleftrightarrow> \<langle>c: t \<doteq> s\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "insert\<langle>t,s\<rangle> \<in> set (unlabel A) \<longleftrightarrow> insert\<langle>t,s\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "delete\<langle>t,s\<rangle> \<in> set (unlabel A) \<longleftrightarrow> delete\<langle>t,s\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "\<langle>c: t \<in> s\<rangle> \<in> set (unlabel A) \<longleftrightarrow> \<langle>c: t \<in> s\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set (unlabel A) \<longleftrightarrow> \<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: G\<rangle> \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(1,2)[of _ ts A]
      dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(3,6)[of _ c t s A]
      dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(4,5)[of _ t s A]
      dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(7)[of _ X F G A]
by (meson unlabel_in unlabel_mem_has_label)+

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all:
  "list_all is_Receive (unlabel A) \<longleftrightarrow> list_all is_Send (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_Send (unlabel A) \<longleftrightarrow> list_all is_Receive (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_Equality (unlabel A) \<longleftrightarrow> list_all is_Equality (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_Insert (unlabel A) \<longleftrightarrow> list_all is_Insert (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_Delete (unlabel A) \<longleftrightarrow> list_all is_Delete (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_InSet (unlabel A) \<longleftrightarrow> list_all is_InSet (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_NegChecks (unlabel A) \<longleftrightarrow> list_all is_NegChecks (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_Assignment (unlabel A) \<longleftrightarrow> list_all is_Assignment (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_Check (unlabel A) \<longleftrightarrow> list_all is_Check (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_Update (unlabel A) \<longleftrightarrow> list_all is_Update (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  "list_all is_Check_or_Assignment (unlabel A) \<longleftrightarrow>
    list_all is_Check_or_Assignment (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
proof (induct A)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  { case 1 thus ?case using Cons.hyps(1) a by (cases b) auto }
  { case 2 thus ?case using Cons.hyps(2) a by (cases b) auto }
  { case 3 thus ?case using Cons.hyps(3) a by (cases b) auto }
  { case 4 thus ?case using Cons.hyps(4) a by (cases b) auto }
  { case 5 thus ?case using Cons.hyps(5) a by (cases b) auto }
  { case 6 thus ?case using Cons.hyps(6) a by (cases b) auto }
  { case 7 thus ?case using Cons.hyps(7) a by (cases b) auto }
  { case 8 thus ?case using Cons.hyps(8) a by (cases b) auto }
  { case 9 thus ?case using Cons.hyps(9) a by (cases b) auto }
  { case 10 thus ?case using Cons.hyps(10) a by (cases b) auto }
  { case 11 thus ?case using Cons.hyps(11) a by (cases b) auto }
qed simp_all

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_list_all_same:
  "list_all is_Equality (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
  "list_all is_Insert (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
  "list_all is_Delete (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
  "list_all is_InSet (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
  "list_all is_NegChecks (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
  "list_all is_Assignment (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
  "list_all is_Check (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
  "list_all is_Update (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
  "list_all is_Check_or_Assignment (unlabel A) \<Longrightarrow> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A = A"
proof (induct A)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  { case 1 thus ?case using Cons.hyps(1) a by (cases b) auto }
  { case 2 thus ?case using Cons.hyps(2) a by (cases b) auto }
  { case 3 thus ?case using Cons.hyps(3) a by (cases b) auto }
  { case 4 thus ?case using Cons.hyps(4) a by (cases b) auto }
  { case 5 thus ?case using Cons.hyps(5) a by (cases b) auto }
  { case 6 thus ?case using Cons.hyps(6) a by (cases b) auto }
  { case 7 thus ?case using Cons.hyps(7) a by (cases b) auto }
  { case 8 thus ?case using Cons.hyps(8) a by (cases b) auto }
  { case 9 thus ?case using Cons.hyps(9) a by (cases b) auto }
qed simp_all

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_set_prefix_obtain:
  assumes "s \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))"
  shows "\<exists>l B s'. (l,s) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l,s') \<and> prefix (B@[(l,s')]) A"
  using assms
proof (induction A rule: List.rev_induct)
  case (snoc a A)
  obtain i b where a: "a = (i,b)" by (metis surj_pair)
  show ?case using snoc
  proof (cases "s \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A))")
    case False thus ?thesis
      using a snoc.prems unlabel_append[of "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t [a]"] dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_append[of A "[a]"]
      by (cases b) (force simp add: unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)+
  qed auto
qed simp

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_set_prefix_obtain_subst:
  assumes "s \<in> set (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
  shows "\<exists>l B s'. (l,s) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,s') \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) \<and> prefix ((B \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)@[(l,s') \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]) (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
proof -
  obtain B l s' where B: "(l,s) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (l,s')" "prefix (B@[(l,s')]) (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)"
    using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_set_prefix_obtain[OF assms] by atomize_elim auto

  obtain C where C: "C \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta> = B@[(l,s')]"
    using subst_lsst_prefix[OF B(2)] by atomize_elim auto

  obtain D u where D: "C = D@[(l,u)]" "D \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta> = B" "[(l,u)] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta> = [(l, s')]"
    using subst_lsst_prefix[OF B(2)] subst_lsst_append_inv[OF C(1)]
    by (auto simp add: subst_apply_labeled_stateful_strand_def)

  show ?thesis 
    using B D subst_lsst_cons subst_lsst_singleton
    by (metis (no_types, lifting) nth_append_length)
qed

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq: "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof (induction A)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons.IH by (cases b) auto
qed simp

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst_cons:
  "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ((l,b)#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<union> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
by (metis subst_lsst_unlabel trms\<^sub>s\<^sub>s\<^sub>t_subst_cons unlabel_Cons(1))

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst:
  assumes "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<theta> = {}"
  shows "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
by (metis trms\<^sub>s\<^sub>s\<^sub>t_subst[OF assms] subst_lsst_unlabel)

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst':
  fixes t::"('a,'b) term" and \<delta>::"('a,'b) subst"
  assumes "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  shows "\<exists>s \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S. \<exists>X. set X \<subseteq> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<and> t = s \<cdot> rm_vars (set X) \<delta>"
using assms
proof (induction S)
  case (Cons a S)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  hence "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) \<or> t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)" 
    using Cons.prems trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst_cons by fast
  thus ?case
  proof
    assume *: "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (b \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
    show ?thesis using trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst''[OF *] a by auto
  next
    assume *: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
    show ?thesis using Cons.IH[OF *] a by auto
  qed
qed simp

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst'':
  fixes t::"('a,'b) term" and \<delta> \<theta>::"('a,'b) subst"
  assumes "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
  shows "\<exists>s \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S. \<exists>X. set X \<subseteq> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<and> t = s \<cdot> rm_vars (set X) \<delta> \<circ>\<^sub>s \<theta>"
proof -
  obtain s where s: "s \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)" "t = s \<cdot> \<theta>" using assms by atomize_elim auto
  show ?thesis using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst'[OF s(1)] s(2) by auto
qed

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual_subst_cons:
  "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>)) = (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<sigma>)) \<union> (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>)))"
proof -
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  thus ?thesis using a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_cons[of a A \<sigma>] by (cases b) auto
qed

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_funs_term:
  "\<Union>(funs_term ` (trms\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t S)))) = \<Union>(funs_term ` (trms\<^sub>s\<^sub>s\<^sub>t (unlabel S)))"
using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq by fast

lemma dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_db\<^sub>l\<^sub>s\<^sub>s\<^sub>t:
  "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof (induction A)
  case (Cons a A)
  obtain l b where a: "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons by (cases b) auto
qed simp

lemma db\<^sub>s\<^sub>s\<^sub>t_unlabel_append:
  "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) I D = db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t B I (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I D)"
by (metis db\<^sub>s\<^sub>s\<^sub>t_append unlabel_append)

lemma db\<^sub>s\<^sub>s\<^sub>t_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t:
  "db'\<^sub>s\<^sub>s\<^sub>t (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>))) \<I> D = db'\<^sub>s\<^sub>s\<^sub>t (unlabel (T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)) \<I> D"
proof (induction T arbitrary: D)
  case (Cons x T)
  obtain l s where "x = (l,s)" by atomize_elim auto
  thus ?case
    using Cons
    by (cases s) (simp_all add: unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def subst_apply_labeled_stateful_strand_def)  
qed (simp add: unlabel_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def subst_apply_labeled_stateful_strand_def)

lemma labeled_list_insert_eq_cases:
  "d \<notin> set (unlabel D) \<Longrightarrow> List.insert d (unlabel D) = unlabel (List.insert (i,d) D)"
  "(i,d) \<in> set D \<Longrightarrow> List.insert d (unlabel D) = unlabel (List.insert (i,d) D)"
unfolding unlabel_def
by (metis (no_types, opaque_lifting) List.insert_def image_eqI list.simps(9) set_map snd_conv,
    metis in_set_insert set_zip_rightD zip_map_fst_snd)

lemma labeled_list_insert_eq_ex_cases:
  "List.insert d (unlabel D) = unlabel (List.insert (i,d) D) \<or>
  (\<exists>j. (j,d) \<in> set D \<and> List.insert d (unlabel D) = unlabel (List.insert (j,d) D))"
using labeled_list_insert_eq_cases unfolding unlabel_def
by (metis in_set_impl_in_set_zip2 length_map zip_map_fst_snd)

lemma in_proj_set:
  assumes "\<langle>l,r\<rangle> \<in> set A"
  shows "\<langle>l,r\<rangle> \<in> set (proj l A)"
using assms unfolding proj_def by force

lemma proj_subst: "proj l (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) = proj l A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"
proof (induction A)
  case (Cons a A)
  obtain l b where "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons unfolding proj_def subst_apply_labeled_stateful_strand_def by force
qed simp 

lemma proj_set_subset[simp]:
  "set (proj n A) \<subseteq> set A"
unfolding proj_def by auto

lemma proj_proj_set_subset[simp]:
  "set (proj n (proj m A)) \<subseteq> set (proj n A)"
  "set (proj n (proj m A)) \<subseteq> set (proj m A)"
  "set (proj_unl n (proj m A)) \<subseteq> set (proj_unl n A)"
  "set (proj_unl n (proj m A)) \<subseteq> set (proj_unl m A)"
unfolding unlabel_def proj_def by auto

lemma proj_mem_iff:
  "(ln i, d) \<in> set D \<longleftrightarrow> (ln i, d) \<in> set (proj i D)"
  "(\<star>, d) \<in> set D \<longleftrightarrow> (\<star>, d) \<in> set (proj i D)"
unfolding proj_def by auto

lemma proj_list_insert:
  "proj i (List.insert (ln i,d) D) = List.insert (ln i,d) (proj i D)"
  "proj i (List.insert (\<star>,d) D) = List.insert (\<star>,d) (proj i D)"
  "i \<noteq> j \<Longrightarrow> proj i (List.insert (ln j,d) D) = proj i D"
unfolding List.insert_def proj_def by auto

lemma proj_filter: "proj i [d\<leftarrow>D. d \<notin> set Di] = [d\<leftarrow>proj i D. d \<notin> set Di]"
by (simp_all add: proj_def conj_commute)

lemma proj_list_Cons:
  "proj i ((ln i,d)#D) = (ln i,d)#proj i D"
  "proj i ((\<star>,d)#D) = (\<star>,d)#proj i D"
  "i \<noteq> j \<Longrightarrow> proj i ((ln j,d)#D) = proj i D"
unfolding List.insert_def proj_def by auto

lemma proj_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t:
  "proj l (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l A)"
proof (induction A)
  case (Cons a A)
  obtain k b where "a = (k,b)" by (metis surj_pair)
  thus ?case using Cons unfolding dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def proj_def by (cases b) auto
qed simp

lemma proj_instance_ex:
  assumes B: "\<forall>b \<in> set B. \<exists>a \<in> set A. \<exists>\<delta>. b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> P \<delta>"
    and b: "b \<in> set (proj l B)"
  shows "\<exists>a \<in> set (proj l A). \<exists>\<delta>. b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<and> P \<delta>"
proof -
  obtain a \<delta> where a: "a \<in> set A" "b = a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" "P \<delta>" using B b proj_set_subset by fast
  obtain k b' where b': "b = (k, b')" "k = (ln l) \<or> k = \<star>" using b proj_in_setD by metis
  obtain a' where a': "a = (k, a')" using b'(1) a(2) by (cases a) simp_all
  show ?thesis using a a' b'(2) unfolding proj_def by auto
qed

lemma proj_dbproj:
  "dbproj (ln i) (proj i D) = dbproj (ln i) D"
  "dbproj \<star> (proj i D) = dbproj \<star> D"
  "i \<noteq> j \<Longrightarrow> dbproj (ln j) (proj i D) = []"
unfolding proj_def dbproj_def by (induct D) auto

lemma dbproj_Cons:
  "dbproj i ((i,d)#D) = (i,d)#dbproj i D"
  "i \<noteq> j \<Longrightarrow> dbproj j ((i,d)#D) = dbproj j D"
unfolding dbproj_def by auto

lemma dbproj_subset[simp]:
  "set (unlabel (dbproj i D)) \<subseteq> set (unlabel D)"
unfolding unlabel_def dbproj_def by auto

lemma dbproj_subseq: 
  assumes "Di \<in> set (subseqs (dbproj k D))"
  shows "dbproj k Di = Di" (is ?A)
  and "i \<noteq> k \<Longrightarrow> dbproj i Di = []" (is "i \<noteq> k \<Longrightarrow> ?B")
proof -
  have *: "set Di \<subseteq> set (dbproj k D)" using subseqs_powset[of "dbproj k D"] assms by auto
  then show ?A
    by (auto simp add: dbproj_def intro: filter_True)
  have "\<And>j d. (j,d) \<in> set Di \<Longrightarrow> j = k" using * unfolding dbproj_def by auto
  moreover have "\<And>j d. (j,d) \<in> set (dbproj i Di) \<Longrightarrow> j = i" unfolding dbproj_def by auto
  moreover have "\<And>j d. (j,d) \<in> set (dbproj i Di) \<Longrightarrow> (j,d) \<in> set Di" unfolding dbproj_def by auto
  ultimately show "i \<noteq> k \<Longrightarrow> ?B" by (metis set_empty subrelI subset_empty)
qed

lemma dbproj_subseq_subset:
  assumes "Di \<in> set (subseqs (dbproj i D))"
  shows "set Di \<subseteq> set D"
  using assms by (auto simp add: dbproj_def image_iff simp flip: Pow_iff subseqs_powset in_set_subseqs
    intro!: bexI [of _ Di])
    (meson in_set_subseqs subseq_filter_left subseq_order.dual_order.trans)

lemma dbproj_subseq_in_subseqs:
  assumes "Di \<in> set (subseqs (dbproj i D))"
  shows "Di \<in> set (subseqs D)"
using assms in_set_subseqs subseq_filter_left subseq_order.dual_order.trans
unfolding dbproj_def by blast

lemma proj_subseq:
  assumes "Di \<in> set (subseqs (dbproj (ln j) D))" "j \<noteq> i"
  shows "[d\<leftarrow>proj i D. d \<notin> set Di] = proj i D"
proof -
  have "set Di \<subseteq> set (dbproj (ln j) D)" using subseqs_powset[of "dbproj (ln j) D"] assms by auto
  hence "\<And>k d. (k,d) \<in> set Di \<Longrightarrow> k = ln j" unfolding dbproj_def by auto
  moreover have "\<And>k d. (k,d) \<in> set (proj i D) \<Longrightarrow> k \<noteq> ln j"
    using assms(2) unfolding proj_def by auto
  ultimately have "\<And>d. d \<in> set (proj i D) \<Longrightarrow> d \<notin> set Di" by auto
  thus ?thesis by simp
qed

lemma unlabel_subseqsD:
  assumes "A \<in> set (subseqs (unlabel B))"
  shows "\<exists>C \<in> set (subseqs B). unlabel C = A"
using assms map_subseqs unfolding unlabel_def by (metis imageE set_map) 

lemma unlabel_filter_eq:
  assumes "\<forall>(j, p) \<in> set A \<union> B. \<forall>(k, q) \<in> set A \<union> B. p = q \<longrightarrow> j = k" (is "?P (set A)")
  shows "[d\<leftarrow>unlabel A. d \<notin> snd ` B] = unlabel [d\<leftarrow>A. d \<notin> B]"
using assms unfolding unlabel_def
proof (induction A)
  case (Cons a A)
  have "set A \<subseteq> set (a#A)" "{a} \<subseteq> set (a#A)" by auto
  hence *: "?P (set A)" "?P {a}" using Cons.prems by fast+
  hence IH: "[d\<leftarrow>map snd A . d \<notin> snd ` B] = map snd [d\<leftarrow>A . d \<notin> B]" using Cons.IH by auto

  { assume "snd a \<in> snd ` B"
    then obtain b where b: "b \<in> B" "snd a = snd b" by atomize_elim auto
    hence "fst a = fst b" using *(2) by auto
    hence "a \<in> B" using b by (metis surjective_pairing)  
  } hence **: "a \<notin> B \<Longrightarrow> snd a \<notin> snd ` B" by metis

  show ?case by (cases "a \<in> B") (simp add: ** IH)+ 
qed simp

lemma subseqs_mem_dbproj:
  assumes "Di \<in> set (subseqs D)" "list_all (\<lambda>d. fst d = i) Di"
  shows "Di \<in> set (subseqs (dbproj i D))"
using assms
proof (induction D arbitrary: Di)
  case (Cons di D)
  obtain d j where di: "di = (j,d)" by (metis surj_pair)
  show ?case
  proof (cases "Di \<in> set (subseqs D)")
    case True
    hence "Di \<in> set (subseqs (dbproj i D))" using Cons.IH Cons.prems by auto
    thus ?thesis using subseqs_Cons unfolding dbproj_def by auto
  next
    case False
    then obtain Di' where Di': "Di = di#Di'" using Cons.prems(1)
      by (metis (mono_tags, lifting) Un_iff imageE set_append set_map subseqs.simps(2)) 
    hence "Di' \<in> set (subseqs D)" using Cons.prems(1) False
      by (metis (no_types, lifting) UnE imageE list.inject set_append set_map subseqs.simps(2)) 
    hence "Di' \<in> set (subseqs (dbproj i D))" using Cons.IH Cons.prems Di' by auto
    moreover have "i = j" using Di' di Cons.prems(2) by auto
    hence "dbproj i (di#D) = di#dbproj i D" unfolding dbproj_def by (simp add: di)
    ultimately show ?thesis using Di'
      by (metis (no_types, lifting) UnCI image_eqI set_append set_map subseqs.simps(2)) 
  qed
qed simp

lemma unlabel_subst: "unlabel S \<cdot>\<^sub>s\<^sub>s\<^sub>t \<delta> = unlabel (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
unfolding unlabel_def subst_apply_stateful_strand_def subst_apply_labeled_stateful_strand_def 
by auto

lemma subterms_subst_lsst:
  assumes "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S). (\<exists>f. \<sigma> x = Fun f []) \<or> (\<exists>y. \<sigma> x = Var y)"
    and "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<sigma> = {}"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>)) = subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
using subterms_subst''[OF assms(1)] trms\<^sub>s\<^sub>s\<^sub>t_subst[OF assms(2)] unlabel_subst[of S \<sigma>]
by simp

lemma subterms_subst_lsst_ik:
  assumes "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t S). (\<exists>f. \<sigma> x = Fun f []) \<or> (\<exists>y. \<sigma> x = Var y)"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma>)) = subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
using subterms_subst''[OF assms(1)] ik\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel S" \<sigma>] unlabel_subst[of S \<sigma>]
by simp

lemma labeled_stateful_strand_subst_comp:
  assumes "range_vars \<delta> \<inter> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S = {}"
  shows "S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta> = (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>"
using assms
proof (induction S)
  case (Cons s S)
  obtain l x where s: "s = (l,x)" by (metis surj_pair)
  hence IH: "S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta> \<circ>\<^sub>s \<theta> = (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>" using Cons by auto

  have "x \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta> \<circ>\<^sub>s \<theta> = (x \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) \<cdot>\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>"
    using s Cons.prems stateful_strand_step_subst_comp[of \<delta> x \<theta>] by auto
  thus ?case using s IH by (simp add: subst_apply_labeled_stateful_strand_def)
qed simp

lemma sst_vars_proj_subset[simp]:
  "fv\<^sub>s\<^sub>s\<^sub>t (proj_unl n A) \<subseteq> fv\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
  "bvars\<^sub>s\<^sub>s\<^sub>t (proj_unl n A) \<subseteq> bvars\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
  "vars\<^sub>s\<^sub>s\<^sub>t (proj_unl n A) \<subseteq> vars\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
using vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel A"]
      vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "proj_unl n A"]
unfolding unlabel_def proj_def by auto

lemma trms\<^sub>s\<^sub>s\<^sub>t_proj_subset[simp]:
  "trms\<^sub>s\<^sub>s\<^sub>t (proj_unl n A) \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel A)" (is ?A)
  "trms\<^sub>s\<^sub>s\<^sub>t (proj_unl m (proj n A)) \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (proj_unl n A)" (is ?B)
  "trms\<^sub>s\<^sub>s\<^sub>t (proj_unl m (proj n A)) \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (proj_unl m A)" (is ?C)
proof -
  show ?A unfolding unlabel_def proj_def by auto
  show ?B using trms\<^sub>s\<^sub>s\<^sub>t_mono[OF proj_proj_set_subset(4)] by metis
  show ?C using trms\<^sub>s\<^sub>s\<^sub>t_mono[OF proj_proj_set_subset(3)] by metis
qed

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset:
  "trms\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel (A@B))" (is ?A)
  "trms\<^sub>s\<^sub>s\<^sub>t (proj_unl n A) \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (proj_unl n (A@B))" (is ?B)
using trms\<^sub>s\<^sub>s\<^sub>t_mono[of "proj_unl n A" "proj_unl n (A@B)"]
unfolding unlabel_def proj_def by auto

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_suffix_subset:
  "trms\<^sub>s\<^sub>s\<^sub>t (unlabel B) \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (unlabel (A@B))"
  "trms\<^sub>s\<^sub>s\<^sub>t (proj_unl n B) \<subseteq> trms\<^sub>s\<^sub>s\<^sub>t (proj_unl n (A@B))"
using trms\<^sub>s\<^sub>s\<^sub>t_mono[of "proj_unl n B" "proj_unl n (A@B)"]
unfolding unlabel_def proj_def by auto

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>pD:
  assumes p: "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
  shows "fst p = fst a" (is ?P)
    and "is_Update (snd a) \<or> is_InSet (snd a) \<or> is_NegChecks (snd a)" (is ?Q)
proof -
  obtain l k p' a' where a: "p = (l,p')" "a = (k,a')" by (metis surj_pair)
  show ?P using p a by (cases a') auto
  show ?Q using p a by (cases a') auto
qed

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_nil[simp]:
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t [] = {}"
by (simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_cons[simp]:
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (x#S) = setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p x \<union> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S"
by (simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>s\<^sub>s\<^sub>t_proj_subset:
  "setops\<^sub>s\<^sub>s\<^sub>t (proj_unl n A) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (unlabel A)"
  "setops\<^sub>s\<^sub>s\<^sub>t (proj_unl m (proj n A)) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (proj_unl n A)"
  "setops\<^sub>s\<^sub>s\<^sub>t (proj_unl m (proj n A)) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (proj_unl m A)"
unfolding unlabel_def proj_def
proof (induction A)
  case (Cons a A)
  obtain l b where lb: "a = (l,b)" by atomize_elim auto
  { case 1 thus ?case using Cons.IH(1) unfolding lb by (cases b) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 2 thus ?case using Cons.IH(2) unfolding lb by (cases b) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 3 thus ?case using Cons.IH(3) unfolding lb by (cases b) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def) }
qed simp_all

lemma setops\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset:
  "setops\<^sub>s\<^sub>s\<^sub>t (unlabel A) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@B))"
  "setops\<^sub>s\<^sub>s\<^sub>t (proj_unl n A) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (proj_unl n (A@B))"
unfolding unlabel_def proj_def
proof (induction A)
  case (Cons a A)
  obtain l b where lb: "a = (l,b)" by atomize_elim auto
  { case 1 thus ?case using Cons.IH lb by (cases b) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 2 thus ?case using Cons.IH lb by (cases b) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def) }
qed (simp_all add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>s\<^sub>s\<^sub>t_unlabel_suffix_subset:
  "setops\<^sub>s\<^sub>s\<^sub>t (unlabel B) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (unlabel (A@B))"
  "setops\<^sub>s\<^sub>s\<^sub>t (proj_unl n B) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (proj_unl n (A@B))"
unfolding unlabel_def proj_def
proof (induction A)
  case (Cons a A)
  obtain l b where lb: "a = (l,b)" by atomize_elim auto
  { case 1 thus ?case using Cons.IH lb by (cases b) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def) }
  { case 2 thus ?case using Cons.IH lb by (cases b) (auto simp add: setops\<^sub>s\<^sub>s\<^sub>t_def) }
qed simp_all

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_proj_subset:
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A) \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj m (proj n A)) \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A)"
unfolding proj_def setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_prefix_subset:
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B)"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n A) \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n (A@B))"
unfolding proj_def setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_suffix_subset:
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B)"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n B) \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n (A@B))"
unfolding proj_def setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_mono:
  "set M \<subseteq> set N \<Longrightarrow> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t M \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t N"
by (auto simp add: setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def)

lemma trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subset_if_no_label:
  "\<not>list_ex (has_LabelN l) A \<Longrightarrow> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l A) \<subseteq> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l' A)"
by (rule trms\<^sub>s\<^sub>s\<^sub>t_mono[OF proj_subset_if_no_label(2)[of l A l']])

lemma setops\<^sub>s\<^sub>s\<^sub>t_unlabel_subset_if_no_label:
  "\<not>list_ex (has_LabelN l) A \<Longrightarrow> setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l A) \<subseteq> setops\<^sub>s\<^sub>s\<^sub>t (proj_unl l' A)"
by (rule setops\<^sub>s\<^sub>s\<^sub>t_mono[OF proj_subset_if_no_label(2)[of l A l']])

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_proj_subset_if_no_label:
  "\<not>list_ex (has_LabelN l) A \<Longrightarrow> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l A) \<subseteq> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l' A)"
by (rule setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_mono[OF proj_subset_if_no_label(1)[of l A l']])

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases[simp]:
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,send\<langle>ts\<rangle>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,receive\<langle>ts\<rangle>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,\<langle>ac: s \<doteq> t\<rangle>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = {}"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,insert\<langle>t,s\<rangle>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = {(l,t \<cdot> \<delta>,s \<cdot> \<delta>)}"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,delete\<langle>t,s\<rangle>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = {(l,t \<cdot> \<delta>,s \<cdot> \<delta>)}"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,\<langle>ac: t \<in> s\<rangle>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) = {(l,t \<cdot> \<delta>,s \<cdot> \<delta>)}"
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p ((l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>) =
    ((\<lambda>(t,s). (l,t \<cdot> rm_vars (set X) \<delta>,s \<cdot> rm_vars (set X) \<delta>)) ` set F')" (is "?A = ?B")
proof -
  have "?A = (\<lambda>(t,s). (l,t,s)) ` set (F' \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s rm_vars (set X) \<delta>)" by auto
  thus "?A = ?B" unfolding subst_apply_pairs_def by auto
qed simp_all

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst:
  assumes "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a)) \<inter> subst_domain \<theta> = {}"
  shows "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = (\<lambda>p. (fst a,snd p \<cdot>\<^sub>p \<theta>)) ` setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
proof -
  obtain l a' where a: "a = (l,a')" by (metis surj_pair)
  show ?thesis
  proof (cases a')
    case (NegChecks X F G)
    hence *: "rm_vars (set X) \<theta> = \<theta>" using a assms rm_vars_apply'[of \<theta> "set X"] by auto
    have "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = (\<lambda>p. (fst a, p)) ` set (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)"
      using * NegChecks a  by auto
    moreover have "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a = (\<lambda>p. (fst a, p)) ` set G" using NegChecks a by simp
    hence "(\<lambda>p. (fst a,snd p \<cdot>\<^sub>p \<theta>)) ` setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a = (\<lambda>p. (fst a, p \<cdot>\<^sub>p \<theta>)) ` set G"
      by (metis (mono_tags, lifting) image_cong image_image snd_conv)
    hence "(\<lambda>p. (fst a,snd p \<cdot>\<^sub>p \<theta>)) ` setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a = (\<lambda>p. (fst a, p)) ` (set G \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>)"
      unfolding case_prod_unfold by auto
    ultimately show ?thesis by (simp add: subst_apply_pairs_def) 
  qed (use a in simp_all)
qed

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst':
  assumes "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a)) \<inter> subst_domain \<theta> = {}"
  shows "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>) = (\<lambda>(i,p). (i,p \<cdot>\<^sub>p \<theta>)) ` setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a"
using setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst[OF assms] setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>pD(1) unfolding case_prod_unfold
by (metis (mono_tags, lifting) image_cong)

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst:
  assumes "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<theta> = {}"
  shows "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = (\<lambda>p. (fst p,snd p \<cdot>\<^sub>p \<theta>)) ` setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S"
using assms
proof (induction S)
  case (Cons a S)
  have "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<inter> subst_domain \<theta> = {}" and *: "set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a)) \<inter> subst_domain \<theta> = {}"
    using Cons.prems by auto
  hence IH: "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (S \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) = (\<lambda>p. (fst p,snd p \<cdot>\<^sub>p \<theta>)) ` setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t S"
    using Cons.IH by auto
  show ?case
    using setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst'[OF *] IH
    unfolding setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def case_prod_unfold subst_lsst_cons 
    by auto
qed (simp add: setops\<^sub>s\<^sub>s\<^sub>t_def)

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_in_subst:
  assumes p: "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
  shows "\<exists>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a. fst p = fst q \<and> snd p = snd q \<cdot>\<^sub>p rm_vars (set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a))) \<delta>"
    (is "\<exists>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a. ?P q")
proof -
  obtain l b where a: "a = (l,b)" by (metis surj_pair)

  show ?thesis
  proof (cases b)
    case (NegChecks X F F')
    hence "p \<in> (\<lambda>(t, s). (l, t \<cdot> rm_vars (set X) \<delta>, s \<cdot> rm_vars (set X) \<delta>)) ` set F'"
      using p a setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_subst_cases(7)[of l X F F' \<delta>] by blast
    then obtain s t where st:
        "(t,s) \<in> set F'" "p = (l, t \<cdot> rm_vars (set X) \<delta>, s \<cdot> rm_vars (set X) \<delta>)"
      by auto
    hence "(l,t,s) \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a" "fst p = fst (l,t,s)"
          "snd p = snd (l,t,s) \<cdot>\<^sub>p rm_vars (set X) \<delta>"
      using a NegChecks by fastforce+
    moreover have "bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a) = X" using NegChecks a by auto
    ultimately show ?thesis by blast
  qed (use p a in auto)
qed

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_in_subst:
  assumes "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)"
  shows "\<exists>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. fst p = fst q \<and> (\<exists>X \<subseteq> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. snd p = snd q \<cdot>\<^sub>p rm_vars X \<delta>)"
    (is "\<exists>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. ?P A q")
  using assms
proof (induction A)
  case (Cons a A)
  note 0 = unlabel_Cons(2)[of a A] bvars\<^sub>s\<^sub>s\<^sub>t_Cons[of "snd a" "unlabel A"]
  show ?case
  proof (cases "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)")
    case False
    hence "p \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p (a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>)"
      using Cons.prems setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_cons[of "a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<delta>" "A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>"] subst_lsst_cons[of a A \<delta>] by auto
    moreover have "(set (bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd a))) \<subseteq> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (a#A)" using 0 by simp
    ultimately have "\<exists>q \<in> setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a. ?P (a#A) q" using setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p_in_subst[of p a \<delta>] by blast
    thus ?thesis by auto
  qed (use Cons.IH 0 in auto)
qed simp

lemma setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq:
  "setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) = setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
proof (induction A)
  case (Cons a A)
  obtain l b where "a = (l,b)" by (metis surj_pair)
  thus ?case using Cons unfolding setops\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by (cases b) auto
qed simp

end
