(*  Title:       Execution equivalence state-space reduction for DCR-graphs
    Author:      Søren Debois & Axel Christfort 2023
    Maintainer:  Axel Christfort <axel@di.ku.dk>
*)

theory DCRExecutionEquivalence
  imports Main
begin


section \<open>DCR processes\<close>

text \<open>Although we use the term "process", the present theory formalises DCR graphs as defined
in the original places and other papers.\<close>


type_synonym event = nat

text \<open>The static structure. This encompasss the relations, the set of event @{term dom} of the
process, and the labelling function @{term lab}. We do not explicitly enforce that relations and marking are confined to this set, except in
definitions of enabledness and execution below. \<close>

record rels =
  (* Relations *)
  cond :: "event rel"
  pend :: "event rel"
  incl :: "event rel"
  excl :: "event rel"
  mist :: "event rel"
  (* Other static structure *)
  dom  :: "event set"

(* abbreviation "rng T \<equiv> range (lab T)"  *)

text \<open>The dynamic structure, called the marking\<close>

record marking =
  Ex :: "event set"
  In :: "event set"
  Re :: "event set"


text \<open>
  It will be convenient to have notation for the events
  required, excluded, etc. by a given event.
\<close>

abbreviation conds :: "rels \<Rightarrow> event \<Rightarrow> event set"
  where
    "conds T e \<equiv> { f . (f,e) \<in> cond T }"


abbreviation excls :: "rels \<Rightarrow> event \<Rightarrow> event set"
  where
    "excls T e \<equiv> { x . (e,x) \<in> excl T \<and> (e,x) \<notin> incl T }"


abbreviation incls :: "rels \<Rightarrow> event \<Rightarrow> event set"
  where
    "incls T e \<equiv> { x . (e,x) \<in> incl T }"


abbreviation resps :: "rels \<Rightarrow> event \<Rightarrow> event set"
  where
    "resps T e \<equiv> { f . (e,f) \<in> pend T }"

abbreviation mists :: "rels \<Rightarrow> event \<Rightarrow> event set"
  where
    "mists T e \<equiv> { f . (f,e) \<in> mist T }"

text \<open>Similarly, it is convenient to be able to identify directly the currently excluded events. \<close>

subsection \<open>Execution semantics\<close>


definition enabled :: "rels \<Rightarrow> marking \<Rightarrow> event \<Rightarrow> bool"
  where
    "enabled T M e \<equiv>
        e \<in> In M  \<and>
        (conds T e \<inter> In M) - Ex M = {} \<and>
        (mists T e \<inter> In M) - (dom T - Re M) = {}"

definition execute :: "rels \<Rightarrow> marking \<Rightarrow> nat \<Rightarrow> marking"
  where
    "execute T M e \<equiv> \<lparr>
       Ex = Ex M \<union> { e },
       In = (In M - excls T e) \<union> incls T e,
       Re = (Re M - { e }) \<union> resps T e
      \<rparr>"

subsection \<open>Execution Equivalence\<close>

definition accepting :: "marking \<Rightarrow> bool" where
  "accepting M = (Re M \<inter> In M = {})"

fun acceptingrun :: "rels \<Rightarrow> marking \<Rightarrow> event list \<Rightarrow> bool" where
  "acceptingrun T M [] = accepting M"
| "acceptingrun T M (e#t) = (enabled T M e \<and> acceptingrun T (execute T M e) t)"

definition all_conds :: "rels \<Rightarrow> nat set" where
  "all_conds T = { fst rel | rel . rel \<in> cond T }"

definition execution_equivalent :: "rels \<Rightarrow> marking \<Rightarrow> marking \<Rightarrow> bool" where
  "execution_equivalent T M1 M2 = (
    (In M1 = In M2) \<and>
    (Re M1 = Re M2) \<and>
    ((Ex M1 \<inter> all_conds T) = (Ex M2 \<inter> all_conds T))
  )"

lemma conds_subset_eq_all_conds: "conds T e \<subseteq> all_conds T"
  using all_conds_def by auto

lemma ex_equiv_over_cond: "(Ex M1 \<inter> all_conds T) = (Ex M2 \<inter> all_conds T) \<Longrightarrow> (Ex M1 \<inter> conds T e) = (Ex M2 \<inter> conds T e)"
  using conds_subset_eq_all_conds by blast

lemma enabled_ex_equiv:
  assumes "execution_equivalent T M1 M2" "enabled T M1 e"
  shows "enabled T M2 e"
proof -
  from assms(1) have
    "(Ex M1 \<inter> all_conds T) = (Ex M2 \<inter> all_conds T)"
    by (simp add: execution_equivalent_def)
  hence ex_eq:
    "(Ex M1 \<inter> conds T e) = (Ex M2 \<inter> conds T e)"
    using ex_equiv_over_cond by metis
  from assms(1) have in_eq:
    "In M1 = In M2"
    by (simp add: execution_equivalent_def)
  from assms(2) have
    "(conds T e \<inter> In M1) \<subseteq> Ex M1"
    by(simp_all add: enabled_def)
  hence
    "(conds T e \<inter> In M1) \<inter> (conds T e) \<subseteq> Ex M1 \<inter> (conds T e)"
    by auto
  hence
    "(conds T e \<inter> In M1) \<subseteq> Ex M1 \<inter> (conds T e)"
    by auto
  hence
    "(conds T e \<inter> In M2) \<subseteq> Ex M2 \<inter> (conds T e)"
    using ex_eq in_eq by auto
  hence
    "(conds T e \<inter> In M2) \<subseteq> Ex M2"
    by simp
  then show ?thesis
    using enabled_def assms in_eq execution_equivalent_def by auto
qed

lemma execute_ex_equiv:
  assumes "execution_equivalent T M1 M2" "execute T M1 e = M3" "execute T M2 e = M4"
  shows "execution_equivalent T M3 M4"
proof-
  from assms have
    "In M3 = In M4"
    using execute_def execution_equivalent_def by fastforce
  moreover from assms have
    "Re M3 = Re M4"
    using execute_def execution_equivalent_def by force
  ultimately show ?thesis using assms execute_def execution_equivalent_def
    by fastforce
qed

lemma accepting_ex_equiv: "execution_equivalent T M1 M2 \<Longrightarrow> accepting M1 \<Longrightarrow> accepting M2"
  by (simp add: accepting_def execution_equivalent_def)

theorem acceptingrun_ex_equiv:
  assumes "acceptingrun T M1 seq" "execution_equivalent T M1 M2"
  shows "acceptingrun T M2 seq"
  using assms
proof(induction seq arbitrary: M1 M2 rule: acceptingrun.induct)
  case (1 T M)
  then show ?case
    by (simp add: accepting_ex_equiv)
next
  case (2 T M e t)
  then show ?case proof-
    from 2(2) obtain M1e where m1e:
      "M1e = execute T M1 e"
      by blast
    hence m1e_accept:
      "acceptingrun T M1e t"
      using 2(2) acceptingrun.simps(2) by blast
    obtain M2e where
      "M2e = execute T M2 e"
      by blast
    moreover from this m1e have
      "execution_equivalent T M1e M2e"
      using 2(3) execute_ex_equiv by blast
    moreover from this have
      "acceptingrun T M2e t"
      using 2(1) m1e_accept by blast
    ultimately show ?thesis using 2(2) enabled_ex_equiv 2(3) acceptingrun.simps(2) by blast
  qed
qed

end