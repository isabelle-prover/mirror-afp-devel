(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Syntactic Fragments of LTL\<close>

theory Syntactic_Fragments
  imports Main LTL
begin

subsection \<open>The fragments $\mu$LTL and $\nu$LTL\<close>

fun is_\<mu>LTL :: "'a ltln \<Rightarrow> bool"
  where
  "is_\<mu>LTL true\<^sub>n = True"
| "is_\<mu>LTL false\<^sub>n = True"
| "is_\<mu>LTL prop\<^sub>n(_) = True"
| "is_\<mu>LTL nprop\<^sub>n(_) = True"
| "is_\<mu>LTL (\<phi> and\<^sub>n \<psi>) = (is_\<mu>LTL \<phi> \<and> is_\<mu>LTL \<psi>)"
| "is_\<mu>LTL (\<phi> or\<^sub>n \<psi>) = (is_\<mu>LTL \<phi> \<and> is_\<mu>LTL \<psi>)"
| "is_\<mu>LTL (X\<^sub>n \<phi>) = is_\<mu>LTL \<phi>"
| "is_\<mu>LTL (\<phi> U\<^sub>n \<psi>) = (is_\<mu>LTL \<phi> \<and> is_\<mu>LTL \<psi>)"
| "is_\<mu>LTL (\<phi> M\<^sub>n \<psi>) = (is_\<mu>LTL \<phi> \<and> is_\<mu>LTL \<psi>)"
| "is_\<mu>LTL _ = False"

fun is_\<nu>LTL :: "'a ltln \<Rightarrow> bool"
  where
  "is_\<nu>LTL true\<^sub>n = True"
| "is_\<nu>LTL false\<^sub>n = True"
| "is_\<nu>LTL prop\<^sub>n(_) = True"
| "is_\<nu>LTL nprop\<^sub>n(_) = True"
| "is_\<nu>LTL (\<phi> and\<^sub>n \<psi>) = (is_\<nu>LTL \<phi> \<and> is_\<nu>LTL \<psi>)"
| "is_\<nu>LTL (\<phi> or\<^sub>n \<psi>) = (is_\<nu>LTL \<phi> \<and> is_\<nu>LTL \<psi>)"
| "is_\<nu>LTL (X\<^sub>n \<phi>) = is_\<nu>LTL \<phi>"
| "is_\<nu>LTL (\<phi> W\<^sub>n \<psi>) = (is_\<nu>LTL \<phi> \<and> is_\<nu>LTL \<psi>)"
| "is_\<nu>LTL (\<phi> R\<^sub>n \<psi>) = (is_\<nu>LTL \<phi> \<and> is_\<nu>LTL \<psi>)"
| "is_\<nu>LTL _ = False"

definition \<mu>LTL :: "'a ltln set" where
  "\<mu>LTL = {\<phi>. is_\<mu>LTL \<phi>}"

definition \<nu>LTL :: "'a ltln set" where
  "\<nu>LTL = {\<phi>. is_\<nu>LTL \<phi>}"

lemma \<mu>LTL_simp[simp]:
  "\<phi> \<in> \<mu>LTL \<longleftrightarrow> is_\<mu>LTL \<phi>"
  unfolding \<mu>LTL_def by simp

lemma \<nu>LTL_simp[simp]:
  "\<phi> \<in> \<nu>LTL \<longleftrightarrow> is_\<nu>LTL \<phi>"
  unfolding \<nu>LTL_def by simp



subsubsection \<open>Subformulas in $\mu$LTL and $\nu$LTL\<close>

fun subformulas\<^sub>\<mu> :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "subformulas\<^sub>\<mu> (\<phi> and\<^sub>n \<psi>) = subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (\<phi> or\<^sub>n \<psi>) = subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (X\<^sub>n \<phi>) = subformulas\<^sub>\<mu> \<phi>"
| "subformulas\<^sub>\<mu> (\<phi> U\<^sub>n \<psi>) = {\<phi> U\<^sub>n \<psi>} \<union> subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (\<phi> R\<^sub>n \<psi>) = subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (\<phi> W\<^sub>n \<psi>) = subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> (\<phi> M\<^sub>n \<psi>) = {\<phi> M\<^sub>n \<psi>} \<union> subformulas\<^sub>\<mu> \<phi> \<union> subformulas\<^sub>\<mu> \<psi>"
| "subformulas\<^sub>\<mu> _ = {}"

fun subformulas\<^sub>\<nu> :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "subformulas\<^sub>\<nu> (\<phi> and\<^sub>n \<psi>) = subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (\<phi> or\<^sub>n \<psi>) = subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (X\<^sub>n \<phi>) = subformulas\<^sub>\<nu> \<phi>"
| "subformulas\<^sub>\<nu> (\<phi> U\<^sub>n \<psi>) = subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (\<phi> R\<^sub>n \<psi>) = {\<phi> R\<^sub>n \<psi>} \<union> subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (\<phi> W\<^sub>n \<psi>) = {\<phi> W\<^sub>n \<psi>} \<union> subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> (\<phi> M\<^sub>n \<psi>) = subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<nu> \<psi>"
| "subformulas\<^sub>\<nu> _ = {}"

abbreviation "ltln_U \<equiv> {\<phi> U\<^sub>n \<psi> | \<phi> \<psi>. True}"
abbreviation "ltln_R \<equiv> {\<phi> R\<^sub>n \<psi> | \<phi> \<psi>. True}"
abbreviation "ltln_W \<equiv> {\<phi> W\<^sub>n \<psi> | \<phi> \<psi>. True}"
abbreviation "ltln_M \<equiv> {\<phi> M\<^sub>n \<psi> | \<phi> \<psi>. True}"

lemma subformulas\<^sub>\<mu>_semantics:
  "subformulas\<^sub>\<mu> \<phi> = subfrmlsn \<phi> \<inter> (ltln_U \<union> ltln_M)"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_semantics:
  "subformulas\<^sub>\<nu> \<phi> = subfrmlsn \<phi> \<inter> (ltln_R \<union> ltln_W)"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>_subfrmlsn:
  "subformulas\<^sub>\<mu> \<phi> \<subseteq> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_subfrmlsn:
  "subformulas\<^sub>\<nu> \<phi> \<subseteq> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>_finite:
  "finite (subformulas\<^sub>\<mu> \<phi>)"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_finite:
  "finite (subformulas\<^sub>\<nu> \<phi>)"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> subformulas\<^sub>\<mu> \<psi> \<subseteq> subformulas\<^sub>\<mu> \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> subformulas\<^sub>\<nu> \<psi> \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  by (induction \<phi>) auto

lemma subfrmlsn_\<mu>LTL:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> subfrmlsn \<phi> \<subseteq> \<mu>LTL"
  by (induction \<phi>) auto

lemma subfrmlsn_\<nu>LTL:
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> subfrmlsn \<phi> \<subseteq> \<nu>LTL"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<mu>\<^sub>\<nu>_disjoint:
  "subformulas\<^sub>\<mu> \<phi> \<inter> subformulas\<^sub>\<nu> \<phi> = {}"
  unfolding subformulas\<^sub>\<mu>_semantics subformulas\<^sub>\<nu>_semantics
  by fastforce


subsubsection \<open>Subformula lists\<close>

fun subformulas\<^sub>\<mu>_list :: "'a ltln \<Rightarrow> 'a ltln list"
where
  "subformulas\<^sub>\<mu>_list (\<phi> and\<^sub>n \<psi>) = subformulas\<^sub>\<mu>_list \<phi> @ subformulas\<^sub>\<mu>_list \<psi>"
| "subformulas\<^sub>\<mu>_list (\<phi> or\<^sub>n \<psi>) = subformulas\<^sub>\<mu>_list \<phi> @ subformulas\<^sub>\<mu>_list \<psi>"
| "subformulas\<^sub>\<mu>_list (X\<^sub>n \<phi>) = subformulas\<^sub>\<mu>_list \<phi>"
| "subformulas\<^sub>\<mu>_list (\<phi> U\<^sub>n \<psi>) = (\<phi> U\<^sub>n \<psi>) # subformulas\<^sub>\<mu>_list \<phi> @ subformulas\<^sub>\<mu>_list \<psi>"
| "subformulas\<^sub>\<mu>_list (\<phi> R\<^sub>n \<psi>) = subformulas\<^sub>\<mu>_list \<phi> @ subformulas\<^sub>\<mu>_list \<psi>"
| "subformulas\<^sub>\<mu>_list (\<phi> W\<^sub>n \<psi>) = subformulas\<^sub>\<mu>_list \<phi> @ subformulas\<^sub>\<mu>_list \<psi>"
| "subformulas\<^sub>\<mu>_list (\<phi> M\<^sub>n \<psi>) = (\<phi> M\<^sub>n \<psi>) # subformulas\<^sub>\<mu>_list \<phi> @ subformulas\<^sub>\<mu>_list \<psi>"
| "subformulas\<^sub>\<mu>_list _ = []"

fun subformulas\<^sub>\<nu>_list :: "'a ltln \<Rightarrow> 'a ltln list"
where
  "subformulas\<^sub>\<nu>_list (\<phi> and\<^sub>n \<psi>) = subformulas\<^sub>\<nu>_list \<phi> @ subformulas\<^sub>\<nu>_list \<psi>"
| "subformulas\<^sub>\<nu>_list (\<phi> or\<^sub>n \<psi>) = subformulas\<^sub>\<nu>_list \<phi> @ subformulas\<^sub>\<nu>_list \<psi>"
| "subformulas\<^sub>\<nu>_list (X\<^sub>n \<phi>) = subformulas\<^sub>\<nu>_list \<phi>"
| "subformulas\<^sub>\<nu>_list (\<phi> U\<^sub>n \<psi>) = subformulas\<^sub>\<nu>_list \<phi> @ subformulas\<^sub>\<nu>_list \<psi>"
| "subformulas\<^sub>\<nu>_list (\<phi> R\<^sub>n \<psi>) = (\<phi> R\<^sub>n \<psi>) # subformulas\<^sub>\<nu>_list \<phi> @ subformulas\<^sub>\<nu>_list \<psi>"
| "subformulas\<^sub>\<nu>_list (\<phi> W\<^sub>n \<psi>) = (\<phi> W\<^sub>n \<psi>) # subformulas\<^sub>\<nu>_list \<phi> @ subformulas\<^sub>\<nu>_list \<psi>"
| "subformulas\<^sub>\<nu>_list (\<phi> M\<^sub>n \<psi>) = subformulas\<^sub>\<nu>_list \<phi> @ subformulas\<^sub>\<nu>_list \<psi>"
| "subformulas\<^sub>\<nu>_list _ = []"


lemma subformulas\<^sub>\<mu>_list_set:
  "set (subformulas\<^sub>\<mu>_list \<phi>) = subformulas\<^sub>\<mu> \<phi>"
  by (induction \<phi>) auto

lemma subformulas\<^sub>\<nu>_list_set:
  "set (subformulas\<^sub>\<nu>_list \<phi>) = subformulas\<^sub>\<nu> \<phi>"
  by (induction \<phi>) auto


end
