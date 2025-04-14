subsubsection \<open>Closure-Operations on Relations\<close>

theory Relation_Closure
  imports "Abstract-Rewriting.Relative_Rewriting"
begin

locale rel_closure =
  fixes cop :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" \<comment> \<open>closure operator\<close>
    and nil :: "'b"
    and add :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes cop_nil: "cop nil x = x"
  assumes cop_add: "cop (add a b) x = cop a (cop b x)"
begin

inductive_set closure for r :: "'a rel"
  where
    [intro]: "(x, y) \<in> r \<Longrightarrow> (cop a x, cop a y) \<in> closure r"

lemma closureI2: "(x, y) \<in> r \<Longrightarrow> u = cop a x \<Longrightarrow> v = cop a y \<Longrightarrow> (u, v) \<in> closure r" by auto

lemma closure_mono: "r \<subseteq> s \<Longrightarrow> closure r \<subseteq> closure s" by (auto elim: closure.cases)

lemma subset_closure: "r \<subseteq> closure r"
  using closure.intros [where a = nil] by (auto simp: cop_nil)

definition "closed r \<longleftrightarrow> closure r \<subseteq> r"

lemma closure_subset: "closed r \<Longrightarrow> closure r \<subseteq> r"
  by (auto simp: closed_def)

lemma closedI [Pure.intro, intro]: "(\<And>x y a. (x, y) \<in> r \<Longrightarrow> (cop a x, cop a y) \<in> r) \<Longrightarrow> closed r"
  by (auto simp: closed_def elim: closure.cases)

lemma closedD [dest]: "closed r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (cop a x, cop a y) \<in> r"
  by (auto simp: closed_def)

lemma closed_closure [intro]: "closed (closure r)"
  using closure.intros [where a = "add a b" for a b]
  by (auto simp: closed_def cop_add elim!: closure.cases)

lemma subset_closure_Un:
  "closure r \<subseteq> closure (r \<union> s)"
  "closure s \<subseteq> closure (r \<union> s)"
  by (auto elim!: closure.cases)

lemma closure_Un: "closure (r \<union> s) = closure r \<union> closure s"
  using subset_closure_Un by (auto elim: closure.cases)

lemma closure_id [simp]: "closed r \<Longrightarrow> closure r = r"
  using subset_closure and closure_subset by blast

lemma closed_Un [intro]: "closed r \<Longrightarrow> closed s \<Longrightarrow> closed (r \<union> s)" by blast

lemma closed_Inr [intro]: "closed r \<Longrightarrow> closed s \<Longrightarrow> closed (r \<inter> s)" by blast

lemma closed_rtrancl [intro]: "closed r \<Longrightarrow> closed (r\<^sup>*)"
  by (best intro: rtrancl_into_rtrancl elim: rtrancl.induct)

lemma closed_trancl [intro]: "closed r \<Longrightarrow> closed (r\<^sup>+)"
  by (best intro: trancl_into_trancl elim: trancl.induct)

lemma closed_converse [intro]: "closed r \<Longrightarrow> closed (r\<inverse>)" by blast

lemma closed_comp [intro]: "closed r \<Longrightarrow> closed s \<Longrightarrow> closed (r O s)" by blast

lemma closed_relpow [intro]: "closed r \<Longrightarrow> closed (r ^^ n)"
  by (auto intro: relpow_image [OF closedD])

lemma closed_conversion [intro]: "closed r \<Longrightarrow> closed (r\<^sup>\<leftrightarrow>\<^sup>*)"
  by (auto simp: conversion_def)

lemma closed_relto [intro]: "closed r \<Longrightarrow> closed s \<Longrightarrow> closed (relto r s)" by blast

lemma closure_diff_subset: "closure r - closure s \<subseteq> closure (r - s)" by (auto elim: closure.cases)

end

end
