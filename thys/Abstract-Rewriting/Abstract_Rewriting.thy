(*  Title:       Abstract Rewriting
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Rene Thiemann       <rene.tiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Rene Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel and René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Abstract Rewrite Systems *}

theory Abstract_Rewriting
imports
  "~~/src/HOL/Library/Infinite_Set"
  "../Transitive-Closure/Transitive_Closure_Impl"
  "../Regular-Sets/Regexp_Method"
  Seq
begin

(*FIXME: move*)
lemma trancl_mono_set: "r \<subseteq> s \<Longrightarrow> r^+ \<subseteq> s^+"
  by (blast intro: trancl_mono)

lemma relpow_mono: assumes "(r :: 'a rel) \<subseteq> r'" shows "r ^^ n \<subseteq> r' ^^ n"
  by (induct n, insert assms, auto)


subsection {* Definitions *}

text {*
  Two elements are \emph{joinable} (and hence in the joinability relation)
  w.r.t.\ @{term "A"}, iff they have a common reduct.
*}
definition join :: "'a rel \<Rightarrow> 'a rel" where
  "join A \<equiv> A^* O (A\<inverse>)^*"

text {*
  Two elements are \emph{meetable} (and hence in the meetability relation)
  w.r.t.\ @{term "A"}, iff they have a common ancestor.
*}
definition meet :: "'a rel \<Rightarrow> 'a rel" where
  "meet A \<equiv> (A^-1)^* O A^*"

text {*The \emph{symmetric closure} of a relation allows steps in both directions.*}
abbreviation symcl :: "'a rel \<Rightarrow> 'a rel" ("(_^<->)" [1000] 999) where
  "A^<-> \<equiv> A \<union> A^-1"

text {*
  A \emph{conversion} is a (possibly empty) sequence of steps in the symmetric
  closure.
*}
definition
  conversion :: "'a rel \<Rightarrow> 'a rel" ("(_^<->*)" [1000] 999)
where
  "A^<->* \<equiv> (A^<->)^*"

text {*
  The set of \emph{normal forms} of an ARS constitutes all the elements that do
  not have any successors.
*}
definition NF :: "'a rel \<Rightarrow> 'a set" where
  "NF A \<equiv> {a. A `` {a} = {}}"

definition
  normalizability :: "'a rel \<Rightarrow> 'a rel" ("(_^!)" [1000] 999)
where
  "A^! \<equiv> {(a, b). (a, b) \<in> A^* \<and> b \<in> NF A}"

notation (xsymbols)
  join ("(_\<^sup>\<down>)" [1000] 999) and
  meet ("(_\<^sup>\<up>)" [1000] 999) and
  symcl ("(_\<^sup>\<leftrightarrow>)" [1000] 999) and
  conversion ("(_\<^bsup>\<leftrightarrow>*\<^esup>)" [1000] 999) and
  normalizability ("(_\<^sup>!)" [1000] 999)

lemma no_step: assumes "A `` {a} = {}" shows "a \<in> NF A"
  using assms by (auto simp: NF_def)

lemma joinI: "(a, c) \<in> A^* \<Longrightarrow> (b, c) \<in> A^* \<Longrightarrow> (a, b) \<in> A\<^sup>\<down>"
  by (auto simp: join_def rtrancl_converse)

lemma joinI_left: "(a, b) \<in> A^* \<Longrightarrow> (a, b) \<in> A\<^sup>\<down>"
  by (auto simp: join_def)

lemma joinI_right: "(b, a) \<in> A^* \<Longrightarrow> (a, b) \<in> A\<^sup>\<down>"
  by (rule joinI) auto

lemma joinE:
  assumes "(a, b) \<in> A\<^sup>\<down>"
  obtains c where "(a, c) \<in> A^*" and "(b, c) \<in> A^*"
  using assms by (auto simp: join_def rtrancl_converse)

lemma joinD: "(a, b) \<in> A\<^sup>\<down> \<Longrightarrow> \<exists>c. (a, c) \<in> A^* \<and> (b, c) \<in> A^*"
  by (blast elim: joinE)

lemma meetI: "(a, b) \<in> A^* \<Longrightarrow> (a, c) \<in> A^* \<Longrightarrow> (b, c) \<in> A\<^sup>\<up>"
by (auto simp: meet_def rtrancl_converse)

lemma meetE:
  assumes "(b, c) \<in> A\<^sup>\<up>"
  obtains a where "(a, b) \<in> A^*" and "(a, c) \<in> A^*"
  using assms by (auto simp: meet_def rtrancl_converse)

lemma meetD: "(b, c) \<in> A\<^sup>\<up> \<Longrightarrow> \<exists>a. (a, b) \<in> A^* \<and> (a, c) \<in> A^*"
  by (blast elim: meetE)

lemma conversionI: "(a, b) \<in> (A\<^sup>\<leftrightarrow>)^* \<Longrightarrow> (a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>"
  by (simp add: conversion_def)

lemma conversion_refl[simp]: "(a, a) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>"
  by (simp add: conversion_def)

lemma conversionI': assumes "(a, b) \<in> A^*" shows "(a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>"
using assms proof (induct)
  case base thus ?case by simp
next
  case (step b c)
  hence "(b, c) \<in> A\<^sup>\<leftrightarrow>" by simp
  with `(a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>` show ?case unfolding conversion_def by (rule rtrancl.intros)
qed


lemma rtrancl_comp_trancl_conv: "r^* O r = r^+" by regexp


lemma trancl_o_refl_is_trancl: "r^+ O r^= = r^+" by regexp

lemma conversionE: "(a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup> \<Longrightarrow> ((a, b) \<in> (A\<^sup>\<leftrightarrow>)^* \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: conversion_def)

text {*
  Later declarations are tried first for `proof' and `rule,' hence the ``main''
  introduction\,/\,elimination rules for constants should be declared last.
*}
declare joinI_left[intro]
declare joinI_right[intro]
declare joinI[intro]
declare joinD[dest]
declare joinE[elim]

declare meetI[intro]
declare meetD[dest]
declare meetE[elim]

declare conversionI'[intro]
declare conversionI[intro]
declare conversionE[elim]

lemma conversion_trans: "trans (A\<^bsup>\<leftrightarrow>*\<^esup>)"
unfolding trans_def proof (intro allI impI)
  fix a b c assume "(a, b) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>" and "(b, c) \<in> A\<^bsup>\<leftrightarrow>*\<^esup>"
  thus "(a, c) \<in> A^<->*" unfolding conversion_def
  proof (induct)
    case base thus ?case by simp
  next
    case (step b c')
    from `(b, c') \<in> A\<^sup>\<leftrightarrow>` and `(c', c) \<in> (A\<^sup>\<leftrightarrow>)^*`
      have "(b, c) \<in> (A\<^sup>\<leftrightarrow>)^*" by (rule converse_rtrancl_into_rtrancl)
    with step show ?case by simp
  qed
qed

lemma conversion_sym: "sym (A^<->*)"
unfolding sym_def proof (intro allI impI)
  fix a b assume "(a, b) \<in> A^<->*" thus "(b, a) \<in> A^<->*" unfolding conversion_def
  proof (induct)
    case base thus ?case by simp
  next
    case (step b c)
    hence "(c, b) \<in> A\<^sup>\<leftrightarrow>" by blast
    from `(c, b) \<in> A\<^sup>\<leftrightarrow>` and `(b, a) \<in> (A\<^sup>\<leftrightarrow>)^*`
      show ?case by (rule converse_rtrancl_into_rtrancl)
  qed
qed

lemma rtrancl_join_join:
  assumes "(a, b) \<in> A^*" and "(b, c) \<in> A\<^sup>\<down>" shows "(a, c) \<in> A\<^sup>\<down>"
proof -
  from `(b, c) \<in> A\<^sup>\<down>` obtain b' where "(b, b') \<in> A^*" and "(b', c) \<in> (A\<inverse>)^*"
    unfolding join_def by blast
  with `(a, b) \<in> A^*` have "(a, b') \<in> A^*" by simp
  with `(b', c) \<in> (A\<inverse>)^*` show ?thesis unfolding join_def by blast
qed

lemma join_rtrancl_join:
  assumes "(a, b) \<in> A\<^sup>\<down>" and "(c, b) \<in> A^*" shows "(a, c) \<in> A\<^sup>\<down>"
proof -
  from `(c, b) \<in> A^*` have "(b, c) \<in> (A\<inverse>)^*" unfolding rtrancl_converse by simp
  from `(a, b) \<in> A\<^sup>\<down>` obtain a' where "(a, a') \<in> A^*" and "(a', b) \<in> (A\<inverse>)^*"
    unfolding join_def by best
  with `(b, c) \<in> (A\<inverse>)^*` have "(a', c) \<in> (A\<inverse>)^*" by simp
  with `(a, a') \<in> A^*` show ?thesis unfolding join_def by blast
qed

lemma NF_I: "(\<And>b. (a, b) \<notin> A) \<Longrightarrow> a \<in> NF A" by (auto intro: no_step)

lemma NF_E: "a \<in> NF A \<Longrightarrow> ((a, b) \<notin> A \<Longrightarrow> P) \<Longrightarrow> P" by (auto simp: NF_def)

declare NF_I[intro]
declare NF_E[elim]

lemma NF_no_step: "a \<in> NF A \<Longrightarrow> \<forall>b. (a, b) \<notin> A" by auto

lemma NF_anti_mono: assumes "A \<subseteq> B" shows "NF B \<subseteq> NF A" using assms by auto

lemma NF_iff_no_step: "a \<in> NF A = (\<forall>b. (a, b) \<notin> A)" by auto

lemma NF_no_trancl_step: assumes "a \<in> NF A" shows "\<forall>b. (a, b) \<notin> A^+"
proof -
  from assms have "\<forall>b. (a, b) \<notin> A" by auto
  show ?thesis
  proof (intro allI notI)
    fix b assume "(a, b) \<in> A^+"
    thus False by (induct) (auto simp: `\<forall>b. (a, b) \<notin> A`)
   qed
qed

lemma NF_Id_on_fst_image[simp]: "NF (Id_on (fst ` A)) = NF A" by force

lemma fst_image_NF_Id_on[simp]: "fst ` R = Q \<Longrightarrow> NF (Id_on Q) = NF R" by force

lemma NF_empty[simp]: "NF {} = UNIV" by auto

lemma normalizability_I: "(a, b) \<in> A^* \<Longrightarrow> b \<in> NF A \<Longrightarrow> (a, b) \<in> A^!"
by (simp add: normalizability_def)

lemma normalizability_I': "(a, b) \<in> A^* \<Longrightarrow> (b, c) \<in> A^! \<Longrightarrow> (a, c) \<in> A^!"
by (auto simp add: normalizability_def)

lemma normalizability_E: "(a, b) \<in> A^! \<Longrightarrow> ((a, b) \<in> A^* \<Longrightarrow> b \<in> NF A \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: normalizability_def)

declare normalizability_I'[intro]
declare normalizability_I[intro]
declare normalizability_E[elim]


subsection {* Properties of ARSs *}

text {*
  The following properties on (elements of) ARSs are defined: completeness,
  Church-Rosser property, semi-completeness, strong normalization, unique normal
  forms, Weak Church-Rosser property, and weak normalization. 
*}

definition CR_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "CR_on r A \<equiv> \<forall>a\<in>A. \<forall>b c. (a, b) \<in> r^* \<and> (a, c) \<in> r^* \<longrightarrow> (b, c) \<in> join r"

abbreviation CR :: "'a rel \<Rightarrow> bool" where
  "CR r \<equiv> CR_on r UNIV"

definition SN_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "SN_on r A \<equiv> \<not> (\<exists>f. f 0 \<in> A \<and> chain r f)"

abbreviation SN :: "'a rel \<Rightarrow> bool" where
  "SN r \<equiv> SN_on r UNIV"

text {* Alternative definition of @{term "SN"}. *}
lemma SN_def: "SN r = (\<forall>x. SN_on r {x})"
  unfolding SN_on_def by blast

definition UNF_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "UNF_on r A \<equiv> \<forall>a\<in>A. \<forall>b c. (a, b) \<in> r^! \<and> (a, c) \<in> r^! \<longrightarrow> b = c"

abbreviation UNF :: "'a rel \<Rightarrow> bool" where "UNF r \<equiv> UNF_on r UNIV"

definition WCR_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "WCR_on r A \<equiv> \<forall>a\<in>A. \<forall>b c. (a, b) \<in> r \<and> (a, c) \<in> r \<longrightarrow> (b, c) \<in> join r"

abbreviation WCR :: "'a rel \<Rightarrow> bool" where "WCR r \<equiv> WCR_on r UNIV"

definition WN_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "WN_on r A \<equiv> \<forall>a\<in>A. \<exists>b. (a, b) \<in> r^!"

abbreviation WN :: "'a rel \<Rightarrow> bool" where
  "WN r \<equiv> WN_on r UNIV"

lemmas CR_defs = CR_on_def
lemmas SN_defs = SN_on_def
lemmas UNF_defs = UNF_on_def
lemmas WCR_defs = WCR_on_def
lemmas WN_defs = WN_on_def

definition complete_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "complete_on r A \<equiv> SN_on r A \<and> CR_on r A"

abbreviation complete :: "'a rel \<Rightarrow> bool" where
  "complete r \<equiv> complete_on r UNIV"

definition semi_complete_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "semi_complete_on r A \<equiv>  WN_on r A \<and> CR_on r A"

abbreviation semi_complete :: "'a rel \<Rightarrow> bool" where
  "semi_complete r \<equiv> semi_complete_on r UNIV"

lemmas complete_defs = complete_on_def
lemmas semi_complete_defs = semi_complete_on_def

text {* Unique normal forms with respect to conversion. *}
definition
  UNC :: "'a rel \<Rightarrow> bool"
where
  "UNC A \<equiv> \<forall>a b. a \<in> NF A \<and> b \<in> NF A \<and> (a, b) \<in> A^<->* \<longrightarrow> a = b"

lemma complete_onI:
  "SN_on r A \<Longrightarrow> CR_on r A \<Longrightarrow> complete_on r A"
  by (simp add: complete_defs)

lemma complete_onE:
  "complete_on r A \<Longrightarrow> (SN_on r A \<Longrightarrow> CR_on r A \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: complete_defs)

lemma CR_onI:
  "(\<And>a b c. a \<in> A \<Longrightarrow> (a, b) \<in> r^* \<Longrightarrow> (a, c) \<in> r^* \<Longrightarrow> (b, c) \<in> join r) \<Longrightarrow> CR_on r A"
  by (simp add: CR_defs)

lemma CR_on_singletonI:
  "(\<And>b c. (a, b) \<in> r^* \<Longrightarrow> (a, c) \<in> r^* \<Longrightarrow> (b, c) \<in> join r) \<Longrightarrow> CR_on r {a}"
  by (simp add: CR_defs)

lemma CR_onE:
  "CR_on r A \<Longrightarrow> a \<in> A \<Longrightarrow> ((b, c) \<in> join r \<Longrightarrow> P) \<Longrightarrow> ((a, b) \<notin> r^* \<Longrightarrow> P) \<Longrightarrow> ((a, c) \<notin> r^* \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding CR_defs by blast

lemma CR_onD:
  "CR_on r A \<Longrightarrow> a \<in> A \<Longrightarrow> (a, b) \<in> r^* \<Longrightarrow> (a, c) \<in> r^* \<Longrightarrow> (b, c) \<in> join r"
  by (blast elim: CR_onE)

lemma semi_complete_onI: "WN_on r A \<Longrightarrow> CR_on r A \<Longrightarrow> semi_complete_on r A"
  by (simp add: semi_complete_defs)

lemma semi_complete_onE:
  "semi_complete_on r A \<Longrightarrow> (WN_on r A \<Longrightarrow> CR_on r A \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: semi_complete_defs)

declare semi_complete_onI[intro]
declare semi_complete_onE[elim]

declare complete_onI[intro]
declare complete_onE[elim]

declare CR_onI[intro]
declare CR_on_singletonI[intro]

declare CR_onD[dest]
declare CR_onE[elim]

lemma UNC_I:
  "(\<And>a b. a \<in> NF A \<Longrightarrow> b \<in> NF A \<Longrightarrow> (a, b) \<in> A^<->* \<Longrightarrow> a = b) \<Longrightarrow> UNC A"
  by (simp add: UNC_def)

lemma UNC_E:
  "\<lbrakk>UNC A; a = b \<Longrightarrow> P; a \<notin> NF A \<Longrightarrow> P; b \<notin> NF A \<Longrightarrow> P; (a, b) \<notin> A^<->* \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding UNC_def by blast

lemma UNF_onI: "(\<And>a b c. a \<in> A \<Longrightarrow> (a, b) \<in> r^! \<Longrightarrow> (a, c) \<in> r^! \<Longrightarrow> b = c) \<Longrightarrow> UNF_on r A"
  by (simp add: UNF_defs)

lemma UNF_onE:
  "UNF_on r A \<Longrightarrow> a \<in> A \<Longrightarrow> (b = c \<Longrightarrow> P) \<Longrightarrow> ((a, b) \<notin> r^! \<Longrightarrow> P) \<Longrightarrow> ((a, c) \<notin> r^! \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding UNF_on_def by blast

lemma UNF_onD:
  "UNF_on r A \<Longrightarrow> a \<in> A \<Longrightarrow> (a, b) \<in> r^! \<Longrightarrow> (a, c) \<in> r^! \<Longrightarrow> b = c"
  by (blast elim: UNF_onE)

declare UNF_onI[intro]
declare UNF_onD[dest]
declare UNF_onE[elim]

lemma SN_onI:
  assumes "\<And>f. \<lbrakk>f 0 \<in> A; chain r f\<rbrakk> \<Longrightarrow> False"
  shows "SN_on r A"
  using assms unfolding SN_defs by blast

lemma SN_I: "(\<And>a. SN_on A {a}) \<Longrightarrow> SN A"
  unfolding SN_on_def by blast

lemma SN_on_trancl_imp_SN_on:
  assumes "SN_on (R^+) T" shows "SN_on R T"
proof (rule ccontr)
  assume "\<not> SN_on R T"
  then obtain s where "s 0 \<in> T" and "chain R s" unfolding SN_defs by auto
  hence "chain (R^+) s" by auto
  with `s 0 \<in> T` have "\<not> SN_on (R^+) T" unfolding SN_defs by auto
  with assms show False by simp
qed

lemma SN_onE:
  assumes "SN_on r A"
    and "\<not> (\<exists>f. f 0 \<in> A \<and> chain r f) \<Longrightarrow> P"
  shows "P"
  using assms unfolding SN_defs by simp

lemma not_SN_onE:
  assumes "\<not> SN_on r A"
    and "\<And>f. \<lbrakk>f 0 \<in> A; chain r f\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms unfolding SN_defs by blast

declare SN_onI[intro]
declare SN_onE[elim]
declare not_SN_onE[Pure.elim, elim]

lemma refl_not_SN: "(x, x) \<in> R \<Longrightarrow> \<not> SN R"
  unfolding SN_defs by force

lemma SN_on_irrefl:
  assumes "SN_on r A"
  shows "\<forall>a\<in>A. (a, a) \<notin> r"
proof (intro ballI notI)
  fix a assume "a \<in> A" and "(a, a) \<in> r"
  with assms show False unfolding SN_defs by auto
qed

lemma WCR_onI: "(\<And>a b c. a \<in> A \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> (a, c) \<in> r \<Longrightarrow> (b, c) \<in> join r) \<Longrightarrow> WCR_on r A"
  by (simp add: WCR_defs)

lemma WCR_onE:
  "WCR_on r A \<Longrightarrow> a \<in> A \<Longrightarrow> ((b, c) \<in> join r \<Longrightarrow> P) \<Longrightarrow> ((a, b) \<notin> r \<Longrightarrow> P) \<Longrightarrow> ((a, c) \<notin> r \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding WCR_on_def by blast

lemma SN_nat_bounded: "SN {(x,y :: nat). x < y \<and> y \<le> b}" (is "SN ?R")
proof 
  fix f
  assume "chain ?R f"
  hence steps: "\<And>i. (f i, f (Suc i)) \<in> ?R" ..
  {
    fix i
    have inc: "f 0 + i \<le> f i"
    proof (induct i)
      case 0 thus ?case by auto
    next
      case (Suc i)
      have "f 0 + Suc i \<le> f i + Suc 0" using Suc by simp
      also have "... \<le> f (Suc i)" using steps[of i]
        by auto
      finally show ?case by simp
    qed
  }
  from this[of "Suc b"] steps[of b]
  show False by simp
qed

lemma WCR_onD:
  "WCR_on r A \<Longrightarrow> a \<in> A \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> (a, c) \<in> r \<Longrightarrow> (b, c) \<in> join r"
  by (blast elim: WCR_onE)

lemma WN_onI: "(\<And>a. a \<in> A \<Longrightarrow> \<exists>b. (a, b) \<in> r^!) \<Longrightarrow> WN_on r A"
  by (auto simp: WN_defs)

lemma WN_onE: "WN_on r A \<Longrightarrow> a \<in> A \<Longrightarrow> (\<And>b. (a, b) \<in> r^! \<Longrightarrow> P) \<Longrightarrow> P"
 unfolding WN_defs by blast

lemma WN_onD: "WN_on r A \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>b. (a, b) \<in> r^!"
  by (blast elim: WN_onE)

declare WCR_onI[intro]
declare WCR_onD[dest]
declare WCR_onE[elim]

declare WN_onI[intro]
declare WN_onD[dest]
declare WN_onE[elim]

text {*
  Restricting a relation @{term r} to those elements that are strongly
  normalizing with respect to a relation @{term s}.
*}
definition
  restrict_SN :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" 
where
  "restrict_SN r s \<equiv> {(a, b) | a b. (a, b) \<in> r \<and> SN_on s {a}}"

lemma SN_restrict_SN_idemp[simp]: "SN (restrict_SN A A)"
  by (auto simp: restrict_SN_def SN_defs)

lemma SN_on_Image:
  assumes "SN_on r A"
  shows "SN_on r (r `` A)"
proof
  fix f
  assume "f 0 \<in> r `` A" and chain: "chain r f"
  then obtain a where "a \<in> A" and 1: "(a, f 0) \<in> r" by auto
  let ?g = "a #s f"
  from cons_chain[OF 1 chain] have "chain r ?g" .
  moreover have "?g 0 \<in> A" by (simp add: `a \<in> A`)
  ultimately have "\<not> SN_on r A" unfolding SN_defs by best
  with assms show False by simp
qed

lemma SN_on_subset2:
  assumes "A \<subseteq> B" and "SN_on r B"
  shows "SN_on r A"
  using assms unfolding SN_on_def by blast

lemma step_preserves_SN_on:
  assumes 1: "(a, b) \<in> r"
    and 2: "SN_on r {a}"
  shows "SN_on r {b}"
  using 1 and SN_on_Image[OF 2] and SN_on_subset2[of "{b}" "r `` {a}"] by auto

lemma steps_preserve_SN_on: "(a, b) \<in> A^* \<Longrightarrow> SN_on A {a} \<Longrightarrow> SN_on A {b}"
  by (induct rule: rtrancl.induct) (auto simp: step_preserves_SN_on)

(*FIXME: move*)
lemma relpow_seq:
  assumes "(x, y) \<in> r^^n"
  shows "\<exists>f. f 0 = x \<and> f n = y \<and> (\<forall>i<n. (f i, f (Suc i)) \<in> r)"
using assms
proof (induct n arbitrary: y)
  case 0 thus ?case by auto
next
  case (Suc n)
  then obtain z where "(x, z) \<in> r^^n" and "(z, y) \<in> r" by auto
  from Suc(1)[OF `(x, z) \<in> r^^n`]
    obtain f where "f 0 = x" and "f n = z" and seq: "\<forall>i<n. (f i, f (Suc i)) \<in> r" by auto
  let ?n = "Suc n"
  let ?f = "\<lambda>i. if i = ?n then y else f i"
  have "?f ?n = y" by simp
  from `f 0 = x` have "?f 0 = x" by simp
  from seq have seq': "\<forall>i<n. (?f i, ?f (Suc i)) \<in> r" by auto
  with `f n = z` and `(z, y) \<in> r` have "\<forall>i<?n. (?f i, ?f (Suc i)) \<in> r" by auto
  with `?f 0 = x` and `?f ?n = y` show ?case by best
qed

lemma rtrancl_imp_seq:
  assumes "(x, y) \<in> r^*"
  shows "\<exists>f n. f 0 = x \<and> f n = y \<and> (\<forall>i<n. (f i, f (Suc i)) \<in> r)"
  using assms[unfolded rtrancl_power] and relpow_seq[of x y _ r] by blast

lemma SN_on_Image_rtrancl:
  assumes "SN_on r A"
  shows "SN_on r (r^* `` A)"
proof
  fix f
  assume f0: "f 0 \<in> r^* `` A" and chain: "chain r f"
  then obtain a where a: "a \<in> A" and "(a, f 0) \<in> r^*" by auto
  then obtain n where "(a, f 0) \<in> r^^n" unfolding rtrancl_power by auto
  show False
  proof (cases n)
    case 0
    with `(a, f 0) \<in> r^^n` have "f 0 = a" by simp
    hence "f 0 \<in> A" by (simp add: a)
    with chain have "\<not> SN_on r A" by auto
    with assms show False by simp
  next
    case (Suc m)
    from relpow_seq[OF `(a, f 0) \<in> r^^n`]
      obtain g where g0: "g 0 = a" and "g n = f 0"
      and gseq: "\<forall>i<n. (g i, g (Suc i)) \<in> r" by auto
    let ?f = "\<lambda>i. if i < n then g i else f (i - n)"
    have "chain r ?f"
    proof
      fix i
      {
        assume "Suc i < n"
        hence "(?f i, ?f (Suc i)) \<in> r" by (simp add: gseq)
      }
      moreover
      {
        assume "Suc i > n"
        hence eq: "Suc (i - n) = Suc i - n" by arith
        from chain have "(f (i - n), f (Suc (i - n))) \<in> r" by simp
        hence "(f (i - n), f (Suc i - n)) \<in> r" by (simp add: eq)
        with `Suc i > n` have "(?f i, ?f (Suc i)) \<in> r" by simp
      }
      moreover
      {
        assume "Suc i = n"
        hence eq: "f (Suc i - n) = g n" by (simp add: `g n = f 0`)
        from `Suc i = n` have eq': "i = n - 1" by arith
        from gseq have "(g i, f (Suc i - n)) \<in> r" unfolding eq by (simp add: Suc eq')
        hence "(?f i, ?f (Suc i)) \<in> r" using `Suc i = n` by simp
      }
      ultimately show "(?f i, ?f (Suc i)) \<in> r" by simp
    qed
    moreover have "?f 0 \<in> A"
    proof (cases n)
      case 0
      with `(a, f 0) \<in> r^^n` have eq: "a = f 0" by simp
      from a show ?thesis by (simp add: eq 0)
    next
      case (Suc m)
      thus ?thesis by (simp add: a g0)
    qed
    ultimately have "\<not> SN_on r A" unfolding SN_defs by best
    with assms show False by simp
  qed
qed

(* FIXME: move somewhere else *)
lemma subsetI2[Pure.intro]: "(\<And>x y. (x,y) \<in> A \<Longrightarrow> (x,y) \<in> B) \<Longrightarrow> A \<subseteq> B" by auto

lemma restrict_SN_trancl_simp[simp]: "(restrict_SN A A)^+ = restrict_SN (A^+) A" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix a b assume "(a, b) \<in> ?lhs" thus "(a, b) \<in> ?rhs"
      unfolding restrict_SN_def by (induct rule: trancl.induct) auto
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix a b assume "(a, b) \<in> ?rhs"
    hence "(a, b) \<in> A^+" and "SN_on A {a}" unfolding restrict_SN_def by auto
    thus "(a, b) \<in> ?lhs"
    proof (induct rule: trancl.induct)
      case (r_into_trancl x y) thus ?case unfolding restrict_SN_def by auto
    next
      case (trancl_into_trancl a b c)
      hence IH: "(a, b) \<in> ?lhs" by auto
      from trancl_into_trancl have "(a, b) \<in> A^*" by auto
      from this and `SN_on A {a}` have "SN_on A {b}" by (rule steps_preserve_SN_on)
      with `(b, c) \<in> A` have "(b, c) \<in> ?lhs" unfolding restrict_SN_def by auto
      with IH show ?case by simp
    qed
  qed
qed

lemma SN_imp_WN: assumes "SN A" shows "WN A"
proof -
  from `SN A` have "wf (A^-1)" by (simp add: SN_defs wf_iff_no_infinite_down_chain)
  show "WN A"
  proof
    fix a
    show "\<exists>b. (a, b) \<in> A^!" unfolding normalizability_def NF_def Image_def
      by (rule wfE_min[OF `wf (A^-1)`, of a "A^* `` {a}", simplified])
         (auto intro: rtrancl_into_rtrancl)
  qed
qed

lemma UNC_imp_UNF:
 assumes "UNC r" shows "UNF r"
proof - {
  fix x y z assume "(x,y) \<in> r^!" and "(x,z) \<in> r^!"
  hence "(x,y) \<in> r^*" and "(x,z) \<in> r^*" and "y \<in> NF r" and "z \<in> NF r" by auto
  hence "(x,y) \<in> r^<->*" and "(x,z) \<in> r^<->*" by auto
  hence "(z,x) \<in> r^<->*" using conversion_sym unfolding sym_def by best
  with `(x,y) \<in> r^<->*` have "(z,y) \<in> r^<->*" using conversion_trans unfolding trans_def by best
  from assms and this and `z \<in> NF r` and `y \<in> NF r` have "z = y" unfolding UNC_def by auto
} thus ?thesis by auto
qed

lemma join_NF_imp_eq:
 assumes "(x,y) \<in> r\<^sup>\<down>" and "x \<in> NF r" and "y \<in> NF r"
 shows "x = y"
proof -
  from `(x,y) \<in> r\<^sup>\<down>` obtain z where "(x,z)\<in>r^*" and "(z,y)\<in>(r\<inverse>)^*" unfolding join_def by auto
  hence "(y,z) \<in> r^*" unfolding rtrancl_converse by simp
  from `x \<in> NF r` have "(x,z) \<notin> r^+" using NF_no_trancl_step by best
  hence "x = z" using rtranclD[OF `(x,z) \<in> r^*`] by auto
  from `y \<in> NF r` have "(y,z) \<notin> r^+" using NF_no_trancl_step by best
  hence "y = z" using rtranclD[OF `(y,z) \<in> r^*`] by auto
  with `x = z` show ?thesis by simp
qed

lemma CR_iff_meet_subset_join: "CR r = (r\<^sup>\<up> \<subseteq> r\<^sup>\<down>)"
proof
 assume "CR r" show "r\<^sup>\<up> \<subseteq> r\<^sup>\<down>"
 proof (rule subsetI2)
  fix x y assume "(x,y) \<in> r\<^sup>\<up>"
  then obtain z where "(z,x) \<in> r^*" and "(z,y) \<in> r^*" using meetD by best
  with `CR r` show "(x,y) \<in> r\<^sup>\<down>" by (auto simp: CR_defs)
 qed
next
 assume "r\<^sup>\<up> \<subseteq> r\<^sup>\<down>" {
  fix x y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
  hence "(y,z) \<in> r\<^sup>\<up>" unfolding meet_def rtrancl_converse by auto
  with `r\<^sup>\<up> \<subseteq> r\<^sup>\<down>` have "(y,z) \<in> r\<^sup>\<down>" by auto
 } thus "CR r" by (auto simp: CR_defs)
qed

lemma CR_divergence_imp_join:
  assumes "CR r" and "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
  shows "(y,z) \<in> r\<^sup>\<down>"
using assms by auto

lemma join_imp_conversion: "r\<^sup>\<down> \<subseteq> r^<->*"
proof
  fix x z assume "(x,z) \<in> r\<^sup>\<down>"
  then obtain y where "(x,y) \<in> r^*" and "(z,y) \<in> r^*" by auto
  hence "(x,y) \<in> r^<->*" and "(z,y) \<in> r^<->*" by auto
  from `(z,y) \<in> r^<->*` have "(y,z) \<in> r^<->*" using conversion_sym unfolding sym_def by best
  with `(x,y) \<in> r^<->*` show "(x,z) \<in> r^<->*" using conversion_trans unfolding trans_def by best
qed

lemma meet_imp_conversion: "r\<^sup>\<up> \<subseteq> r^<->*"
proof (rule subsetI2)
  fix y z assume "(y,z) \<in> r\<^sup>\<up>"
  then obtain x where "(x,y) \<in> r^*" and "(x,z) \<in> r^*" by auto
  hence "(x,y) \<in> r^<->*" and "(x,z) \<in> r^<->*" by auto
  from `(x,y) \<in> r^<->*` have "(y,x) \<in> r^<->*" using conversion_sym unfolding sym_def by best
  with `(x,z) \<in> r^<->*` show "(y,z) \<in> r^<->*" using conversion_trans unfolding trans_def by best
qed

lemma CR_imp_UNF: assumes "CR r" shows "UNF r"
proof - {
fix x y z assume "(x,y) \<in> r^!" and "(x,z) \<in> r^!"
  hence "(x,y) \<in> r^*" and "y \<in> NF r" and "(x,z) \<in> r^*" and "z \<in> NF r"
    unfolding normalizability_def by auto
  from assms and `(x,y) \<in> r^*` and `(x,z) \<in> r^*` have "(y,z) \<in> r\<^sup>\<down>"
    by (rule CR_divergence_imp_join)
  from this and `y \<in> NF r` and `z \<in> NF r` have "y = z" by (rule join_NF_imp_eq)
} thus ?thesis by auto
qed

lemma CR_iff_conversion_imp_join: "CR r = (r^<->* \<subseteq> r\<^sup>\<down>)"
proof (intro iffI subsetI2)
  fix x y assume "CR r" and "(x,y) \<in> r^<->*"
  then obtain n where "(x,y) \<in> (r\<^sup>\<leftrightarrow>)^^n" unfolding conversion_def rtrancl_is_UN_relpow by auto
  thus "(x,y) \<in> r\<^sup>\<down>"
  proof (induct n arbitrary: x)
    case 0
    assume "(x,y) \<in> r\<^sup>\<leftrightarrow> ^^ 0" hence "x = y" by simp
    show ?case unfolding `x = y` by auto
  next
    case (Suc n)
    from `(x,y) \<in> r\<^sup>\<leftrightarrow> ^^ Suc n` obtain  z where "(x,z) \<in> r\<^sup>\<leftrightarrow>" and "(z,y) \<in> r\<^sup>\<leftrightarrow> ^^ n"
      using relpow_Suc_D2 by best
    with Suc have "(z,y) \<in> r\<^sup>\<down>" by simp
    from `(x,z) \<in> r\<^sup>\<leftrightarrow>` show ?case
    proof
      assume "(x,z) \<in> r" with `(z,y) \<in> r\<^sup>\<down>` show ?thesis by (auto intro: rtrancl_join_join)
    next
      assume "(x,z) \<in> r^-1"
      hence "(z,x) \<in> r^*" by simp
      from `(z,y) \<in> r\<^sup>\<down>` obtain z' where "(z,z') \<in> r^*" and "(y,z') \<in> r^*" by auto
      from `CR r` and `(z,x) \<in> r^*` and `(z,z') \<in> r^*` have "(x,z') \<in> r\<^sup>\<down>"
        by (rule CR_divergence_imp_join)
      then obtain x' where "(x,x') \<in> r^*" and "(z',x') \<in> r^*" by auto
      with `(y,z') \<in> r^*` show ?thesis by auto
    qed
  qed
next
  assume "r^<->* \<subseteq> r\<^sup>\<down>" thus "CR r" unfolding CR_iff_meet_subset_join
    using meet_imp_conversion by auto
qed

lemma CR_imp_conversionIff_join: assumes "CR r" shows "r^<->* = r\<^sup>\<down>"
proof
  show "r^<->* \<subseteq> r\<^sup>\<down>" using CR_iff_conversion_imp_join assms by auto
next
  show "r\<^sup>\<down> \<subseteq> r^<->*" by (rule join_imp_conversion)
qed

lemma join_sym: "sym (join r)" unfolding sym_def by auto

lemma CR_join_left_I:
  assumes "CR r" and "(x,y) \<in> r^*" and "(x,z) \<in> r\<^sup>\<down>" shows "(y,z) \<in> r\<^sup>\<down>"
proof -
  from `(x,z) \<in> r\<^sup>\<down>` obtain x' where "(x,x') \<in> r^*" and "(z,x') \<in> r\<^sup>\<down>" by auto
  from `CR r` and `(x,x') \<in> r^*` and `(x,y) \<in> r^*` have "(x,y) \<in> r\<^sup>\<down>" by auto
  hence "(y,x) \<in> r\<^sup>\<down>" using join_sym unfolding sym_def by best
  from `CR r` have "r^<->* = r\<^sup>\<down>" by (rule CR_imp_conversionIff_join)
  from `(y,x) \<in> r\<^sup>\<down>` and `(x,z) \<in> r\<^sup>\<down>` show ?thesis using conversion_trans
    unfolding trans_def `r^<->* = r\<^sup>\<down>`[symmetric] by best
qed

lemma CR_join_right_I:
 assumes "CR r" and "(x,y) \<in> r\<^sup>\<down>" and "(y,z) \<in> r^*" shows "(x,z) \<in> r\<^sup>\<down>"
proof -
  have "r^<->* = r\<^sup>\<down>" by (rule CR_imp_conversionIff_join[OF `CR r`])
  from `(y,z) \<in> r^*` have "(y,z) \<in> r^<->*" by auto
  with `(x,y) \<in> r\<^sup>\<down>` show ?thesis unfolding `r^<->* = r\<^sup>\<down>`[symmetric] using conversion_trans
    unfolding trans_def by fast
qed

lemma NF_not_suc: assumes "(x,y) \<in> r^*" and "x \<in> NF r" shows "x = y"
proof -
  from `x \<in> NF r` have "\<forall>y. (x,y) \<notin> r" using NF_no_step by auto
  hence "x \<notin> Domain r" unfolding Domain_unfold by simp
  from `(x,y) \<in> r^*` show ?thesis unfolding Not_Domain_rtrancl[OF `x \<notin> Domain r`] by simp
qed

lemma semi_complete_imp_conversionIff_same_NF:
  assumes "semi_complete r"
  shows "((x,y) \<in> r^<->*) = (\<forall>u v. (x,u) \<in> r^! \<and> (y,v) \<in> r^! \<longrightarrow> u = v)"
proof -
  from assms have "WN r" and "CR r" unfolding semi_complete_defs by auto
  hence "r^<->* = r\<^sup>\<down>" using CR_imp_conversionIff_join by auto
  show ?thesis
  proof
    assume "(x,y) \<in> r^<->*"
    from `(x,y) \<in> r^<->*` have "(x,y) \<in> r\<^sup>\<down>" unfolding `r^<->* = r\<^sup>\<down>` .
    show "\<forall>u v. (x,u) \<in> r^! \<and> (y,v) \<in> r^! \<longrightarrow> u = v"
    proof (intro allI impI, elim conjE)
      fix u v assume "(x,u) \<in> r^!" and "(y,v) \<in> r^!"
      hence "(x,u) \<in> r^*" and "(y,v) \<in> r^*" and "u \<in> NF r" and "v \<in> NF r" by auto
      from `CR r` and `(x,u) \<in> r^*` and `(x,y) \<in> r\<^sup>\<down>` have "(u,y) \<in> r\<^sup>\<down>"
        by (auto intro: CR_join_left_I)
      hence "(y,u) \<in> r\<^sup>\<down>" using join_sym unfolding sym_def by best
      with `(x,y) \<in> r\<^sup>\<down>` have "(x,u) \<in> r\<^sup>\<down>" unfolding `r^<->* = r\<^sup>\<down>`[symmetric]
        using conversion_trans unfolding trans_def by best
      from `CR r` and `(x,y) \<in> r\<^sup>\<down>` and `(y,v) \<in> r^*` have "(x,v) \<in> r\<^sup>\<down>"
        by (auto intro: CR_join_right_I)
      hence "(v,x) \<in> r\<^sup>\<down>" using join_sym unfolding sym_def by best
      with `(x,u) \<in> r\<^sup>\<down>` have "(v,u) \<in> r\<^sup>\<down>" unfolding `r^<->* = r\<^sup>\<down>`[symmetric]
        using conversion_trans unfolding trans_def by best
      then obtain v' where "(v,v') \<in> r^*" and "(u,v') \<in> r^*" by auto
      from `(u,v') \<in> r^*` and `u \<in> NF r` have "u = v'" by (rule NF_not_suc)
      from `(v,v') \<in> r^*` and `v \<in> NF r` have "v = v'" by (rule NF_not_suc)
      thus "u = v" unfolding `u = v'` by simp
    qed
  next
    assume equal_NF:"\<forall>u v. (x,u) \<in> r^! \<and> (y,v) \<in> r^! \<longrightarrow> u = v"
    from `WN r` obtain u where "(x,u) \<in> r^!" by auto
    from `WN r` obtain v where "(y,v) \<in> r^!" by auto
    from `(x,u) \<in> r^!` and `(y,v) \<in> r^!` have "u = v" using equal_NF by simp
    from `(x,u) \<in> r^!` and `(y,v) \<in> r^!` have "(x,v) \<in> r^*" and "(y,v) \<in> r^*"
      unfolding `u = v` by auto
    hence "(x,v) \<in> r^<->*" and "(y,v) \<in> r^<->*" by auto
    from `(y,v) \<in> r^<->*` have "(v,y) \<in> r^<->*" using conversion_sym unfolding sym_def by best
    with `(x,v) \<in> r^<->*` show "(x,y) \<in> r^<->*" using conversion_trans unfolding trans_def by best
  qed
qed

lemma CR_imp_UNC: assumes "CR r" shows "UNC r"
proof - {
  fix x y assume "x \<in> NF r" and "y \<in> NF r" and "(x,y) \<in> r^<->*"
  have "r^<->* = r\<^sup>\<down>" by (rule CR_imp_conversionIff_join [OF assms])
  from `(x,y) \<in> r^<->*` have "(x,y) \<in> r\<^sup>\<down>" unfolding `r^<->* = r\<^sup>\<down>` by simp
  then obtain x' where "(x,x') \<in> r^*" and "(y,x') \<in> r^*" by best
  from `(x,x') \<in> r^*` and `x \<in> NF r` have "x = x'" by (rule NF_not_suc)
  from `(y,x') \<in> r^*` and `y \<in> NF r` have "y = x'" by (rule NF_not_suc)
  hence "x = y" unfolding `x = x'` by simp
} thus ?thesis by (auto simp: UNC_def)
qed

lemma WN_UNF_imp_CR: assumes "WN r" and "UNF r" shows "CR r"
proof - {
  fix x y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
  from assms obtain y' where "(y,y') \<in> r^!" unfolding WN_defs by best
  with `(x,y) \<in> r^*` have "(x,y') \<in> r^!" by auto
  from assms obtain z' where "(z,z') \<in> r^!" unfolding WN_defs by best
  with `(x,z) \<in> r^*` have "(x,z') \<in> r^!" by auto
  with `(x,y') \<in> r^!` have "y' = z'" using `UNF r` unfolding UNF_defs by auto
  from `(y,y') \<in> r^!` and `(z,z') \<in> r^!` have "(y,z) \<in> r\<^sup>\<down>" unfolding `y' = z'` by auto
} thus ?thesis by auto
qed

definition diamond :: "'a rel \<Rightarrow> bool" ("\<diamond>") where "\<diamond> r \<equiv> (r\<inverse> O r) \<subseteq> (r O r\<inverse>)"

lemma diamond_I[intro]: "(r\<inverse> O r) \<subseteq> (r O r\<inverse>) \<Longrightarrow> \<diamond> r" unfolding diamond_def by simp

lemma diamond_E[elim]: "\<diamond> r \<Longrightarrow> ((r\<inverse> O r) \<subseteq> (r O r\<inverse>) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding diamond_def by simp

lemma diamond_imp_semi_confluence: assumes "\<diamond> r" shows "(r\<inverse> O r^*) \<subseteq> r\<^sup>\<down>"
proof (rule subsetI2)
  fix y z assume "(y,z) \<in>  r\<inverse> O r^*"
  then obtain x where "(x,y) \<in> r" and "(x,z) \<in> r^*" by best
  then obtain n where "(x,z) \<in> r^^n" using rtrancl_imp_UN_relpow by best
  with `(x,y) \<in> r` show "(y,z) \<in> r\<^sup>\<down>"
  proof (induct n arbitrary: x z y)
    case 0 thus ?case by auto
  next
    case (Suc n)
    from `(x,z) \<in> r^^Suc n` obtain x' where "(x,x') \<in> r" and "(x',z) \<in> r^^n"
      using relpow_Suc_D2 by best
    with `(x,y) \<in> r` have "(y,x') \<in> (r\<inverse> O r)" by auto
    with `\<diamond> r` have "(y,x') \<in> (r O r\<inverse>)" by auto
    then obtain y' where "(x',y') \<in> r" and "(y,y') \<in> r" by best
    with Suc and `(x',z) \<in> r^^n` have "(y',z) \<in> r\<^sup>\<down>" by auto
    with `(y,y') \<in> r` show ?case by (auto intro: rtrancl_join_join)
  qed
qed

lemma semi_confluence_imp_CR: assumes "(r\<inverse> O r^*) \<subseteq> r\<^sup>\<down>" shows "CR r"
proof - {
  fix x y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
  then obtain n where "(x,z) \<in> r^^n" using rtrancl_imp_UN_relpow by best
  with `(x,y) \<in> r^*` have "(y,z) \<in> r\<^sup>\<down>"
  proof (induct n arbitrary: x y z)
    case 0 thus ?case by auto
  next
    case (Suc n)
    from `(x,z) \<in> r^^Suc n` obtain x' where "(x,x') \<in> r" and "(x',z) \<in> r^^n"
      using relpow_Suc_D2 by best
    from `(x,x') \<in> r` and `(x,y) \<in> r^*` have "(x',y) \<in> (r\<inverse> O r^* )" by auto
    with assms have "(x',y) \<in> r\<^sup>\<down>" by auto
    then obtain y' where "(x',y') \<in> r^*" and "(y,y') \<in> r^*" by best
    with Suc and `(x',z) \<in> r^^n` have "(y',z) \<in> r\<^sup>\<down>" by simp
    then obtain u where "(z,u) \<in> r^*" and "(y',u) \<in> r^*" by best
    from `(y,y') \<in> r^*` and `(y',u) \<in> r^*` have "(y,u) \<in> r^*" by auto
    with `(z,u) \<in> r^*` show ?case by best
  qed
} thus ?thesis by auto
qed
 
lemma diamond_imp_CR: assumes "\<diamond> r" shows "CR r"
  using assms by (rule diamond_imp_semi_confluence[THEN semi_confluence_imp_CR])

lemma diamond_imp_CR':
  assumes "\<diamond> s" and "r \<subseteq> s" and "s \<subseteq> r^*" shows "CR r"
  unfolding CR_iff_meet_subset_join
proof -
  from `\<diamond> s` have "CR s" by (rule diamond_imp_CR)
  hence "s\<^sup>\<up> \<subseteq> s\<^sup>\<down>" unfolding CR_iff_meet_subset_join by simp
  from `r \<subseteq> s` have "r^* \<subseteq> s^*" by (rule rtrancl_mono)
  from `s \<subseteq> r^*` have "s^* \<subseteq> (r^*)^*" by (rule rtrancl_mono)
  hence "s^* \<subseteq> r^*" by simp
  with `r^* \<subseteq> s^*` have "r^* = s^*" by simp
  show "r\<^sup>\<up> \<subseteq> r\<^sup>\<down>" unfolding meet_def join_def rtrancl_converse `r^* = s^*`
    unfolding rtrancl_converse[symmetric] meet_def[symmetric]
      join_def[symmetric] by (rule `s\<^sup>\<up> \<subseteq> s\<^sup>\<down>`)
qed

lemma SN_imp_minimal:
  assumes "SN A"
  shows "\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z, y) \<in> A \<longrightarrow> y \<notin> Q)"
proof (rule ccontr)
  assume "\<not> (\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z, y) \<in> A \<longrightarrow> y \<notin> Q))"
  then obtain Q x where "x \<in> Q" and "\<forall>z\<in>Q. \<exists>y. (z, y) \<in> A \<and> y \<in> Q" by auto
  hence "\<forall>z. \<exists>y. z \<in> Q \<longrightarrow> (z, y) \<in> A \<and> y \<in> Q" by auto
  hence "\<exists>f. \<forall>x. x \<in> Q \<longrightarrow> (x, f x) \<in> A \<and> f x \<in> Q" by (rule choice)
  then obtain f where a:"\<forall>x. x \<in> Q \<longrightarrow> (x,f x) \<in> A \<and> f x \<in> Q" (is "\<forall>x. ?P x") by best
  let ?S = "\<lambda>i. (f ^^ i) x"
  have "?S 0 = x" by simp
  have "\<forall>i. (?S i, ?S (Suc i)) \<in> A \<and> ?S (Suc i) \<in> Q"
  proof
    fix i show "(?S i, ?S (Suc i)) \<in> A \<and> ?S (Suc i) \<in> Q"
      by (induct i) (auto simp: `x \<in> Q` a)
  qed
  with `?S 0 = x` have "\<exists>S. S 0 = x \<and> chain A S" by fast
  with assms show False by auto
qed

lemma SN_on_imp_on_minimal:
  assumes "SN_on r {x}"
  shows "\<forall>Q. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z, y) \<in> r \<longrightarrow> y \<notin> Q)"
proof (rule ccontr)
  assume "\<not>(\<forall>Q. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> Q))"
  then obtain Q where "x \<in> Q" and "\<forall>z\<in>Q. \<exists>y. (z,y) \<in> r \<and> y \<in> Q" by auto
  hence "\<forall>z. \<exists>y. z \<in> Q \<longrightarrow> (z,y) \<in> r \<and> y \<in> Q" by auto
  hence "\<exists>f. \<forall>x. x \<in> Q \<longrightarrow> (x,f x) \<in> r \<and> f x \<in> Q" by (rule choice)
  then obtain f where a: "\<forall>x. x \<in> Q \<longrightarrow> (x,f x) \<in> r \<and> f x \<in> Q" (is "\<forall>x. ?P x") by best
  let ?S = "\<lambda>i. (f ^^ i) x"
  have "?S 0 = x" by simp
  have "\<forall>i. (?S i,?S(Suc i)) \<in> r \<and> ?S(Suc i) \<in> Q"
  proof
    fix i show "(?S i,?S(Suc i)) \<in> r \<and> ?S(Suc i) \<in> Q" by (induct i) (auto simp:`x \<in> Q` a)
  qed
  with `?S 0 = x` have "\<exists>S. S 0 = x \<and> chain r S" by fast
  with assms show False by auto
qed

lemma minimal_imp_wf:
  assumes "\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> Q)"
  shows "wf(r\<inverse>)"
proof (rule ccontr)
  assume "\<not> wf(r\<inverse>)"
  hence "\<exists>P. (\<forall>x. (\<forall>y. (x,y) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<and> (\<exists>x. \<not> P x)" unfolding wf_def by simp
  then obtain P x where suc:"\<forall>x. (\<forall>y. (x,y) \<in> r \<longrightarrow> P y) \<longrightarrow> P x" and "\<not> P x" by auto
  let ?Q = "{x. \<not> P x}"
  from `\<not> P x` have "x \<in> ?Q" by simp
  from assms have "\<forall>x. x \<in> ?Q \<longrightarrow> (\<exists>z\<in>?Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> ?Q)" by (rule allE[where x = ?Q])
  with `x \<in> ?Q` obtain z where "z \<in> ?Q" and min:" \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> ?Q" by best
  from `z \<in> ?Q` have "\<not> P z" by simp
  with suc obtain y where "(z,y) \<in> r" and "\<not> P y" by best
  hence "y \<in> ?Q" by simp
  with `(z,y) \<in> r` and min show False by simp
qed

lemmas SN_imp_wf = SN_imp_minimal[THEN minimal_imp_wf]

lemma wf_imp_SN: assumes "wf (A\<inverse>)" shows "SN A"
proof - {
  fix a
  let ?P = "\<lambda>a. \<not>(\<exists>S. S 0 = a \<and> chain A S)"
  from `wf (A\<inverse>)` have "?P a"
  proof induct
    case (less a)
    hence IH: "\<And>b. (a,b) \<in> A \<Longrightarrow> ?P b" by auto
    show "?P a"
    proof (rule ccontr)
      assume "\<not> ?P a"
      then obtain S where "S 0 = a" and "chain A S" by auto
      hence "(S 0, S 1) \<in> A" by auto
      with IH have "?P (S 1)" unfolding `S 0 = a` by auto
      with `chain A S` show False by auto
    qed
  qed
  hence "SN_on A {a}" unfolding SN_defs by auto
} thus ?thesis by best
qed

lemma SN_nat_gt: "SN {(a,b :: nat) . a > b}"
proof -
  from wf_less have "wf ({(x,y) . (x :: nat) > y}^-1)" unfolding converse_unfold by auto
  from wf_imp_SN[OF this] show ?thesis .
qed


lemma SN_iff_wf: "SN A = wf (A\<inverse>)" by (auto simp: SN_imp_wf wf_imp_SN)

lemma SN_imp_acyclic: "SN R \<Longrightarrow> acyclic R"
  using wf_acyclic[of "R^-1", unfolded SN_iff_wf[symmetric]] by auto

lemma SN_induct:
  assumes sn: "SN r" and step: "\<And>a. (\<And>b. (a, b) \<in> r \<Longrightarrow> P b) \<Longrightarrow> P a"
  shows "P a"
using sn unfolding SN_iff_wf proof induct
  case (less a)
  with step show ?case by best
qed

(* The same as well-founded induction, but in the 'correct' direction. *)
lemmas SN_induct_rule = SN_induct[consumes 1, case_names IH, induct pred: SN]

lemma SN_on_induct[consumes 2, case_names IH, induct pred: SN_on]:
  assumes SN: "SN_on R A"
    and "s \<in> A"
    and imp: "\<And>t. (\<And>u. (t, u) \<in> R \<Longrightarrow> P u) \<Longrightarrow> P t"
  shows "P s"
proof -
  let ?R = "restrict_SN R R"
  let ?P = "\<lambda>t. SN_on R {t} \<longrightarrow> P t"
  have "SN_on R {s} \<longrightarrow> P s"
  proof (rule SN_induct[OF SN_restrict_SN_idemp[of R], of ?P])
    fix a
    assume ind: "\<And>b. (a, b) \<in> ?R \<Longrightarrow> SN_on R {b} \<longrightarrow> P b"
    show "SN_on R {a} \<longrightarrow> P a"
    proof
      assume SN: "SN_on R {a}"
      show "P a"
      proof (rule imp)
        fix b
        assume "(a, b) \<in> R"
        with SN step_preserves_SN_on[OF this SN]
        show "P b" using ind[of b] unfolding restrict_SN_def by auto
      qed
    qed
  qed
  with SN show "P s" using `s \<in> A` unfolding SN_on_def by blast
qed

(* link SN_on to acc / accp *)
lemma accp_imp_SN_on:
  assumes "\<And>x. x \<in> A \<Longrightarrow> accp g x"
  shows "SN_on {(y, z). g z y} A"
proof - {
  fix x assume "x \<in> A"
  from assms[OF this]
  have "SN_on {(y, z). g z y} {x}"
  proof (induct rule: accp.induct)
    case (accI x)
    show ?case
    proof
      fix f
      assume x: "f 0 \<in> {x}" and steps: "\<forall> i. (f i, f (Suc i)) \<in> {a. (\<lambda>(y,z). g z y) a}"
      hence "g (f 1) x" by auto
      from accI(2)[OF this] steps x show False unfolding SN_on_def by auto
    qed
  qed
  }
  thus ?thesis unfolding SN_on_def by blast
qed

lemma SN_on_imp_accp:
  assumes "SN_on {(y,z). g z y} A"
  shows "\<forall>x\<in>A. accp g x"
proof
  fix x assume "x \<in> A"
  with assms show "accp g x"
  proof (induct rule: SN_on_induct)
    case (IH x)
    show ?case
    proof
      fix y
      assume "g y x"
      with IH show "accp g y" by simp
    qed
  qed
qed

lemma SN_on_conv_accp:
  "SN_on {(y,z). g z y} {x} = accp g x"
  using SN_on_imp_accp[of g "{x}"]
        accp_imp_SN_on[of "{x}" g]
  by auto

lemma SN_on_conv_acc: "SN_on {(y,z). (z,y) \<in> r} {x} \<longleftrightarrow> x \<in> acc r"
  unfolding SN_on_conv_accp accp_acc_eq ..

lemma acc_imp_SN_on:
  assumes "x \<in> acc r" shows "SN_on {(y,z). (z,y) \<in> r} {x}"
  using assms unfolding SN_on_conv_acc by simp

lemma SN_on_imp_acc: assumes "SN_on {(y,z). (z,y) \<in> r} {x}" shows "x \<in> acc r"
  using assms unfolding SN_on_conv_acc by simp


subsection {* Newman's Lemma *}

lemma rtrancl_len_E[elim]: assumes "(x, y) \<in> r^*" obtains n where "(x, y) \<in> r^^n"
  using rtrancl_imp_UN_relpow[OF assms] by best

lemma relpow_Suc_E2'[elim]:
  assumes "(x, z) \<in> A^^Suc n" obtains y where "(x, y) \<in> A" and "(y, z) \<in> A^*"
proof -
  assume assm: "\<And>y. (x,y) \<in> A \<Longrightarrow> (y,z) \<in> A^* \<Longrightarrow> thesis"
  from relpow_Suc_E2[OF assms] obtain y where "(x,y) \<in> A" and "(y,z) \<in> A^^n" by auto
  hence "(y,z) \<in> A^*" using (*FIXME*) relpow_imp_rtrancl by auto
  from assm[OF `(x,y) \<in> A` this] show thesis .
qed

lemmas SN_on_induct'[consumes 1, case_names IH] = SN_on_induct[OF _ singletonI]

lemma Newman_local:
  assumes "SN_on r X" and WCR: "WCR_on r {x. SN_on r {x}}"
  shows "CR_on r X"
proof - {
  fix x
  assume "x \<in> X"
  with assms have "SN_on r {x}" unfolding SN_on_def by auto
  with this  have "CR_on r {x}"
  proof (induct rule: SN_on_induct')
    case (IH x) show ?case
    proof
      fix y z assume "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
      from `(x,y) \<in> r^*` obtain m where "(x,y) \<in> r^^m" ..
      from `(x,z) \<in> r^*` obtain n where "(x,z) \<in> r^^n" ..
      show "(y,z) \<in> r\<^sup>\<down>"
      proof (cases n)
        case 0
        from `(x,z) \<in> r^^n` have eq: "x = z" by (simp add: 0)
        from `(x,y) \<in> r^*` show ?thesis unfolding eq ..
      next
        case (Suc n')
        from `(x,z) \<in> r^^n`[unfolded Suc] obtain t where "(x,t) \<in> r" and "(t,z) \<in> r^*" ..
        show ?thesis
        proof (cases m)
          case 0
          from `(x,y) \<in> r^^m` have eq: "x = y" by (simp add: 0)
          from `(x,z) \<in> r^*` show ?thesis unfolding eq ..
        next
          case (Suc m')
          from `(x,y) \<in> r^^m`[unfolded Suc] obtain s where "(x,s) \<in> r" and "(s,y) \<in> r^*" ..          
          from WCR IH(2) have "WCR_on r {x}" unfolding WCR_on_def by auto
          with `(x,s) \<in> r` and `(x,t) \<in> r` have "(s,t) \<in> r\<^sup>\<down>" by auto
          then obtain u where "(s,u) \<in> r^*" and "(t,u) \<in> r^*" ..
          from `(x,s) \<in> r` IH(2) have "SN_on r {s}" by (rule step_preserves_SN_on)
          from IH(1)[OF `(x,s) \<in> r` this] have "CR_on r {s}" .
          from this and `(s,u) \<in> r^*` and `(s,y) \<in> r^*` have "(u,y) \<in> r\<^sup>\<down>" by auto
          then obtain v where "(u,v) \<in> r^*" and "(y,v) \<in> r^*" ..
          from `(x,t) \<in> r` IH(2) have "SN_on r {t}" by (rule step_preserves_SN_on)
          from IH(1)[OF `(x,t) \<in> r` this] have "CR_on r {t}" .
          moreover from `(t,u) \<in> r^*` and `(u,v) \<in> r^*` have "(t,v) \<in> r^*" by auto
          ultimately have "(z,v) \<in> r\<^sup>\<down>" using `(t,z) \<in> r^*` by auto
          then obtain w where "(z,w) \<in> r^*" and "(v,w) \<in> r^*" ..
          from `(y,v) \<in> r^*` and `(v,w) \<in> r^*` have "(y,w) \<in> r^*" by auto
          with `(z,w) \<in> r^*` show ?thesis by auto
        qed
      qed
    qed
  qed
  }
  thus ?thesis unfolding CR_on_def by blast
qed

lemma Newman: "SN r \<Longrightarrow> WCR r \<Longrightarrow> CR r"
  using Newman_local[of r UNIV]
  unfolding WCR_on_def by auto
  
lemma Image_SN_on:
  assumes "SN_on r (r `` A)"
  shows "SN_on r A"
proof
  fix f
  assume "f 0 \<in> A" and chain: "chain r f"
  hence "f (Suc 0) \<in> r `` A" by auto
  with assms have "SN_on r {f (Suc 0)}" by (auto simp add: `f 0 \<in> A` SN_defs)
  moreover have "\<not> SN_on r {f (Suc 0)}"
  proof -
    have "f (Suc 0) \<in> {f (Suc 0)}" by simp
    moreover from chain have "chain r (f \<circ> Suc)" by auto
    ultimately show ?thesis by auto
  qed
  ultimately show False by simp
qed

lemma SN_on_Image_conv: "SN_on r (r `` A) = SN_on r A"
  using SN_on_Image and Image_SN_on by blast

lemma all_reducts_SN_on_imp_SN_on:
  assumes "(\<And>b. (a, b) \<in> r \<Longrightarrow> SN_on r {b})"
  shows "SN_on r {a}"
  using assms and Image_SN_on[of r "{a}"] by (auto simp: SN_defs)

lemma SN_on_all_reducts_SN_on_conv:
  "SN_on r {a} = (\<forall>b. (a, b) \<in> r \<longrightarrow> SN_on r {b})"
  using SN_on_Image_conv[of r "{a}"] by (auto simp: SN_defs)

lemma SN_imp_SN_trancl: "SN R \<Longrightarrow> SN (R^+)"
  unfolding SN_iff_wf by (rule wf_converse_trancl)

lemma SN_trancl_imp_SN: assumes "SN (R^+)" shows "SN R"
proof (rule ccontr)
  assume "\<not> SN R"
  then obtain s where "chain R s" unfolding SN_defs by auto
  hence "chain (R^+) s" by auto
  hence "\<not> SN(R^+)" unfolding SN_defs by auto
  with assms show False by simp
qed

lemma SN_trancl_SN_conv: "SN (R^+) = SN R"
  using SN_trancl_imp_SN[of R] SN_imp_SN_trancl[of R] by blast


(*FIXME: move to HOL/Relation.thy (in Isabelle)*)
lemma converse_inv_image[simp]: "(inv_image R f)^-1 = inv_image (R^-1) f"
  unfolding inv_image_def converse_unfold by auto

lemma SN_inv_image: "SN R \<Longrightarrow> SN (inv_image R f)" unfolding SN_iff_wf by simp

lemma SN_subset: "SN R \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> SN R'" unfolding SN_defs by blast
 
lemma SN_pow_imp_SN: assumes "SN (A^^Suc n)" shows "SN A"
proof (rule ccontr)
  assume "\<not> SN A"
  then obtain S where "chain A S" unfolding SN_defs by auto
  from chain_imp_relpow[OF this]
    have step: "\<And>i. (S i, S (i + (Suc n))) \<in> A^^Suc n" .
  let ?T = "\<lambda>i. S (i * (Suc n))"
  have "chain (A^^Suc n) ?T"
  proof
    fix i show "(?T i, ?T (Suc i)) \<in> A^^Suc n" unfolding mult_Suc
      using step[of "i * Suc n"] unfolding add_commute .
  qed
  hence "\<not> SN (A^^Suc n)" unfolding SN_defs by best
  with assms show False by simp
qed

(* TODO: move to Isabelle Library? *)
lemma pow_Suc_subset_trancl: "R^^(Suc n) \<subseteq> R^+"
  using trancl_power[of _ R] by blast

lemma SN_imp_SN_pow: assumes "SN R" shows "SN (R^^Suc n)"
  using SN_subset[where R="R^+",OF SN_imp_SN_trancl[OF assms] pow_Suc_subset_trancl] by simp
  
(*FIXME: needed in HOL/Wellfounded.thy*)
lemma SN_pow: "SN R \<longleftrightarrow> SN (R ^^ Suc n)"
  by (rule iffI,rule SN_imp_SN_pow,assumption,rule SN_pow_imp_SN,assumption)

lemma SN_on_trancl:
  assumes "SN_on r A" shows "SN_on (r^+) A"
using assms
proof (rule contrapos_pp)
  let ?r = "restrict_SN r r"
  assume "\<not> SN_on (r^+) A"
  then obtain f where "f 0 \<in> A" and chain: "chain (r^+) f" by auto
  have "SN ?r" by (rule SN_restrict_SN_idemp)
  hence "SN (?r^+)" by (rule SN_imp_SN_trancl)
  have "\<forall>i. (f 0, f i) \<in> r^*"
  proof
    fix i show "(f 0, f i) \<in> r^*"
    proof (induct i)
      case 0 show ?case ..
    next
      case (Suc i)
      from chain have "(f i, f (Suc i)) \<in> r^+" ..
      with Suc show ?case by auto
    qed
  qed
  with assms have "\<forall>i. SN_on r {f i}"
    using steps_preserve_SN_on[of "f 0" _ r]
    and `f 0 \<in> A`
    and SN_on_subset2[of "{f 0}" "A"] by auto
  with chain have "chain (?r^+) f"
    unfolding restrict_SN_trancl_simp
    unfolding restrict_SN_def by auto
  hence "\<not> SN_on (?r^+) {f 0}" by auto
  with `SN (?r^+)` have False by (simp add: SN_defs)
  thus "\<not> SN_on r A" by simp
qed

lemma SN_on_trancl_SN_on_conv: "SN_on (R^+) T = SN_on R T"
  using SN_on_trancl_imp_SN_on[of R] SN_on_trancl[of R] by blast


text {* Restrict an ARS to elements of a given set. *}
definition "restrict" :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" where
  "restrict r S \<equiv> {(x, y). x \<in> S \<and> y \<in> S \<and> (x, y) \<in> r}"

lemma SN_on_restrict:
  assumes "SN_on r A"
  shows "SN_on (restrict r S) A" (is "SN_on ?r A")
proof (rule ccontr)
  assume "\<not> SN_on ?r A"
  hence "\<exists>f. f 0 \<in> A \<and> chain ?r f" by auto
  hence "\<exists>f. f 0 \<in> A \<and> chain r f" unfolding restrict_def by auto
  with `SN_on r A` show False by auto
qed

lemma restrict_rtrancl: "(restrict r S)^* \<subseteq> r^*" (is "?r^* \<subseteq> r^*")
proof - {
  fix x y assume "(x,y) \<in> ?r^*" hence "(x,y) \<in> r^*" unfolding restrict_def by induct auto
} thus ?thesis by auto
qed

lemma rtrancl_Image_step:
  assumes "a \<in> r^* `` A"
    and "(a, b) \<in> r^*"
  shows "b \<in> r^* `` A"
proof -
  from assms(1) obtain c where "c \<in> A" and "(c, a) \<in> r^*" by auto
  with assms have "(c, b) \<in> r^*" by auto
  with `c \<in> A` show ?thesis by auto
qed

lemma WCR_SN_on_imp_CR_on: assumes "WCR r" and "SN_on r A" shows "CR_on r A"
proof -
  let ?S = "r^* `` A"
  let ?r = "restrict r ?S"
  have "\<forall>x. SN_on ?r {x}"
  proof
    fix y have "y \<notin> ?S \<or> y \<in> ?S" by simp
    thus "SN_on ?r {y}"
    proof
      assume "y \<notin> ?S" thus ?thesis unfolding restrict_def by auto
    next
      assume "y \<in> ?S"
      hence "y \<in> r^* `` A" by simp
      with SN_on_Image_rtrancl[OF `SN_on r A`]
        have "SN_on r {y}" using SN_on_subset2[of "{y}" "r^* `` A"] by blast
      thus ?thesis by (rule SN_on_restrict)
    qed
  qed
  hence "SN ?r" unfolding SN_defs by auto
  {
    fix x y assume "(x,y) \<in> r^*" and "x \<in> ?S" and "y \<in> ?S"
    then obtain n where "(x,y) \<in> r^^n" and "x \<in> ?S" and "y \<in> ?S"
      using rtrancl_imp_UN_relpow by best
    hence "(x,y) \<in> ?r^*"
    proof (induct n arbitrary: x y)
      case 0 thus ?case by simp
    next
      case (Suc n)
      from `(x,y) \<in> r^^Suc n` obtain x' where "(x,x') \<in> r" and "(x',y) \<in> r^^n"
        using relpow_Suc_D2 by best
      hence "(x,x') \<in> r^*" by simp
      with `x \<in> ?S` have "x' \<in> ?S" by (rule rtrancl_Image_step)
      with Suc and `(x',y) \<in> r^^n` have "(x',y) \<in> ?r^*" by simp
      from `(x,x') \<in> r` and `x \<in> ?S` and `x' \<in> ?S` have "(x,x') \<in> ?r"
        unfolding restrict_def by simp
      with `(x',y) \<in> ?r^*` show ?case by simp
    qed
  }
  hence a:"\<forall>x y. (x,y) \<in> r^* \<and> x \<in> ?S \<and> y \<in> ?S \<longrightarrow> (x,y) \<in> ?r^*" by simp
  {
    fix x' y z assume "(x',y) \<in> ?r" and "(x',z) \<in> ?r"
    hence "x' \<in> ?S" and "y \<in> ?S" and "z \<in> ?S" and "(x',y) \<in> r" and "(x',z) \<in> r"
      unfolding restrict_def by auto
    with `WCR r` have "(y,z) \<in> r\<^sup>\<down>" by auto
    then obtain u where "(y,u) \<in> r^*" and "(z,u) \<in> r^*" by auto
    from `x' \<in> ?S` obtain x where "x \<in> A" and "(x,x') \<in> r^*" by auto
    from `(x',y) \<in> r` have "(x',y) \<in> r^*" by auto
    with `(y,u) \<in> r^*` have "(x',u) \<in> r^*" by auto
    with `(x,x') \<in> r^*` have "(x,u) \<in> r^*" by simp
    hence "u \<in> ?S" using `x \<in> A` by auto
    from `y \<in> ?S` and `u \<in> ?S` and `(y,u) \<in> r^*` have "(y,u) \<in> ?r^*" using a by auto
    from `z \<in> ?S` and `u \<in> ?S` and `(z,u) \<in> r^*` have "(z,u) \<in> ?r^*" using a by auto
    with `(y,u) \<in> ?r^*` have "(y,z) \<in> ?r\<^sup>\<down>" by auto
  }
  hence "WCR ?r" by auto
  have "CR ?r" using Newman[OF `SN ?r` `WCR ?r`] by simp
  {
    fix x y z assume "x \<in> A" and "(x,y) \<in> r^*" and "(x,z) \<in> r^*"
    hence "y \<in> ?S" and "z \<in> ?S" by auto
    have "x \<in> ?S" using `x \<in> A` by auto
    from a and `(x,y) \<in> r^*` and `x \<in> ?S` and `y \<in> ?S` have "(x,y) \<in> ?r^*" by simp
    from a and `(x,z) \<in> r^*` and `x \<in> ?S` and `z \<in> ?S` have "(x,z) \<in> ?r^*" by simp
    with `CR ?r` and `(x,y) \<in> ?r^*` have "(y,z) \<in> ?r\<^sup>\<down>" by auto
    then obtain u where "(y,u) \<in> ?r^*" and "(z,u) \<in> ?r^*" by best
    hence "(y,u) \<in> r^*" and "(z,u) \<in> r^*" using restrict_rtrancl by auto
    hence "(y,z) \<in> r\<^sup>\<down>" by auto
  }
  thus ?thesis by auto
qed

lemma SN_on_Image_normalizable:
  assumes "SN_on r A"
  shows "\<forall>a\<in>A. \<exists>b. b \<in> r^! `` A"
proof
  fix a assume a: "a \<in> A"
  show "\<exists>b. b \<in> r^! `` A"
  proof (rule ccontr)
    assume "\<not> (\<exists>b. b \<in> r^! `` A)"
    hence A: "\<forall>b. (a, b) \<in> r^* \<longrightarrow> b \<notin> NF r" using a by auto
    hence "a \<notin> NF r" by auto
    let ?Q = "{c. (a, c) \<in> r^* \<and> c \<notin> NF r}"
    have "a \<in> ?Q" using `a \<notin> NF r` by simp
    have "\<forall>c\<in>?Q. \<exists>b. (c, b) \<in> r \<and> b \<in> ?Q"
    proof
      fix c
      assume "c \<in> ?Q"
      hence "(a, c) \<in> r^*" and "c \<notin> NF r" by auto
      then obtain d where "(c, d) \<in> r" by auto
      with `(a, c) \<in> r^*` have "(a, d) \<in> r^*" by simp
      with A have "d \<notin> NF r" by simp
      with `(c, d) \<in> r` and `(a, c) \<in> r^*`
        show "\<exists>b. (c, b) \<in> r \<and> b \<in> ?Q" by auto
    qed
    with `a \<in> ?Q` have "a \<in> ?Q \<and> (\<forall>c\<in>?Q. \<exists>b. (c, b) \<in> r \<and> b \<in> ?Q)" by auto
    hence "\<exists>Q. a \<in> Q \<and> (\<forall>c\<in>Q. \<exists>b. (c, b) \<in> r \<and> b \<in> Q)" by (rule exI[of _ "?Q"])
    hence "\<not> (\<forall>Q. a \<in> Q \<longrightarrow> (\<exists>c\<in>Q. \<forall>b. (c, b) \<in> r \<longrightarrow> b \<notin> Q))" by simp
    with SN_on_imp_on_minimal[of r a] have "\<not> SN_on r {a}" by blast
    with assms and `a \<in> A` and SN_on_subset2[of "{a}" A r] show False by simp
  qed
qed

lemma SN_on_imp_normalizability:
  assumes "SN_on r {a}" shows "\<exists>b. (a, b) \<in> r^!"
  using SN_on_Image_normalizable[OF assms] by auto


subsection {* Commutation *}

definition commute :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool"
where "commute r s \<equiv> ((r\<inverse>)^* O s^*) \<subseteq> (s^* O (r\<inverse>)^*)"

lemma CR_iff_self_commute: "CR r = commute r r"
  unfolding commute_def CR_iff_meet_subset_join meet_def join_def
  by simp

(* FIXME: move somewhere else *)
lemma rtrancl_imp_rtrancl_UN: 
  assumes "(x,y) \<in> r^*" and "r \<in> I"
  shows "(x,y) \<in> (\<Union>r\<in>I. r)^*" (is "(x,y) \<in> ?r^*")
using assms proof induct
  case base thus ?case by simp
next
  case (step y z)
  hence "(x,y) \<in> ?r^*" by simp
  from `(y,z) \<in> r` and `r \<in> I` have "(y,z) \<in> ?r^*" by auto
  with `(x,y) \<in> ?r^*` show ?case by auto
qed

definition
  quasi_commute :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool"
where
  "quasi_commute r s \<equiv> (s O r) \<subseteq> r O (r \<union> s)^*"

lemma rtrancl_union_subset_rtrancl_union_trancl: "(r \<union> s^+)^* = (r \<union> s)^*"
proof
  show "(r \<union> s^+)^* \<subseteq> (r \<union> s)^*"
  proof (rule subsetI2)
    fix x y assume "(x,y) \<in> (r \<union> s^+)^*"
    thus "(x,y) \<in> (r \<union> s)^*"
    proof (induct)
      case base thus ?case by auto
    next
      case (step y z)
      hence "(y,z) \<in> r \<or> (y,z) \<in> s^+" by auto
      hence "(y,z) \<in> (r \<union> s)^*"
      proof
        assume "(y,z) \<in> r" thus ?thesis by auto
      next
        assume "(y,z) \<in> s^+"
        hence "(y,z) \<in> s^*" by auto
        hence "(y,z) \<in> r^* \<union> s^*" by auto
        thus ?thesis using rtrancl_Un_subset by auto
      qed
      with `(x,y) \<in> (r \<union> s)^*` show ?case by simp
    qed
  qed
next
  show "(r \<union> s)^* \<subseteq> (r \<union> s^+)^*"
  proof (rule subsetI2)
    fix x y assume "(x,y) \<in> (r \<union> s)^*"
    thus "(x,y) \<in> (r \<union> s^+)^*"
    proof (induct)
      case base thus ?case by auto
    next
      case (step y z)
      hence "(y,z) \<in> (r \<union> s^+)^*" by auto
      with `(x,y) \<in> (r \<union> s^+)^*` show ?case by auto
    qed
  qed
qed

lemma qc_imp_qc_trancl: assumes "quasi_commute r s" shows "quasi_commute r (s^+)"
unfolding quasi_commute_def proof (rule subsetI2)
  fix x z assume "(x,z) \<in> s^+ O r"
  then obtain y where "(x,y) \<in> s^+" and "(y,z) \<in> r" by best
  thus "(x,z) \<in> r O (r \<union> s^+)^*"
  proof (induct arbitrary: z)
    case (base y)
    hence "(x,z) \<in> (s O r)" by auto
    with assms have "(x,z) \<in> r O (r \<union> s)^*" unfolding quasi_commute_def by auto
    thus ?case using rtrancl_union_subset_rtrancl_union_trancl by auto
  next
    case (step a b)
    hence "(a,z) \<in> (s O r)" by auto
    with assms have "(a,z) \<in> r O (r \<union> s)^*" unfolding quasi_commute_def by auto
    then obtain u where "(a,u) \<in> r" and "(u,z) \<in> (r \<union> s)^*" by best
    hence "(u,z) \<in> (r \<union> s^+)^*" using rtrancl_union_subset_rtrancl_union_trancl by auto
    from `(a,u) \<in> r` and step have "(x,u) \<in> r O (r \<union> s^+)^*" by auto
    then obtain v where "(x,v) \<in> r" and "(v,u) \<in> (r \<union> s^+)^*" by best
    with `(u,z) \<in> (r \<union> s^+)^*` have "(v,z) \<in> (r \<union> s^+)^*" by auto
    with `(x,v) \<in> r` show ?case by auto
  qed
qed

lemma steps_reflect_SN_on:
  assumes "\<not> SN_on r {b}" and "(a, b) \<in> r^*"
  shows "\<not> SN_on r {a}"
  using SN_on_Image_rtrancl[of r "{a}"]
  and assms and SN_on_subset2[of "{b}" "r^* `` {a}" r] by blast

lemma chain_imp_not_SN_on:
   assumes "chain r f"
   shows "\<not> SN_on r {f i}"
proof -
  let ?f = "\<lambda>j. f (i + j)"
  have "?f 0 \<in> {f i}" by simp
  moreover have "chain r ?f" using assms by auto
  ultimately have "?f 0 \<in> {f i} \<and> chain r ?f" by blast
  hence "\<exists>g. g 0 \<in> {f i} \<and> chain r g" by (rule exI[of _ "?f"])
  thus ?thesis unfolding SN_defs by auto
qed

lemma quasi_commute_imp_SN:
  assumes "SN r" and "SN s" and "quasi_commute r s"
  shows "SN (r \<union> s)"
proof -
  have "quasi_commute r (s^+)" by (rule qc_imp_qc_trancl[OF `quasi_commute r s`])
  let ?B = "{a. \<not> SN_on (r \<union> s) {a}}"
  {
    assume "\<not> SN(r \<union> s)"
    then obtain a where "a \<in> ?B" unfolding SN_defs by best
    from `SN r` have "\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> Q)"
      by (rule SN_imp_minimal)
    hence "\<forall>x. x \<in> ?B \<longrightarrow> (\<exists>z\<in>?B. \<forall>y. (z,y) \<in> r \<longrightarrow> y \<notin> ?B)" by (rule spec[where x = ?B])
    with `a \<in> ?B` obtain b where "b \<in> ?B" and min: "\<forall>y. (b,y) \<in> r \<longrightarrow> y \<notin> ?B" by auto
    from `b \<in> ?B` obtain S where "S 0 = b" and
      chain: "chain (r \<union> s) S" unfolding SN_on_def by auto
    let ?S = "\<lambda>i. S(Suc i)"
    have "?S 0 = S 1" by simp
    from chain have "chain (r \<union> s) ?S" by auto
    with `?S 0 = S 1` have "\<not> SN_on (r \<union> s) {S 1}" unfolding SN_on_def by auto
    from `S 0 = b` and chain have "(b,S 1) \<in> r \<union> s" by auto
    with min and `\<not> SN_on (r \<union> s) {S 1}` have "(b,S 1) \<in> s" by auto
    let ?i = "LEAST i. (S i,S(Suc i)) \<notin> s"
    {
      assume "chain s S"
      with `S 0 = b` have "\<not> SN_on s {b}" unfolding SN_on_def by auto
      with `SN s` have False unfolding SN_defs by auto
    }
    hence ex: "\<exists>i. (S i,S(Suc i)) \<notin> s" by auto
    hence "(S ?i,S(Suc ?i)) \<notin> s" by (rule LeastI_ex)
    with chain have "(S ?i,S(Suc ?i)) \<in> r" by auto
    have ini: "\<forall>i<?i. (S i,S(Suc i)) \<in> s" using not_less_Least by auto
    {
      fix i assume "i < ?i" hence "(b,S(Suc i)) \<in> s^+"
      proof (induct i)
        case 0 thus ?case using `(b,S 1) \<in> s` and `S 0 = b` by auto
      next
        case (Suc k)
      hence "(b,S(Suc k)) \<in> s^+" and "Suc k < ?i" by auto
      with `\<forall>i<?i. (S i,S(Suc i)) \<in> s` have "(S(Suc k),S(Suc(Suc k))) \<in> s" by fast
      with `(b,S(Suc k)) \<in> s^+` show ?case by auto
    qed
    }
    hence pref: "\<forall>i<?i. (b,S(Suc i)) \<in> s^+" by auto
    from `(b,S 1) \<in> s` and `S 0 = b` have "(S 0,S(Suc 0)) \<in> s" by auto
    {
      assume "?i = 0"
      from ex have "(S ?i,S(Suc ?i)) \<notin> s" by (rule LeastI_ex)
      with `(S 0,S(Suc 0)) \<in> s` have False unfolding `?i = 0` by simp
    }
    hence "0 < ?i" by auto
    then obtain j where "?i =  Suc j" unfolding gr0_conv_Suc by best
    with ini have "(S(?i-Suc 0),S(Suc(?i-Suc 0))) \<in> s" by auto
    with pref have "(b,S(Suc j)) \<in> s^+" unfolding `?i = Suc j` by auto
    hence "(b,S ?i) \<in> s^+" unfolding `?i = Suc j` by auto
    with `(S ?i,S(Suc ?i)) \<in> r` have "(b,S(Suc ?i)) \<in> (s^+ O r)" by auto
    with `quasi_commute r (s^+)` have "(b,S(Suc ?i)) \<in> r O (r \<union> s^+)^*"
      unfolding quasi_commute_def by auto
    then obtain c where "(b,c) \<in> r" and "(c,S(Suc ?i)) \<in> (r \<union> s^+)^*" by best
    from `(b,c) \<in> r` have "(b,c) \<in> (r \<union> s)^*" by auto
    from chain_imp_not_SN_on[of S "r \<union> s"]
      and chain have "\<not> SN_on (r \<union> s) {S (Suc ?i)}" by auto
    from `(c,S(Suc ?i)) \<in> (r \<union> s^+)^*` have "(c,S(Suc ?i)) \<in> (r \<union> s)^*"
      unfolding rtrancl_union_subset_rtrancl_union_trancl by auto
    with steps_reflect_SN_on[of "r \<union> s"]
      and `\<not> SN_on (r \<union> s) {S(Suc ?i)}` have "\<not> SN_on (r \<union> s) {c}" by auto
    hence "c \<in> ?B" by simp
    with `(b,c) \<in> r` and min have False by auto
  }
  thus ?thesis by auto
qed


subsection {* Strong Normalization *}

lemma non_strict_into_strict:
  assumes compat: "NS O S \<subseteq> S"
  and steps: "(s,t) \<in> (NS^*) O S"
  shows "(s,t) \<in> S"
using steps proof
  fix x u z
  assume "(s,t) = (x,z)" and "(x,u) \<in> NS^*" and "(u,z) \<in> S"
  hence "(s,u) \<in> NS^*" and "(u,t) \<in> S" by auto
  thus ?thesis
  proof (induct rule:rtrancl.induct)
    case (rtrancl_refl x) thus ?case .
  next
    case (rtrancl_into_rtrancl a b c)
    with compat show ?case by auto
  qed
qed

lemma comp_trancl: assumes "R O S \<subseteq> S" shows "R O S^+ \<subseteq> S^+"
proof (rule subsetI2)
  fix w z assume "(w,z) \<in> R O S^+"
  then obtain x where R_step: "(w,x) \<in> R" and S_seq: "(x,z) \<in> S^+" by best
  from tranclD[OF S_seq] obtain y where S_step: "(x,y) \<in> S" and S_seq': "(y,z) \<in> S^*" by auto
  from R_step and S_step have "(w,y) \<in> R O S" by auto
  with assms have "(w,y) \<in> S" by auto
  with S_seq' show "(w,z) \<in> S^+" by simp
qed

lemma comp_rtrancl_trancl:
  assumes comp: "R O S \<subseteq> S"
    and seq: "(s,t) \<in> (R \<union> S)^* O S"
  shows "(s,t) \<in> S^+"
using seq proof
  fix x u z
  assume "(s,t) = (x,z)" and "(x,u) \<in> (R \<union> S)^*" and "(u,z) \<in> S"
  hence "(s,u) \<in> (R \<union> S)^*" and "(u,t) \<in> S^+" by auto
  thus ?thesis
  proof (induct rule: rtrancl.induct)
    case (rtrancl_refl x) thus ?case .
  next
    case (rtrancl_into_rtrancl a b c)
    hence "(b,c) \<in> R \<union> S" by simp
    thus ?case
    proof
      assume "(b,c) \<in> S"
      with rtrancl_into_rtrancl
      have "(b,t) \<in> S^+" by simp
      with rtrancl_into_rtrancl show ?thesis by simp
    next
      assume "(b,c) \<in> R"
      with comp_trancl[OF comp] rtrancl_into_rtrancl
      show ?thesis by auto
    qed
  qed
qed

lemma trancl_union_right: "r^+ \<subseteq> (s \<union> r)^+"
proof (rule subsetI2)
  fix x y assume "(x,y) \<in> r^+" thus "(x,y) \<in> (s \<union> r)^+"
  proof (induct)
    case base thus ?case by auto
  next
    case (step a b)
    hence "(a,b) \<in> (s \<union> r)^+" by auto
    with `(x,a) \<in> (s \<union> r)^+` show ?case by auto
  qed
qed

lemma restrict_SN_subset: "restrict_SN R S \<subseteq> R"
proof (rule subsetI2)
  fix a b assume "(a,b) \<in> restrict_SN R S" thus "(a,b) \<in> R" unfolding restrict_SN_def by simp
qed

lemma chain_Un_SN_on_imp_first_step:
  assumes "chain (R \<union> S) t" and "SN_on S {t 0}"
  shows "\<exists>i. (t i, t (Suc i)) \<in> R \<and> (\<forall>j<i. (t j, t (Suc j)) \<in> S \<and> (t j, t (Suc j)) \<notin> R)"
proof -
  from `SN_on S {t 0}` obtain i where "(t i, t (Suc i)) \<notin> S" by blast
  with assms have "(t i, t (Suc i)) \<in> R" (is "?P i") by auto
  let ?i = "Least ?P"
  from `?P i` have "?P ?i" by (rule LeastI)
  have "\<forall>j<?i. (t j, t (Suc j)) \<notin> R" using not_less_Least by auto
  moreover with assms have "\<forall>j<?i. (t j, t (Suc j)) \<in> S" by best
  ultimately have "\<forall>j<?i. (t j, t (Suc j)) \<in> S \<and> (t j, t (Suc j)) \<notin> R" by best
  with `?P ?i` show ?thesis by best
qed

lemma first_step:
  assumes C: "C = A \<union> B" and steps: "(x, y) \<in> C^*" and Bstep: "(y, z) \<in> B"
  shows "\<exists>y. (x, y) \<in> A^* O B"
  using steps
proof (induct rule: converse_rtrancl_induct)
  case base
  show ?case using Bstep by auto
next 
  case (step u x)
  from step(1)[unfolded C] 
  show ?case
  proof
    assume "(u,x) \<in> B"
    thus ?thesis by auto
  next
    assume ux: "(u,x) \<in> A"
    from step(3) obtain y where "(x,y) \<in> A^* O B" by auto
    then obtain z where "(x,z) \<in> A^*" and step: "(z,y) \<in> B" by auto
    with ux have "(u,z) \<in> A^*" by auto
    with step have "(u,y) \<in> A^* O B" by auto
    thus ?thesis by auto
  qed
qed

lemma first_step_O: assumes C: "C = A \<union> B" and steps: "(x,y) \<in> C^* O B"
  shows "\<exists> y. (x,y) \<in> A^* O B"
proof -
  from steps obtain z where "(x,z) \<in> C^*" and "(z,y) \<in> B" by auto
  from first_step[OF C this] show ?thesis .
qed

lemma firstStep: assumes LSR: "L = S \<union> R" and xyL: "(x,y) \<in> L^*"
  shows "(x,y) \<in> R^* \<or> (x,y) \<in> R^* O S O L^*"
proof (cases "(x,y) \<in> R^*")
  case True
  thus ?thesis by simp
next
  case False 
  let ?SR = "S \<union> R"
  from xyL and LSR have "(x,y) \<in> ?SR^*" by simp
  from this and False have "(x,y) \<in> R^* O S O ?SR^*" 
  proof (induct rule: rtrancl_induct)
    case base thus ?case by simp
  next
    case (step y z)
    thus ?case
    proof (cases "(x,y) \<in> R^*")
      case False with step have "(x,y) \<in> R^* O S O ?SR^*" by simp
      from this obtain u where xu: "(x,u) \<in> R^* O S" and uy: "(u,y) \<in> ?SR^*" by force
      from `(y,z) \<in> ?SR` have "(y,z) \<in> ?SR^*" by auto
      with uy have "(u,z) \<in> ?SR^*" by (rule rtrancl_trans)
      with xu show ?thesis by auto
    next
      case True 
      have "(y,z) \<in> S" 
      proof (rule ccontr)
        assume "(y,z) \<notin> S" with `(y,z) \<in> ?SR` have "(y,z) \<in> R" by auto
        with True  have "(x,z) \<in> R^*"  by auto
        with `(x,z) \<notin> R^*` show False ..
      qed
      with True show ?thesis by auto
    qed
  qed
  with LSR show ?thesis by simp
qed


lemma non_strict_ending:
  assumes chain: "chain (R \<union> S) t"
    and comp: "R O S \<subseteq> S"
    and SN: "SN_on S {t 0}"
  shows "\<exists>j. \<forall>i\<ge>j. (t i, t (Suc i)) \<in> R - S"
proof (rule ccontr)
  assume "\<not> ?thesis"
  with chain have "\<forall>i. \<exists>j. j \<ge> i \<and> (t j, t (Suc j)) \<in> S" by blast
  from choice[OF this] obtain f where S_steps: "\<forall>i. i \<le> f i \<and> (t (f i), t (Suc (f i))) \<in> S" ..
  let ?t = "\<lambda>i. t (((Suc \<circ> f) ^^ i) 0)"
  have S_chain: "\<forall>i. (t i, t (Suc (f i))) \<in> S^+"
  proof
    fix i
    from S_steps have leq: "i\<le>f i" and step: "(t(f i),t(Suc(f i))) \<in> S" by auto
    from chain_imp_rtrancl[OF chain leq] have "(t i,t(f i)) \<in> (R \<union> S)^*" .
    with step have "(t i,t(Suc(f i))) \<in> (R \<union> S)^* O S" by auto
    from comp_rtrancl_trancl[OF comp this] show "(t i,t(Suc(f i))) \<in> S^+" .
  qed
  hence "chain (S^+) ?t"by simp
  moreover have "SN_on (S^+) {?t 0}" using SN_on_trancl[OF SN] by simp
  ultimately show False unfolding SN_defs by best
qed

lemma SN_on_subset1:
  assumes "SN_on r A" and "s \<subseteq> r"
  shows "SN_on s A"
  using assms unfolding SN_defs by blast

lemmas SN_on_mono = SN_on_subset1


lemma rtrancl_fun_conv:
  "((s,t) \<in> R^*) = (\<exists> f n. f 0 = s \<and> f n = t \<and> (\<forall> i < n. (f i, f (Suc i)) \<in> R))"
  unfolding rtrancl_is_UN_relpow using relpow_fun_conv[where R = R]
  by auto


lemma rtrancl_imp_relpow': "(x,y) \<in> R^* \<Longrightarrow> \<exists>n. (x,y) \<in> ((R::'a rel) ^^ n)"
  unfolding rtrancl_is_UN_relpow by auto

lemma compat_tr_compat: assumes "NS O S \<subseteq> S" shows "NS^* O S \<subseteq> S"
  using non_strict_into_strict[where S = S and NS = NS] assms by blast

lemma right_comp_S[simp]:
  assumes "(x, y) \<in> S O (S O S^* O NS^* \<union> NS^*)"
  shows "(x, y) \<in> (S O S^* O NS^*)"
proof-
  from assms have "(x, y) \<in> (S O S O S^* O NS^*) \<union> (S O NS^*)" by auto
  hence  xy:"(x, y) \<in> (S O (S O S^*) O NS^*) \<union> (S O NS^*)" by auto
  have "S O S^* \<subseteq> S^*" by auto
  with xy have "(x, y) \<in> (S O S^* O NS^*) \<union> (S O NS^*)" by auto
  then show "(x, y) \<in> (S O S^* O NS^*)" by auto
qed

lemma compatible_SN:
  assumes SN: "SN S"
  and compat: "NS O S \<subseteq> S" 
  shows "SN (S O S^* O NS^*)" (is "SN ?A")
proof
  fix F assume chain: "chain ?A F"
  from compat compat_tr_compat have tr_compat: "NS^* O S \<subseteq> S" by blast
  have "\<forall>i. (\<exists>y z. (F i, y) \<in> S \<and> (y, z)  \<in> S^* \<and> (z, F (Suc i)) \<in> NS^*)"
  proof
    fix i
    from chain have "(F i, F (Suc i)) \<in> (S O S^* O NS^*)" by auto
    thus "\<exists> y z. (F i, y)  \<in> S \<and> (y, z)  \<in> S^* \<and> (z, F (Suc i)) \<in> NS^*"
      unfolding relcomp_def (*FIXME:relcomp_unfold*) using mem_Collect_eq by auto
  qed
  hence "\<exists> f. (\<forall> i. (\<exists> z. (F i, f i)  \<in> S \<and> ((f i, z)  \<in> S^*) \<and>(z, F (Suc i)) \<in> NS^*))"
    by (rule choice)
  then obtain f
    where "\<forall> i. (\<exists> z. (F i, f i)  \<in> S \<and> ((f i, z)  \<in> S^*) \<and>(z, F (Suc i)) \<in> NS^*)" ..
  hence "\<exists> g. \<forall> i. (F i, f i)  \<in> S \<and> (f i, g i)  \<in> S^* \<and> (g i, F (Suc i)) \<in> NS^*"
    by (rule choice)
  then obtain g where "\<forall> i. (F i, f i)  \<in> S \<and> (f i, g i)  \<in> S^* \<and> (g i, F (Suc i)) \<in> NS^*" ..
  hence "\<forall> i. (f i, g i)  \<in> S^* \<and> (g i, F (Suc i)) \<in> NS^* \<and> (F (Suc i), f (Suc i))  \<in> S"
    by auto
  hence "\<forall> i. (f i, g i)  \<in> S^* \<and> (g i, f (Suc i))  \<in> S" unfolding relcomp_def (*FIXME*)
    using tr_compat by auto
  hence all:"\<forall> i. (f i, g i)  \<in> S^* \<and> (g i, f (Suc i))  \<in> S^+" by auto
  have "\<forall> i. (f i, f (Suc i))  \<in> S^+"
  proof
    fix i
    from all have "(f i, g i)  \<in> S^* \<and> (g i, f (Suc i))  \<in> S^+" ..
    thus "(f i, f (Suc i))  \<in> S^+" using transitive_closure_trans by auto
  qed
  hence "\<exists>x. f 0 = x \<and> chain (S^+) f"by auto
  then obtain x where "f 0 = x \<and> chain (S^+) f" by auto
  hence "\<exists>f. f 0 = x \<and> chain (S^+) f" by auto
  hence "\<not> SN_on (S^+) {x}" by auto
  hence "\<not> SN (S^+)" unfolding SN_defs by auto
  hence wfSconv:"\<not> wf ((S^+)\<inverse>)" using SN_iff_wf by auto
  from SN have "wf (S\<inverse>)" using SN_imp_wf[where?r=S] by simp
  with wf_converse_trancl wfSconv show False by auto
qed

lemma compatible_rtrancl_split:
  assumes compat: "NS O S \<subseteq> S"
   and steps: "(x, y) \<in> (NS \<union> S)^*"
  shows "(x, y) \<in> S O S^* O NS^* \<union> NS^*"
proof-
  from steps have "\<exists> n. (x, y) \<in> (NS \<union> S)^^n" using rtrancl_imp_relpow'[where ?R="NS \<union> S"] by auto
  then obtain n where "(x, y) \<in> (NS \<union> S)^^n" by auto
  thus "(x, y) \<in>  S O S^* O NS^* \<union> NS^*"
  proof (induct n arbitrary: x, simp)
    case (Suc m)
    assume "(x, y) \<in> (NS \<union> S)^^(Suc m)"
    hence "\<exists> z. (x, z) \<in> (NS \<union> S) \<and> (z, y) \<in> (NS \<union> S)^^m"
      using relpow_Suc_D2[where ?R="NS \<union> S"] by auto
    then obtain z where xz:"(x, z) \<in> (NS \<union> S)" and zy:"(z, y) \<in> (NS \<union> S)^^m" by auto
    with Suc have zy:"(z, y) \<in>  S O S^* O NS^* \<union> NS^*" by auto
    thus "(x, y) \<in>  S O S^* O NS^* \<union> NS^*"
    proof (cases "(x, z) \<in> NS")
      case True
      from compat compat_tr_compat have trCompat: "NS^* O S \<subseteq> S" by blast
      from zy True have "(x, y) \<in> (NS O S O S^* O NS^*) \<union> (NS O NS^*)" by auto
      hence "(x, y) \<in> ((NS O S) O S^* O NS^*) \<union> (NS O NS^*)" by auto
      hence "(x, y) \<in> ((NS^* O S) O S^* O NS^*) \<union> (NS O NS^*)" by auto
      with trCompat have xy:"(x, y) \<in> (S O S^* O NS^*) \<union> (NS O NS^*)" by auto
      have "NS O NS^* \<subseteq> NS^*" by auto
      with xy show "(x, y) \<in> (S O S^* O NS^*) \<union> NS^*" by auto
    next
      case False
      with xz have xz:"(x, z) \<in> S" by auto
      with zy have "(x, y) \<in> S O (S O S^* O NS^* \<union> NS^*)" by auto
      thus "(x, y) \<in> (S O S^* O NS^*) \<union> NS^*" using right_comp_S by simp
    qed
  qed
qed

lemma compatible_conv:
  assumes compat: "NS O S \<subseteq> S" 
  shows "(NS \<union> S)^* O S O (NS \<union> S)^* = S O S^* O NS^*" 
proof -
  let ?NSuS = "NS \<union> S"
  let ?NSS = "S O S^* O NS^*"
  let ?midS = "?NSuS^* O S O ?NSuS^*"
  have one: "?NSS \<subseteq> ?midS" by regexp 
  have "?NSuS^* O S \<subseteq> (?NSS \<union> NS^*) O S"
    using compatible_rtrancl_split[where S = S and NS = NS] compat by blast
  also have "\<dots> \<subseteq> ?NSS O S \<union> NS^* O S" by auto
  also have "\<dots> \<subseteq> ?NSS O S \<union> S" using compat compat_tr_compat[where S = S and NS = NS] by auto
  also have "\<dots> \<subseteq> S O ?NSuS^*" by regexp
  finally have "?midS \<subseteq> S O ?NSuS^* O ?NSuS^*" by blast
  also have "\<dots> \<subseteq> S O ?NSuS^*" by regexp
  also have "\<dots> \<subseteq> S O (?NSS \<union> NS^*)"
    using compatible_rtrancl_split[where S = S and NS = NS] compat by blast
  also have "\<dots> \<subseteq> ?NSS" by regexp
  finally have two: "?midS \<subseteq> ?NSS" . 
  from one two show ?thesis by auto 
qed

lemma compatible_SN': 
  assumes compat: "NS O S \<subseteq> S" and SN: "SN S"
  shows "SN((NS \<union> S)^* O S O (NS \<union> S)^*)"
using compatible_conv[where S = S and NS = NS] 
  compatible_SN[where S = S and NS = NS] assms by force

lemma rtrancl_diff_decomp:
 assumes "(x, y) \<in> A^* - B^*"
 shows "(x, y) \<in> A^* O (A - B) O A^*"
proof-
 from assms have A: "(x, y) \<in> A^*" and B:"(x, y) \<notin> B^*" by auto
 from A have "\<exists> k. (x, y) \<in> A^^k" by (rule rtrancl_imp_relpow')
 then obtain k where Ak:"(x, y) \<in> A^^k" by auto
 from Ak B show "(x, y) \<in> A^* O (A - B) O A^*"
 proof (induct k arbitrary: x)
 case 0
  with `(x, y) \<notin> B^*` 0 show ?case using ccontr by auto
 next
 case (Suc i)
  hence B:"(x, y) \<notin> B^*" and ASk:"(x, y) \<in> A ^^ Suc i" by auto
  from ASk have "\<exists>z. (x, z) \<in> A \<and> (z, y) \<in> A ^^ i" using relpow_Suc_D2[where ?R=A] by auto
  then obtain z where xz:"(x, z) \<in> A" and "(z, y) \<in> A ^^ i" by auto
  hence zy:"(z, y) \<in> A^*" using relpow_imp_rtrancl by auto
  from xz show "(x, y) \<in> A^* O (A - B) O A^*"
  proof (cases "(x, z) \<in> B")
   case False
    with xz zy show "(x, y) \<in> A\<^sup>* O (A - B) O A\<^sup>*" by auto
   next
   case True
    hence "(x, z) \<in> B^*" by auto
    have "\<lbrakk>(x, z) \<in> B^*; (z, y) \<in> B^*\<rbrakk> \<Longrightarrow> (x, y) \<in> B^*" using rtrancl_trans [of x z B] by auto
    with  `(x, z) \<in> B^*` `(x, y) \<notin> B^*` have "(z, y) \<notin> B^*" by auto
    with Suc `(z, y) \<in> A ^^ i` have "(z, y) \<in> A^* O (A - B) O A^*" by auto
    with xz have xy:"(x, y) \<in> A O A\<^sup>* O (A - B) O A\<^sup>*" by auto
    have "A O A\<^sup>* O (A - B) O A\<^sup>* \<subseteq> A\<^sup>* O (A - B) O A\<^sup>*" by regexp
    from this xy show "(x, y) \<in> A\<^sup>* O (A - B) O A\<^sup>*" using subsetD[where ?A="A O A\<^sup>* O (A - B) O A\<^sup>*"] by auto
  qed
 qed
qed

lemma SN_empty[simp]: "SN {}" by auto

lemma SN_on_weakening:
  assumes "SN_on R1 A"
  shows "SN_on (R1 \<inter> R2) A"
proof -
  {
    assume "\<exists>S. S 0 \<in> A \<and> chain (R1 \<inter> R2) S"
    then obtain S where
      S0: "S 0 \<in> A" and
      SN: "chain (R1 \<inter> R2) S"
      by auto
    from SN have SN': "chain R1 S" by simp
    with S0 and assms have "False" by auto
  }
  thus ?thesis by force
qed

lemma SN_weakening:
  assumes "SN R1"
  shows "SN (R1 \<inter> R2)"
  using SN_on_weakening and assms
  unfolding SN_on_def by best

(* an explicit version of infinite reduction *)
definition ideriv :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "ideriv R S as \<equiv> (\<forall>i. (as i, as (Suc i)) \<in> R \<union> S) \<and> (INFM i. (as i, as (Suc i)) \<in> R)"

lemma ideriv_mono: "R \<subseteq> R' \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> ideriv R S as \<Longrightarrow> ideriv R' S' as"
  unfolding ideriv_def INFM_nat by blast

fun
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"
where
  "shift f j = (\<lambda> i. f (i+j))"

lemma ideriv_split: assumes ideriv: "ideriv R S as"
  and nideriv: "\<not> ideriv (D \<inter> (R \<union> S)) (R \<union> S - D) as"
  shows "\<exists> i. ideriv (R - D) (S - D) (shift as i)"
proof -
  have RS: "R - D \<union> (S - D) = R \<union> S - D" by auto
  from ideriv[unfolded ideriv_def]
  have as: "\<And> i. (as i, as (Suc i)) \<in> R \<union> S"
    and inf: "INFM i. (as i, as (Suc i)) \<in> R" by auto
  show ?thesis
  proof (cases "INFM i. (as i, as (Suc i)) \<in> D \<inter> (R \<union> S)")
    case True
    have "ideriv (D \<inter> (R \<union> S)) (R \<union> S - D) as"
      unfolding ideriv_def
      using as True  by auto
    with nideriv show ?thesis ..
  next
    case False
    from False[unfolded INFM_nat]
    obtain i where Dn: "\<And> j. i < j \<Longrightarrow> (as j, as (Suc j)) \<notin> D \<inter> (R \<union> S)"
      by auto
    from Dn as have as: "\<And> j. i < j \<Longrightarrow> (as j, as (Suc j)) \<in> R \<union> S - D" by auto
    show ?thesis
    proof (rule exI[of _ "Suc i"], unfold ideriv_def RS, insert as, intro conjI, simp, unfold INFM_nat, intro allI)
      fix m
      from inf[unfolded INFM_nat] obtain j where j: "j > Suc i + m" and R: "(as j, as (Suc j)) \<in> R" by auto
      with as[of j] have RD: "(as j, as (Suc j)) \<in> R - D" by auto      
      show "\<exists> j > m. (shift as (Suc i) j, shift as (Suc i) (Suc j)) \<in> R - D"
        by (rule exI[of _ "j - Suc i"], insert j RD, auto)
    qed
  qed
qed

lemma ideriv_SN: assumes SN: "SN S"
  and compat: "NS O S \<subseteq> S"
  and R: "R \<subseteq> NS \<union> S"
  shows "\<not> ideriv (S \<inter> R) (R - S) as"
proof
  assume "ideriv (S \<inter> R) (R - S) as"
  with R have steps: "\<forall> i. (as i, as (Suc i)) \<in> NS \<union> S" and inf: "INFM i. (as i, as (Suc i)) \<in> S \<inter> R" unfolding ideriv_def by auto
  from non_strict_ending[OF steps compat] SN
  obtain i where i: "\<And> j. j \<ge> i \<Longrightarrow> (as j, as (Suc j)) \<in> NS - S" by best
  from inf[unfolded INFM_nat] obtain j where "j > i" and "(as j, as (Suc j)) \<in> S" by auto
  with i[of j] show False by auto
qed

lemma Infm_shift: "(INFM i. P (shift f n i)) = (INFM i. P (f i))" (is "?S = ?O")
proof 
  assume ?S
  show ?O
    unfolding INFM_nat_le 
  proof
    fix m
    from `?S`[unfolded INFM_nat_le]
    obtain k where k: "k \<ge> m" and p: "P (shift f n k)" by auto
    show "\<exists> k \<ge> m. P (f k)"
      by (rule exI[of _ "k + n"], insert k p, auto)
  qed
next
  assume ?O
  show ?S
    unfolding INFM_nat_le 
  proof
    fix m
    from `?O`[unfolded INFM_nat_le]
    obtain k where k: "k \<ge> m + n" and p: "P (f k)" by auto
    show "\<exists> k \<ge> m. P (shift f n k)"
      by (rule exI[of _ "k - n"], insert k p, auto)
  qed
qed

lemma rtrancl_list_conv:  "((s,t) \<in> R^*) = 
  (\<exists> list.  last (s # list) = t \<and> (\<forall> i. i < length list \<longrightarrow> ((s # list) ! i, (s # list) ! Suc i) \<in> R))" (is "?l = ?r")
proof 
  assume ?r
  then obtain list where "last (s # list) = t \<and> (\<forall> i. i < length list \<longrightarrow> ((s # list) ! i, (s # list) ! Suc i) \<in> R)" ..
  thus ?l
  proof (induct list arbitrary: s, simp)
    case (Cons u ll)
    hence "last (u # ll) = t \<and> (\<forall> i. i < length ll \<longrightarrow> ((u # ll) ! i, (u # ll) ! Suc i) \<in> R)" by auto
    from Cons(1)[OF this] have rec: "(u,t) \<in> R^*" .
    from Cons have "(s, u) \<in> R" by auto
    with rec show ?case by auto
  qed
next
  assume ?l
  from rtrancl_imp_seq[OF this]
  obtain S n where s: "S 0 = s" and t: "S n = t" and steps: "\<forall> i<n. (S i, S (Suc i)) \<in> R" by auto
  let ?list = "map (\<lambda> i. S (Suc i)) [0 ..< n]"
  show ?r
  proof (rule exI[of _ ?list], intro conjI, 
      cases n, simp add: s[symmetric] t[symmetric], simp add: t[symmetric]) 
    show "\<forall> i < length ?list. ((s # ?list) ! i, (s # ?list) ! Suc i) \<in> R" 
    proof (intro allI impI)
      fix i
      assume i: "i < length ?list"
      thus "((s # ?list) ! i, (s # ?list) ! Suc i) \<in> R"
      proof (cases i, simp add: s[symmetric] steps)
        case (Suc j)
        with i steps show ?thesis by simp
      qed
    qed
  qed
qed

lemma SN_reaches_NF:
  assumes "SN_on r {x}"
  shows "\<exists>y. (x, y) \<in> r^* \<and> y \<in> NF r"
using assms
proof (induct rule: SN_on_induct')
  case (IH x)
  show ?case
  proof (cases "x \<in> NF r")
    case True
    thus ?thesis by auto
  next
    case False
    then obtain y where step: "(x,y) \<in> r" by auto
    from IH[OF this] obtain z where steps: "(y,z) \<in> r^*" and NF: "z \<in> NF r" by auto
    show ?thesis
      by (intro exI, rule conjI[OF _ NF], insert step steps, auto)
  qed
qed

lemma SN_WCR_reaches_NF:
  assumes SN: "SN_on r {x}" 
    and WCR: "WCR_on r {x. SN_on r {x}}"
  shows "\<exists>! y. (x,y) \<in> r^* \<and> y \<in> NF r"
proof -
  from SN_reaches_NF[OF SN] obtain y where steps: "(x,y) \<in> r^*" and NF: "y \<in> NF r" by auto
  show ?thesis
  proof(rule, rule conjI[OF steps NF])
    fix z
    assume steps': "(x,z) \<in> r^* \<and> z \<in> NF r"
    from Newman_local[OF SN WCR] have "CR_on r {x}" by auto
    from CR_onD[OF this _ steps] steps' have "(y,z) \<in> r\<^sup>\<down>" by simp
    from join_NF_imp_eq[OF this NF] steps' show "z = y" by simp
  qed
qed

definition some_NF :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a" where
  "some_NF r x \<equiv> SOME y. (x, y) \<in> r^* \<and> y \<in> NF r"

lemma some_NF:
  assumes SN: "SN_on r {x}" 
  shows "(x,some_NF r x) \<in> r^* \<and> some_NF r x \<in> NF r"
  using someI_ex[OF SN_reaches_NF[OF SN]]
  unfolding some_NF_def .

lemma the_NF:
  assumes SN: "SN_on r {x}"
    and WCR: "WCR_on r {x. SN_on r {x}}"
    and steps: "(x,y) \<in> r^*"
    and NF: "y \<in> NF r"
  shows "y = some_NF r x"
proof -
  let ?p = "\<lambda> y. (x,y) \<in> r^* \<and> y \<in> NF r"
  from SN_WCR_reaches_NF[OF SN WCR]
  have one: "\<exists>! y. ?p y" .
  from steps NF have y: "?p y" ..
  from some_NF[OF SN] have some: "?p (some_NF r x)" .
  from one some y show ?thesis by auto
qed

lemma the_NF_UNF:
  assumes UNF: "UNF r"
    and steps: "(x,y) \<in> r^*"
    and NF: "y \<in> NF r"
  shows "y = some_NF r x"
proof -
  let ?p = "\<lambda> y. (x,y) \<in> r^* \<and> y \<in> NF r"
  from steps NF have py: "?p y" by simp
  hence pNF: "?p (some_NF r x)" unfolding some_NF_def 
    by (rule someI)
  from py have y: "(x,y) \<in> r^!" by auto
  from pNF have nf: "(x,some_NF r x) \<in> r^!" by auto
  from UNF[unfolded UNF_on_def] y nf show ?thesis by auto
qed

definition weak_diamond :: "'a rel \<Rightarrow> bool" ("w\<diamond>") where "w\<diamond> r \<equiv> (r\<inverse> O r) - Id \<subseteq> (r O r\<inverse>)"

lemma weak_diamond_imp_CR:
  assumes wd: "w\<diamond> r"
  shows "CR r"
proof (rule semi_confluence_imp_CR, rule)
  fix x y
  assume "(x,y) \<in> r^-1 O r^*"
  then obtain z where step: "(z,x) \<in> r" and steps: "(z,y) \<in> r^*" by auto
  from steps
  have "\<exists> u. (x,u) \<in> r^* \<and> (y,u) \<in> r^=" 
  proof (induct) 
    case base
    show ?case
      by (rule exI[of _ x], insert step, auto)
  next
    case (step y' y)
    from step(3) obtain u where xu: "(x,u) \<in> r^*" and y'u: "(y',u) \<in> r^=" by auto
    from y'u have "(y',u) \<in> r \<or> y' = u" by auto
    thus ?case
    proof
      assume y'u: "y' = u"
      with xu step(2) have xy: "(x,y) \<in> r^*" by auto
      show ?thesis 
        by (intro exI conjI, rule xy, simp)
    next
      assume "(y',u) \<in> r"
      with step(2) have uy: "(u,y) \<in> r^-1 O r" by auto
      show ?thesis
      proof (cases "u = y")
        case True
        show ?thesis
          by (intro exI conjI, rule xu, unfold True, simp)
      next
        case False
        with uy
          wd[unfolded weak_diamond_def] obtain u' where uu': "(u,u') \<in> r"
          and yu': "(y,u') \<in> r" by auto
        from xu uu' have xu: "(x,u') \<in> r^*" by auto
        show ?thesis
          by (intro exI conjI, rule xu, insert yu', auto)
      qed
    qed
  qed        
  thus "(x,y) \<in> r\<^sup>\<down>" by auto
qed

lemma steps_imp_not_SN_on:
  fixes t :: "'a \<Rightarrow> 'b"
    and R :: "'b rel"
  assumes steps: "\<And> x. (t x, t (f x)) \<in> R"
  shows "\<not> SN_on R {t x}"
proof  
  let ?U = "range t"
  assume "SN_on R {t x}"
  from SN_on_imp_on_minimal[OF this, rule_format, of ?U]
  obtain tz where tz: "tz \<in> range t" and min: "\<And> y. (tz,y) \<in> R \<Longrightarrow> y \<notin> range t" by auto
  from tz obtain z where tz: "tz = t z" by auto
  from steps[of z] min[of "t (f z)"] show False unfolding tz by auto
qed

lemma steps_imp_not_SN:
  fixes t :: "'a \<Rightarrow> 'b"
    and R :: "'b rel"
  assumes steps: "\<And> x. (t x, t (f x)) \<in> R"
  shows "\<not> SN R"
proof -
  from steps_imp_not_SN_on[of t f R, OF steps]
  show ?thesis unfolding SN_def by blast
qed

lemma steps_map:
  assumes fg: "\<And>t u R . P t \<Longrightarrow> Q R \<Longrightarrow> (t,u) \<in> R \<Longrightarrow> P u \<and> (f t, f u) \<in> g R"
  and t: "P t"
  and R: "Q R"
  and S: "Q S"
  shows "((t,u) \<in> R^* \<longrightarrow> (f t, f u) \<in> (g R)^*)
    \<and> ((t,u) \<in> R^* O S O R^* \<longrightarrow> (f t, f u) \<in> (g R)^* O (g S) O (g R)^*)"
proof -
  {
    fix t u
    assume "(t,u) \<in> R^*" and "P t"
    hence "P u \<and> (f t, f u) \<in> (g R)^*"
    proof (induct)
      case (step u v)
      from step(3)[OF step(4)] have Pu: "P u" and steps: "(f t, f u) \<in> (g R)^*" by auto
      from fg[OF Pu R step(2)] have Pv: "P v" and step: "(f u, f v) \<in> g R" by auto
      with steps have "(f t, f v) \<in> (g R)^*" by auto
      with Pv show ?case by simp
    qed simp
  } note main = this
  note maint = main[OF _ t]
  from maint[of u] have one: "(t, u) \<in> R^* \<longrightarrow> (f t, f u) \<in> (g R)^*" by simp
  show ?thesis
  proof (rule conjI[OF one impI])
    assume "(t,u) \<in> R^* O S O R^*"
    then obtain s v where ts: "(t,s) \<in> R^*" and sv: "(s,v) \<in> S" and vu: "(v,u) \<in> R^*" by auto
    from maint[OF ts] have Ps: "P s" and ts: "(f t, f s) \<in> (g R)^*" by auto
    from fg[OF Ps S sv] have Pv: "P v" and sv: "(f s, f v) \<in> g S" by auto
    from main[OF vu Pv] have vu: "(f v, f u) \<in> (g R)^*" by auto
    from ts sv vu show "(f t, f u) \<in> (g R)^* O g S O (g R)^*" by auto
  qed
qed


subsection {* Terminating part of a relation *}

inductive_set
  SN_part :: "'a rel \<Rightarrow> 'a set"
  for r :: "'a rel"
where
  SN_partI: "(\<And>y. (x, y) \<in> r \<Longrightarrow> y \<in> SN_part r) \<Longrightarrow> x \<in> SN_part r"

text {*The accessible part of a relation is the same as the terminating part
(just two names for the same definition -- modulo argument order). See
@{thm accI}.*}

text {*If all successors are terminating, then the current element is also terminating.*}
lemma step_reflects_SN_on:
  assumes "\<And>y. (x, y) \<in> r \<Longrightarrow> SN_on r {y}"
  shows "SN_on r {x}"
  by (rule ccontr) (insert assms, unfold SN_defs, force)

text {*Characterization of @{const SN_on} via terminating part.*}
lemma SN_on_SN_part_conv:
  "SN_on r A \<longleftrightarrow> A \<subseteq> SN_part r"
proof -
  {
    fix x assume "SN_on r A" and "x \<in> A"
    hence "x \<in> SN_part r" by (induct) (auto intro: SN_partI)
  } moreover {
    fix x assume "x \<in> A" and "A \<subseteq> SN_part r"
    hence "x \<in> SN_part r" by auto
    hence "SN_on r {x}" by (induct) (auto intro: step_reflects_SN_on)
  } ultimately show ?thesis by (force simp: SN_defs)
qed

text {*Special case for ``full'' termination.*}
lemma SN_SN_part_UNIV_conv:
  "SN r \<longleftrightarrow> SN_part r = UNIV"
  using SN_on_SN_part_conv[of r UNIV] by auto

end
