(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

text_raw \<open>\part{AutoCorres}\<close>

chapter \<open>Spec-Monad\<close>

theory Spec_Monad
  imports
  "Basic_Runs_To_VCG"
  "HOL-Library.Complete_Partial_Order2"
  "HOL-Library.Monad_Syntax"
  "AutoCorres_Utils"
begin

section \<open>\<open>rel_map\<close> and \<open>rel_project\<close>\<close>

definition rel_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "rel_map f r x = (x = f r)"

lemma rel_map_direct[simp]: "rel_map f a (f a)"
  by (simp add: rel_map_def)

abbreviation "rel_project \<equiv> rel_map"

lemmas rel_project_def = rel_map_def

lemma rel_project_id: "rel_project id = (=)" 
   "rel_project (\<lambda>v. v) = (=)"
  by (auto simp add: rel_project_def fun_eq_iff)

lemma rel_project_unit: "rel_project (\<lambda>_. ()) x y = True"
  by (simp add: rel_project_def)

lemma rel_projectI: "y = prj x \<Longrightarrow> rel_project prj x y"
  by (simp add: rel_project_def)

lemma rel_project_conv: "rel_project prj x y = (y = prj x)"
  by (simp add: rel_project_def)

section \<open>Misc Theorems\<close>

declare case_unit_Unity [simp] \<comment> \<open>without this rule simplifier seems loops in unexpected ways \<close>

lemma abs_const_unit: "(\<lambda>(v::unit). f) = (\<lambda>(). f)"
  by auto

lemma SUP_mono'': "(\<And>x. x\<in>A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> (\<Squnion>x\<in>A. f x) \<le> (\<Squnion>x\<in>A. g x :: _::complete_lattice)"
  by (rule SUP_mono) auto

lemma wf_nat_bound: "wf {(a, b). b < a \<and> b \<le> (n::nat)}"
  apply (rule wf_subset)
  apply (rule wf_measure[where f="\<lambda>a. Suc n - a"])
  apply auto
  done

lemma (in complete_lattice) admissible_le:
  "ccpo.admissible Inf (\<le>) (\<lambda>x. (y \<le> x))"
  by (simp add: ccpo.admissibleI local.Inf_greatest)

lemma mono_const: "mono (\<lambda>x. c)"
  by (simp add: mono_def)

lemma mono_lam: "(\<And>a. mono (\<lambda>x. F x a)) \<Longrightarrow> mono F"
  by (simp add: mono_def le_fun_def)

lemma mono_app: "mono (\<lambda>x. x a)"
  by (simp add: mono_def le_fun_def)

lemma all_cong_map:
  assumes f_f': "\<And>y. f (f' y) = y" and P_Q: "\<And>x. P x \<longleftrightarrow> Q (f x)"
  shows "(\<forall>x. P x) \<longleftrightarrow> (\<forall>y. Q y)"
  using assms by metis

lemma rel_set_refl: "(\<And>x. x \<in> A \<Longrightarrow> R x x) \<Longrightarrow> rel_set R A A"
  by (auto simp: rel_set_def)

lemma rel_set_converse_iff: "rel_set R X Y \<longleftrightarrow> rel_set R\<inverse>\<inverse> Y X"
  by (auto simp add: rel_set_def)

lemma rel_set_weaken:
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> P x y \<Longrightarrow> Q x y) \<Longrightarrow> rel_set P A B \<Longrightarrow> rel_set Q A B"
  by (force simp: rel_set_def)

lemma sim_set_refl: "(\<And>x. x \<in> X \<Longrightarrow> R x x) \<Longrightarrow> sim_set R X X"
  by (auto simp: sim_set_def)

section \<open>Galois Connections\<close>

lemma mono_of_Sup_cont:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes cont: "\<And>X. f (Sup X) = (SUP x\<in>X. f x)"
  assumes xy: "x \<le> y"
  shows "f x \<le> f y"
proof -
  have "f x \<le> sup (f x) (f y)" by (rule sup_ge1)
  also have "\<dots> = (SUP x\<in>{x, y}. f x)" by simp
  also have "\<dots> = f (Sup {x, y})" by (rule cont[symmetric])
  finally show ?thesis using xy by (simp add: sup_absorb2)
qed

lemma gc_of_Sup_cont:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes cont: "\<And>X. f (Sup X) = (SUP x\<in>X. f x)"
  shows "f x \<le> y \<longleftrightarrow> x \<le> Sup {x. f x \<le> y}"
proof safe
  assume "f x \<le> y" then show "x \<le> Sup {x. f x \<le> y}"
    by (intro Sup_upper) simp
next
  assume "x \<le> Sup {x. f x \<le> y}"
  then have "f x \<le> f (Sup {x. f x \<le> y})"
    by (rule mono_of_Sup_cont[OF cont])
  also have "\<dots> = (SUP x\<in>{x. f x \<le> y}. f x)" by (rule cont)
  also have "\<dots> \<le> y" by (rule Sup_least) auto
  finally show "f x \<le> y" .
qed

lemma mono_of_Inf_cont:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes cont: "\<And>X. f (Inf X) = (INF x\<in>X. f x)"
  assumes xy: "x \<le> y"
  shows "f x \<le> f y"
proof -
  have "f x = f (Inf {x, y})" using xy by (simp add: inf_absorb1)
  also have "\<dots> = (INF x\<in>{x, y}. f x)" by (rule cont)
  also have "\<dots> = inf (f x) (f y)" by simp
  also have "\<dots> \<le> f y" by (rule inf_le2)
  finally show ?thesis .
qed

lemma gc_of_Inf_cont:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes cont: "\<And>X. f (Inf X) = (INF x\<in>X. f x)"
  shows "Inf {y. x \<le> f y} \<le> y \<longleftrightarrow> x \<le> f y"
proof safe
  assume "x \<le> f y" then show "Inf {y. x \<le> f y} \<le> y"
    by (intro Inf_lower) simp
next
  assume *: "Inf {y. x \<le> f y} \<le> y"
  have "x \<le> (INF y\<in>{y. x \<le> f y}. f y)" by (rule Inf_greatest) auto
  also have "\<dots> = f (Inf {y. x \<le> f y})" by (rule cont[symmetric])
  also have "\<dots> \<le> f y"
    using * by (rule mono_of_Inf_cont[OF cont])
  finally show "x \<le> f y" .
qed

lemma gfp_fusion:
  assumes f_g: "\<And>x y. g x \<le> y \<longleftrightarrow> x \<le> f y"
  assumes a: "mono a"
  assumes b: "mono b"
  assumes *: "\<And>x. f (a x) = b (f x)"
  shows "f (gfp a) = gfp b"
  apply (intro antisym gfp_upperbound)
  subgoal
    apply (subst *[symmetric])
    apply (subst gfp_fixpoint[OF a])
    ..
  apply (rule f_g[THEN iffD1])
  apply (rule gfp_upperbound)
  apply (rule f_g[THEN iffD2])
  apply (subst *)
  apply (subst gfp_fixpoint[OF b, symmetric])
  apply (rule monoD[OF b])
  apply (rule f_g[THEN iffD1])
  apply (rule order_refl)
  done

lemma lfp_fusion:
  assumes f_g: "\<And>x y. g x \<le> y \<longleftrightarrow> x \<le> f y"
  assumes a: "mono a"
  assumes b: "mono b"
  assumes *: "\<And>x. g (a x) = b (g x)"
  shows "g (lfp a) = lfp b"
  apply (intro antisym lfp_lowerbound)
  subgoal
    apply (rule f_g[THEN iffD2])
    apply (rule lfp_lowerbound)
    apply (rule f_g[THEN iffD1])
    apply (subst *)
    apply (subst (2) lfp_fixpoint[OF b, symmetric])
    apply (rule monoD[OF b])
    apply (rule f_g[THEN iffD2])
    apply (rule order_refl)
    done
  subgoal
    apply (subst *[symmetric])
    apply (subst lfp_fixpoint[OF a])
    ..
  done

section \<open>\<open>post_state\<close> type\<close>

datatype 'r post_state = Failure | Success "'r set"

text \<open>
\<^const>\<open>Failure\<close> is supposed to model things like undefined behaviour in C. We usually have
to show the absence of \<^const>\<open>Failure\<close> for all possible executions of the program. Moreover,
it is used to model the 'result' of a non terminating computation.
\<close>

lemma split_post_state:
  "x = (case x of Success X \<Rightarrow> Success X | Failure \<Rightarrow> Failure)"
  for x::"'a post_state"
  by (cases x) auto

instantiation post_state :: (type) order
begin

inductive less_eq_post_state :: "'a post_state \<Rightarrow> 'a post_state \<Rightarrow> bool" where
  Failure_le[simp, intro]: "less_eq_post_state p Failure"
| Success_le_Success[intro]: "r \<subseteq> q \<Longrightarrow> less_eq_post_state (Success r) (Success q)"

definition less_post_state :: "'a post_state \<Rightarrow> 'a post_state \<Rightarrow> bool" where
  "less_post_state p q \<longleftrightarrow> p \<le> q \<and> \<not> q \<le> p"

instance
proof
  fix p q r :: "'a post_state"
  show "p \<le> p" by (cases p) auto
  show "p \<le> q \<Longrightarrow> q \<le> r \<Longrightarrow> p \<le> r" by (blast elim: less_eq_post_state.cases)
  show "p \<le> q \<Longrightarrow> q \<le> p \<Longrightarrow> p = q" by (blast elim: less_eq_post_state.cases)
qed (fact less_post_state_def)
end

lemma Success_le_Success_iff[simp]: "Success r \<le> Success q \<longleftrightarrow> r \<subseteq> q"
  by (auto elim: less_eq_post_state.cases)

lemma Failure_le_iff[simp]: "Failure \<le> q \<longleftrightarrow> q = Failure"
  by (auto elim: less_eq_post_state.cases)

instantiation post_state :: (type) complete_lattice
begin

definition top_post_state :: "'a post_state" where
  "top_post_state = Failure"

definition bot_post_state :: "'a post_state" where
  "bot_post_state = Success {}"

definition inf_post_state :: "'a post_state \<Rightarrow> 'a post_state \<Rightarrow> 'a post_state" where
  "inf_post_state =
    (\<lambda>Failure \<Rightarrow> id | Success res1 \<Rightarrow>
      (\<lambda>Failure \<Rightarrow> Success res1 | Success res2 \<Rightarrow> Success (res1 \<inter> res2)))"

definition sup_post_state :: "'a post_state \<Rightarrow> 'a post_state \<Rightarrow> 'a post_state" where
  "sup_post_state =
    (\<lambda>Failure \<Rightarrow> (\<lambda>_. Failure) | Success res1 \<Rightarrow>
      (\<lambda>Failure \<Rightarrow> Failure | Success res2 \<Rightarrow> Success (res1 \<union> res2)))"

definition Inf_post_state :: "'a post_state set \<Rightarrow> 'a post_state" where
  "Inf_post_state s = (if Success -` s = {} then Failure else Success (\<Inter> (Success -` s)))"

definition Sup_post_state :: "'a post_state set \<Rightarrow> 'a post_state" where
  "Sup_post_state s = (if Failure \<in> s then Failure else Success (\<Union> (Success -` s)))"

instance
proof
  fix x y z :: "'a post_state" and A :: "'a post_state set"
  show "inf x y \<le> y" by (simp add: inf_post_state_def split: post_state.split)
  show "inf x y \<le> x" by (simp add: inf_post_state_def split: post_state.split)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
    by (auto simp add: inf_post_state_def elim!: less_eq_post_state.cases)
  show "x \<le> sup x y" by (simp add: sup_post_state_def split: post_state.split)
  show "y \<le> sup x y" by (simp add: sup_post_state_def split: post_state.split)
  show "x \<le> y \<Longrightarrow> z \<le> y \<Longrightarrow> sup x z \<le> y"
    by (auto simp add: sup_post_state_def elim!: less_eq_post_state.cases)
  show "x \<in> A \<Longrightarrow> Inf A \<le> x" by (cases x) (auto simp add: Inf_post_state_def)
  show "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" by (cases z) (force simp add: Inf_post_state_def)+
  show "x \<in> A \<Longrightarrow> x \<le> Sup A" by (cases x) (auto simp add: Sup_post_state_def)
  show "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z" by (cases z) (force simp add: Sup_post_state_def)+
qed (simp_all add: top_post_state_def Inf_post_state_def bot_post_state_def Sup_post_state_def)
end

primrec holds_post_state :: "('a \<Rightarrow> bool) \<Rightarrow> 'a post_state \<Rightarrow> bool" where
  "holds_post_state P Failure \<longleftrightarrow> False"
| "holds_post_state P (Success X) \<longleftrightarrow> (\<forall>x\<in>X. P x)"

primrec holds_partial_post_state :: "('a \<Rightarrow> bool) \<Rightarrow> 'a post_state \<Rightarrow> bool" where
  "holds_partial_post_state P Failure \<longleftrightarrow> True"
| "holds_partial_post_state P (Success X) \<longleftrightarrow> (\<forall>x\<in>X. P x)"

inductive
  sim_post_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a post_state \<Rightarrow> 'b post_state \<Rightarrow> bool"
  for R
where
  [simp]: "\<And>p. sim_post_state R p Failure"
| "\<And>A B. sim_set R A B \<Longrightarrow> sim_post_state R (Success A) (Success B)"

inductive
  rel_post_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a post_state \<Rightarrow> 'b post_state \<Rightarrow> bool"
  for R
where
  [simp]: "rel_post_state R Failure Failure"
| "\<And>A B. rel_set R A B \<Longrightarrow> rel_post_state R (Success A) (Success B)"

primrec lift_post_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b post_state \<Rightarrow> 'a post_state" where
  "lift_post_state R Failure = Failure"
| "lift_post_state R (Success Y) = Success {x. \<exists>y\<in>Y. R x y}"

primrec unlift_post_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a post_state \<Rightarrow> 'b post_state" where
  "unlift_post_state R Failure = Failure"
| "unlift_post_state R (Success X) = Success {y. \<forall>x. R x y \<longrightarrow> x \<in> X}"

primrec map_post_state :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a post_state \<Rightarrow> 'b post_state" where
  "map_post_state f Failure  = Failure"
| "map_post_state f (Success r) = Success (f ` r)"

primrec vmap_post_state :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b post_state \<Rightarrow> 'a post_state" where
  "vmap_post_state f Failure  = Failure"
| "vmap_post_state f (Success r) = Success (f -` r)"

definition pure_post_state :: "'a \<Rightarrow> 'a post_state" where
  "pure_post_state v = Success {v}"

primrec bind_post_state :: "'a post_state \<Rightarrow> ('a \<Rightarrow> 'b post_state) \<Rightarrow> 'b post_state" where
  "bind_post_state Failure p = Failure"
| "bind_post_state (Success res) p = \<Squnion> (p ` res)"

subsection \<open>Order Properties\<close>

lemma top_ne_bot[simp]: "(\<bottom>:: _ post_state) \<noteq> \<top>"
  and bot_ne_top[simp]: "(\<top>:: _ post_state) \<noteq> \<bottom>"
  by (auto simp: top_post_state_def bot_post_state_def)

lemma Success_ne_top[simp]:
  "Success X \<noteq> \<top>" "\<top> \<noteq> Success X"
  by (auto simp: top_post_state_def)

lemma Success_eq_bot_iff[simp]:
  "Success X = \<bottom> \<longleftrightarrow> X = {}" "\<bottom> = Success X \<longleftrightarrow> X = {}"
  by (auto simp: bot_post_state_def)

lemma Sup_Success: "(\<Squnion>x\<in>X. Success (f x)) = Success (\<Union>x\<in>X. f x)"
  by (auto simp: Sup_post_state_def)

lemma Sup_Success_pair: "(\<Squnion>(x, y)\<in>X. Success (f x y)) = Success (\<Union>(x, y)\<in>X. f x y)"
  by (simp add: split_beta' Sup_Success)

subsection \<open>\<open>holds_post_state\<close>\<close>

lemma holds_post_state_iff:
  "holds_post_state P p \<longleftrightarrow> (\<exists>X. p = Success X \<and> (\<forall>x\<in>X. P x))"
  by (cases p) auto

lemma holds_post_state_weaken:
  "holds_post_state P p \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> holds_post_state Q p"
  by (cases p; auto)

lemma holds_post_state_combine:
  "holds_post_state P p \<Longrightarrow> holds_post_state Q p \<Longrightarrow>
    (\<And>x. P x \<Longrightarrow> Q x \<Longrightarrow> R x) \<Longrightarrow> holds_post_state R p"
  by (cases p; auto)

lemma holds_post_state_Ball:
  "Y \<noteq> {} \<or> p \<noteq> Failure \<Longrightarrow>
    holds_post_state (\<lambda>x. \<forall>y\<in>Y. P x y) p \<longleftrightarrow> (\<forall>y\<in>Y. holds_post_state (\<lambda>x. P x y) p)"
  by (cases p; auto)

lemma holds_post_state_All:
  "holds_post_state (\<lambda>x. \<forall>y. P x y) p \<longleftrightarrow> (\<forall>y. holds_post_state (\<lambda>x. P x y) p)"
  by (cases p; auto)

lemma holds_post_state_BexI:
  "y \<in> Y \<Longrightarrow> holds_post_state (\<lambda>x. P x y) p \<Longrightarrow> holds_post_state (\<lambda>x. \<exists>y\<in>Y. P x y) p"
  by (cases p; auto)

lemma holds_post_state_conj:
  "holds_post_state (\<lambda>x. P x \<and> Q x) p \<longleftrightarrow> holds_post_state P p \<and> holds_post_state Q p"
  by (cases p; auto)

lemma sim_post_state_iff:
  "sim_post_state R p q \<longleftrightarrow>
    (\<forall>P. holds_post_state (\<lambda>y. \<forall>x. R x y \<longrightarrow> P x) q \<longrightarrow> holds_post_state P p)"
  apply (cases p; cases q; simp add: sim_set_def sim_post_state.simps)
  apply safe
  apply force
  apply force
  subgoal premises prems for A B
    using prems(3)[THEN spec, of "\<lambda>a. \<exists>b\<in>B. R a b"] prems(4)
    by auto
  done

lemma post_state_le_iff:
  "p \<le> q \<longleftrightarrow> (\<forall>P. holds_post_state P q \<longrightarrow> holds_post_state P p)"
  by (cases p; cases q; force simp add: subset_eq Ball_def)

lemma post_state_eq_iff:
  "p = q \<longleftrightarrow> (\<forall>P. holds_post_state P p \<longleftrightarrow> holds_post_state P q)"
  by (simp add: order_eq_iff post_state_le_iff)

lemma holds_top_post_state[simp]: "\<not> holds_post_state P \<top>"
  by (simp add: top_post_state_def)

lemma holds_bot_post_state[simp]: "holds_post_state P \<bottom>"
  by (simp add: bot_post_state_def)



lemma holds_Sup_post_state[simp]: "holds_post_state P (Sup F) \<longleftrightarrow> (\<forall>f\<in>F. holds_post_state P f)"
  by (subst (2) split_post_state)
    (auto simp: Sup_post_state_def split: post_state.splits)

lemma holds_post_state_gfp:
  "holds_post_state P (gfp f) \<longleftrightarrow> (\<forall>p. p \<le> f p \<longrightarrow> holds_post_state P p)"
  by (simp add: gfp_def)

lemma holds_post_state_gfp_apply:
  "holds_post_state P (gfp f x) \<longleftrightarrow> (\<forall>p. p \<le> f p \<longrightarrow> holds_post_state P (p x))"
  by (simp add: gfp_def)

lemma holds_lift_post_state[simp]:
  "holds_post_state P (lift_post_state R x) \<longleftrightarrow> holds_post_state (\<lambda>y. \<forall>x. R x y \<longrightarrow> P x) x"
  by (cases x) auto

lemma holds_map_post_state[simp]:
  "holds_post_state P (map_post_state f x) \<longleftrightarrow> holds_post_state (\<lambda>x. P (f x)) x"
  by (cases x) auto

lemma holds_vmap_post_state[simp]:
  "holds_post_state P (vmap_post_state f x) \<longleftrightarrow> holds_post_state (\<lambda>x. \<forall>y. f y = x \<longrightarrow> P y) x"
  by (cases x) auto

lemma holds_pure_post_state[simp]: "holds_post_state P (pure_post_state x) \<longleftrightarrow> P x"
  by (simp add: pure_post_state_def)

lemma holds_bind_post_state[simp]:
  "holds_post_state P (bind_post_state f g) \<longleftrightarrow> holds_post_state (\<lambda>x. holds_post_state P (g x)) f"
  by (cases f) auto

lemma holds_post_state_False: "holds_post_state (\<lambda>x. False) f \<longleftrightarrow> f = \<bottom>"
  by (cases f) (auto simp: bot_post_state_def)

subsection \<open>\<open>holds_post_state_partial\<close>\<close>

lemma holds_partial_post_state_of_holds:
  "holds_post_state P p \<Longrightarrow> holds_partial_post_state P p"
  by (cases p; simp)

lemma holds_partial_post_state_iff:
  "holds_partial_post_state P p \<longleftrightarrow> (\<forall>X. p = Success X \<longrightarrow> (\<forall>x\<in>X. P x))"
  by (cases p) auto

lemma holds_partial_post_state_True[simp]: "holds_partial_post_state (\<lambda>x. True) p"
  by (cases p; simp)

lemma holds_partial_post_state_weaken:
  "holds_partial_post_state P p \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> holds_partial_post_state Q p"
  by (cases p; auto)

lemma holds_partial_post_state_Ball:
  "holds_partial_post_state (\<lambda>x. \<forall>y\<in>Y. P x y) p \<longleftrightarrow> (\<forall>y\<in>Y. holds_partial_post_state (\<lambda>x. P x y) p)"
  by (cases p; auto)

lemma holds_partial_post_state_All:
  "holds_partial_post_state (\<lambda>x. \<forall>y. P x y) p \<longleftrightarrow> (\<forall>y. holds_partial_post_state (\<lambda>x. P x y) p)"
  by (cases p; auto)

lemma holds_partial_post_state_conj:
  "holds_partial_post_state (\<lambda>x. P x \<and> Q x) p \<longleftrightarrow>
    holds_partial_post_state P p \<and> holds_partial_post_state Q p"
  by (cases p; auto)

lemma holds_partial_top_post_state[simp]: "holds_partial_post_state P \<top>"
  by (simp add: top_post_state_def)

lemma holds_partial_bot_post_state[simp]: "holds_partial_post_state P \<bottom>"
  by (simp add: bot_post_state_def)

lemma holds_partial_pure_post_state[simp]: "holds_partial_post_state P (pure_post_state x) \<longleftrightarrow> P x"
  by (simp add: pure_post_state_def)

lemma holds_partial_Sup_post_stateI:
  "(\<And>x. x \<in> X \<Longrightarrow> holds_partial_post_state P x) \<Longrightarrow> holds_partial_post_state P (Sup X)"
  by (force simp: Sup_post_state_def)

lemma holds_partial_bind_post_stateI:
  "holds_partial_post_state (\<lambda>x. holds_partial_post_state P (g x)) f \<Longrightarrow>
    holds_partial_post_state P (bind_post_state f g)"
  by (cases f) (auto intro: holds_partial_Sup_post_stateI)

lemma holds_partial_map_post_state[simp]:
  "holds_partial_post_state P (map_post_state f x) \<longleftrightarrow> holds_partial_post_state (\<lambda>x. P (f x)) x"
  by (cases x) auto

lemma holds_partial_vmap_post_state[simp]:
  "holds_partial_post_state P (vmap_post_state f x) \<longleftrightarrow>
    holds_partial_post_state (\<lambda>x. \<forall>y. f y = x \<longrightarrow> P y) x"
  by (cases x) auto

lemma holds_partial_bind_post_state:
  "holds_partial_post_state (\<lambda>x. holds_partial_post_state P (g x)) f \<Longrightarrow>
    holds_partial_post_state P (bind_post_state f g)"
  by (cases f) (auto intro: holds_partial_Sup_post_stateI)

subsection \<open>\<open>sim_post_state\<close>\<close>

lemma sim_post_state_eq_iff_le: "sim_post_state (=) p q \<longleftrightarrow> p \<le> q"
  by (simp add: post_state_le_iff sim_post_state_iff)

lemma sim_post_state_Success_Success_iff[simp]:
  "sim_post_state R (Success r) (Success q) \<longleftrightarrow> (\<forall>a\<in>r. \<exists>b\<in>q. R a b)"
  by (auto simp add: sim_set_def elim: sim_post_state.cases intro: sim_post_state.intros)

lemma sim_post_state_Success2:
  "sim_post_state R f (Success q) \<longleftrightarrow> holds_post_state (\<lambda>a. \<exists>b\<in>q. R a b) f"
  by (cases f; simp add: sim_post_state.simps sim_set_def)

lemma sim_post_state_Failure1[simp]: "sim_post_state R Failure q \<longleftrightarrow> q = Failure"
  by (auto elim: sim_post_state.cases intro: sim_post_state.intros)

lemma sim_post_state_top2[simp, intro]: "sim_post_state R p \<top>"
  by (simp add: top_post_state_def)

lemma sim_post_state_top1[simp]: "sim_post_state R \<top> q \<longleftrightarrow> q = \<top>"
  using sim_post_state_Failure1 by (metis top_post_state_def)

lemma sim_post_state_bot2[simp, intro]: "sim_post_state R p \<bottom> \<longleftrightarrow> p = \<bottom>"
  by (cases p; simp add: bot_post_state_def)

lemma sim_post_state_bot1[simp, intro]: "sim_post_state R \<bottom> q"
  by (cases q; simp add: bot_post_state_def)

lemma sim_post_state_le1: "sim_post_state R f' g \<Longrightarrow> f \<le> f' \<Longrightarrow> sim_post_state R f g"
  by (simp add: post_state_le_iff sim_post_state_iff)

lemma sim_post_state_le2: "sim_post_state R f g \<Longrightarrow> g \<le> g' \<Longrightarrow> sim_post_state R f g'"
  by (simp add: post_state_le_iff sim_post_state_iff)

lemma sim_post_state_Sup1:
  "sim_post_state R (Sup A) f \<longleftrightarrow> (\<forall>a\<in>A. sim_post_state R a f)"
  by (auto simp add: sim_post_state_iff)

lemma sim_post_state_Sup2:
  "a \<in> A \<Longrightarrow> sim_post_state R f a \<Longrightarrow> sim_post_state R f (Sup A)"
  by (auto simp add: sim_post_state_iff)

lemma sim_post_state_Sup:
  "\<forall>a\<in>A. \<exists>b\<in>B. sim_post_state R a b \<Longrightarrow> sim_post_state R (Sup A) (Sup B)"
  by (auto simp: sim_post_state_Sup1 intro: sim_post_state_Sup2)

lemma sim_post_state_weaken:
  "sim_post_state R f g \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> Q x y) \<Longrightarrow> sim_post_state Q f g"
  by (cases f; cases g; force)

lemma sim_post_state_trans:
  "sim_post_state R f g \<Longrightarrow> sim_post_state Q g h \<Longrightarrow> (\<And>x y z. R x y \<Longrightarrow> Q y z \<Longrightarrow> S x z) \<Longrightarrow>
    sim_post_state S f h"
  by (fastforce elim!: sim_post_state.cases intro: sim_post_state.intros simp: sim_set_def)

lemma sim_post_state_refl': "holds_partial_post_state (\<lambda>x. R x x) f \<Longrightarrow> sim_post_state R f f"
  by (cases f; auto simp: rel_set_def)

lemma sim_post_state_refl: "(\<And>x. R x x) \<Longrightarrow> sim_post_state R f f"
  by (simp add: sim_post_state_refl')

lemma sim_post_state_pure_post_state2:
  "sim_post_state F f (pure_post_state x) \<longleftrightarrow> holds_post_state (\<lambda>y. F y x) f"
  by (cases f; simp add: pure_post_state_def)

subsection \<open>\<open>rel_post_state\<close>\<close>

lemma rel_post_state_top[simp, intro!]: "rel_post_state R \<top> \<top>"
  by (auto simp: top_post_state_def)

lemma rel_post_state_top_iff[simp]:
  "rel_post_state R \<top> p \<longleftrightarrow> p = \<top>"
  "rel_post_state R p \<top> \<longleftrightarrow> p = \<top>"
  by (auto simp: top_post_state_def rel_post_state.simps)

lemma rel_post_state_Success_iff[simp]:
  "rel_post_state R (Success A) (Success B) \<longleftrightarrow> rel_set R A B"
  by (auto elim: rel_post_state.cases intro: rel_post_state.intros)

lemma rel_post_state_bot[simp, intro!]: "rel_post_state R \<bottom> \<bottom>"
  by (auto simp: bot_post_state_def Lifting_Set.empty_transfer)

lemma rel_post_state_eq_sim_post_state:
  "rel_post_state R p q \<longleftrightarrow> sim_post_state R p q \<and> sim_post_state R\<inverse>\<inverse> q p"
  by (auto simp: rel_set_def sim_set_def elim!: sim_post_state.cases rel_post_state.cases)

lemma rel_post_state_weaken:
  "rel_post_state R f g \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> Q x y) \<Longrightarrow> rel_post_state Q f g"
  by (auto intro: sim_post_state_weaken simp: rel_post_state_eq_sim_post_state)

lemma rel_post_state_eq[relator_eq]: "rel_post_state (=) = (=)"
  by (simp add: rel_post_state_eq_sim_post_state fun_eq_iff sim_post_state_eq_iff_le order_eq_iff)

lemma rel_post_state_mono[relator_mono]:
  "A \<le> B \<Longrightarrow> rel_post_state A \<le> rel_post_state B"
  using rel_set_mono[of A B]
  by (auto simp add: le_fun_def intro!: rel_post_state.intros elim!: rel_post_state.cases)

lemma rel_post_state_refl': "holds_partial_post_state (\<lambda>x. R x x) f \<Longrightarrow> rel_post_state R f f"
  by (cases f; auto simp: rel_set_def)

lemma rel_post_state_refl: "(\<And>x. R x x) \<Longrightarrow> rel_post_state R f f"
  by (simp add: rel_post_state_refl')

subsection \<open>\<open>lift_post_state\<close>\<close>

lemma lift_post_state_top: "lift_post_state R \<top> = \<top>"
  by (auto simp: top_post_state_def)

lemma lift_post_state_unlift_post_state: "lift_post_state R p \<le> q \<longleftrightarrow> p \<le> unlift_post_state R q"
  by (cases p; cases q; auto simp add: subset_eq)

lemma lift_post_state_eq_Sup: "lift_post_state R p = Sup {q. sim_post_state R q p}"
  unfolding post_state_eq_iff holds_Sup_post_state
  using holds_lift_post_state sim_post_state_iff
  by blast

lemma le_lift_post_state_iff: "q \<le> lift_post_state R p \<longleftrightarrow> sim_post_state R q p"
  by (simp add: post_state_le_iff sim_post_state_iff)

lemma lift_post_state_eq[simp]: "lift_post_state (=) p = p"
  by (simp add: post_state_eq_iff)

lemma lift_post_state_comp:
  "lift_post_state R (lift_post_state Q p) = lift_post_state (R OO Q) p"
  by (cases p) auto

lemma sim_post_state_lift:
  "sim_post_state Q q (lift_post_state R p) \<longleftrightarrow> sim_post_state (Q OO R) q p"
  unfolding le_lift_post_state_iff[symmetric] lift_post_state_comp ..

lemma lift_post_state_Sup: "lift_post_state R (Sup F) = (SUP f\<in>F. lift_post_state R f)"
  by (simp add: post_state_eq_iff)

lemma lift_post_state_mono: "p \<le> q \<Longrightarrow> lift_post_state R p \<le> lift_post_state R q"
  by (simp add: post_state_le_iff)

subsection \<open>\<open>map_post_state\<close>\<close>

lemma map_post_state_top: "map_post_state f \<top> = \<top>"
  by (auto simp: top_post_state_def)

lemma mono_map_post_state: "s1 \<le> s2 \<Longrightarrow> map_post_state f s1  \<le> map_post_state f s2"
  by (simp add: post_state_le_iff)

lemma map_post_state_eq_lift_post_state: "map_post_state f p = lift_post_state (\<lambda>a b. a = f b) p"
  by (cases p) auto

lemma map_post_state_Sup: "map_post_state f (Sup X) = (SUP x\<in>X. map_post_state f x)"
  by (simp add: post_state_eq_iff)

lemma map_post_state_comp: "map_post_state f (map_post_state g p) = map_post_state (f \<circ> g) p"
  by (simp add: post_state_eq_iff)

lemma map_post_state_id[simp]: "map_post_state id p = p"
  by (simp add: post_state_eq_iff)

lemma map_post_state_pure[simp]: "map_post_state f (pure_post_state x) = pure_post_state (f x)"
  by (simp add: pure_post_state_def)

lemma sim_post_state_map_post_state1:
  "sim_post_state R (map_post_state f p) q \<longleftrightarrow> sim_post_state (\<lambda>x y. R (f x) y) p q"
  by (cases p; cases q; simp)

lemma sim_post_state_map_post_state2:
  "sim_post_state R p (map_post_state f q) \<longleftrightarrow> sim_post_state (\<lambda>x y. R x (f y)) p q"
  unfolding map_post_state_eq_lift_post_state sim_post_state_lift by (simp add: OO_def[abs_def])

lemma map_post_state_eq_top[simp]: "map_post_state f p = \<top> \<longleftrightarrow> p = \<top>"
  by (cases p; simp add: top_post_state_def)

lemma map_post_state_eq_bot[simp]: "map_post_state f p = \<bottom> \<longleftrightarrow> p = \<bottom>"
  by (cases p; simp add: bot_post_state_def)

subsection \<open>\<open>vmap_post_state\<close>\<close>

lemma vmap_post_state_top: "vmap_post_state f \<top> = \<top>"
  by (auto simp: top_post_state_def)

lemma vmap_post_state_Sup:
  "vmap_post_state f (Sup X) = (SUP x\<in>X. vmap_post_state f x)"
  by (simp add: post_state_eq_iff)

lemma vmap_post_state_le_iff: "(vmap_post_state f p \<le> q) = (p \<le> \<Squnion> {p. vmap_post_state f p \<le> q})"
  using vmap_post_state_Sup by (rule gc_of_Sup_cont)

lemma vmap_post_state_eq_lift_post_state: "vmap_post_state f p = lift_post_state (\<lambda>a b. f a = b) p"
  by (cases p) auto

lemma vmap_post_state_comp: "vmap_post_state f (vmap_post_state g p) = vmap_post_state (g \<circ> f) p"
  apply (simp add: post_state_eq_iff)
  apply (intro allI arg_cong[where f="\<lambda>P. holds_post_state P p"])
  apply auto
  done

lemma vmap_post_state_id: "vmap_post_state id p = p"
  by (simp add: post_state_eq_iff)

lemma sim_post_state_vmap_post_state2:
  "sim_post_state R p (vmap_post_state f q) \<longleftrightarrow>
    sim_post_state (\<lambda>x y. \<exists>y'. f y' = y \<and> R x y') p q"
  by (cases p; cases q; auto) blast+

lemma vmap_post_state_le_iff_le_map_post_state:
  "map_post_state f p \<le> q \<longleftrightarrow> p \<le> vmap_post_state f q"
  by (simp flip: sim_post_state_eq_iff_le
           add: sim_post_state_map_post_state1 sim_post_state_vmap_post_state2)

subsection \<open>\<open>pure_post_state\<close>\<close>

lemma pure_post_state_Failure[simp]: "pure_post_state v \<noteq> Failure"
  by (simp add: pure_post_state_def)

lemma pure_post_state_top[simp]: "pure_post_state v \<noteq> \<top>"
  by (simp add: pure_post_state_def top_post_state_def)

lemma pure_post_state_bot[simp]: "pure_post_state v \<noteq> \<bottom>"
  by (simp add: pure_post_state_def bot_post_state_def)

lemma pure_post_state_inj[simp]: "pure_post_state v = pure_post_state w \<longleftrightarrow> v = w"
  by (simp add: pure_post_state_def)

lemma sim_pure_post_state_iff[simp]:
  "sim_post_state R (pure_post_state a) (pure_post_state b) \<longleftrightarrow> R a b"
  by (simp add: pure_post_state_def)

lemma rel_pure_post_state_iff[simp]:
  "rel_post_state R (pure_post_state a) (pure_post_state b) \<longleftrightarrow> R a b"
  by (simp add: rel_post_state_eq_sim_post_state)

lemma pure_post_state_le[simp]: "pure_post_state v \<le> pure_post_state w \<longleftrightarrow> v = w"
  by (simp add: pure_post_state_def)

lemma Success_eq_pure_post_state[simp]: "Success X = pure_post_state x \<longleftrightarrow> X = {x}"
  by (auto simp add: pure_post_state_def)

lemma pure_post_state_eq_Success[simp]: "pure_post_state x = Success X \<longleftrightarrow> X = {x}"
  by (auto simp add: pure_post_state_def)

lemma pure_post_state_le_Success[simp]: "pure_post_state x \<le> Success X \<longleftrightarrow> x \<in> X"
  by (auto simp add: pure_post_state_def)

lemma Success_le_pure_post_state[simp]: "Success X \<le> pure_post_state x \<longleftrightarrow> X \<subseteq> {x}"
  by (auto simp add: pure_post_state_def)

subsection \<open>\<open>bind_post_state\<close>\<close>

lemma bind_post_state_top: "bind_post_state \<top> g = \<top>"
  by (auto simp: top_post_state_def)

lemma bind_post_state_Sup1[simp]:
  "bind_post_state (Sup F) g = (SUP f\<in>F. bind_post_state f g)"
  by (simp add: post_state_eq_iff)

lemma bind_post_state_Sup2[simp]:
  "G \<noteq> {} \<or> f \<noteq> Failure \<Longrightarrow> bind_post_state f (Sup G) = (SUP g\<in>G. bind_post_state f g)"
  by (simp add: post_state_eq_iff holds_post_state_Ball)

lemma bind_post_state_sup1[simp]:
  "bind_post_state (sup f1 f2) g = sup (bind_post_state f1 g) (bind_post_state f2 g)"
  using bind_post_state_Sup1[of "{f1, f2}" g] by simp

lemma bind_post_state_sup2[simp]:
  "bind_post_state f (sup g1 g2) = sup (bind_post_state f g1) (bind_post_state f g2)"
  using bind_post_state_Sup2[of "{g1, g2}" f] by simp

lemma bind_post_state_top1[simp]: "bind_post_state \<top> f = \<top>"
  by (simp add: post_state_eq_iff)

lemma bind_post_state_bot1[simp]: "bind_post_state \<bottom> f = \<bottom>"
  by (simp add: post_state_eq_iff)

lemma bind_post_state_eq_top:
  "bind_post_state f g = \<top> \<longleftrightarrow> \<not> holds_post_state (\<lambda>x. g x \<noteq> \<top>) f"
  by (cases f) (force simp add: Sup_post_state_def simp flip: top_post_state_def)+

lemma bind_post_state_eq_bot:
  "bind_post_state f g = \<bottom> \<longleftrightarrow> holds_post_state (\<lambda>x. g x = \<bottom>) f"
  by (cases f) (auto simp flip: top_post_state_def)

lemma lift_post_state_bind_post_state:
  "lift_post_state R (bind_post_state x g) = bind_post_state x (\<lambda>v. lift_post_state R (g v))"
  by (simp add: post_state_eq_iff)

lemma vmap_post_state_bind_post_state:
  "vmap_post_state f (bind_post_state p g) = bind_post_state p (\<lambda>v. vmap_post_state f (g v))"
  by (simp add: post_state_eq_iff)

lemma map_post_state_bind_post_state:
  "map_post_state f (bind_post_state x g) = bind_post_state x (\<lambda>v. map_post_state f (g v))"
  by (simp add: post_state_eq_iff)

lemma bind_post_state_pure_post_state1[simp]:
  "bind_post_state (pure_post_state v) f = f v"
  by (simp add: post_state_eq_iff)

lemma bind_post_state_pure_post_state2:
  "bind_post_state p (\<lambda>x. pure_post_state (f x)) = map_post_state f p"
  by (simp add: post_state_eq_iff)

lemma bind_post_state_map_post_state:
  "bind_post_state (map_post_state f p) g = bind_post_state p (\<lambda>x. g (f x))"
  by (simp add: post_state_eq_iff)

lemma bind_post_state_assoc[simp]:
  "bind_post_state (bind_post_state f g) h =
    bind_post_state f (\<lambda>v. bind_post_state (g v) h)"
  by (simp add: post_state_eq_iff)

lemma sim_bind_post_state':
  "sim_post_state (\<lambda>x y. sim_post_state R (g x) (k y)) f h \<Longrightarrow>
    sim_post_state R (bind_post_state f g) (bind_post_state h k)"
  by (cases f; cases h; simp add: sim_post_state_Sup)

lemma sim_bind_post_state_left_iff:
  "sim_post_state R (bind_post_state f g) h \<longleftrightarrow>
    h = Failure \<or> holds_post_state (\<lambda>x. sim_post_state R (g x) h) f"
  by (cases f; cases h) (simp_all add: sim_post_state_Sup1)

lemma sim_bind_post_state_left:
  "holds_post_state (\<lambda>x. sim_post_state R (g x) h) f \<Longrightarrow>
    sim_post_state R (bind_post_state f g) h"
  by (simp add: sim_bind_post_state_left_iff)

lemma sim_bind_post_state_right:
  "g \<noteq> \<bottom> \<Longrightarrow> holds_partial_post_state (\<lambda>x. sim_post_state R f (h x)) g \<Longrightarrow>
    sim_post_state R f (bind_post_state g h) "
  by (cases g) (auto intro: sim_post_state_Sup2)

lemma sim_bind_post_state:
  "sim_post_state Q f h \<Longrightarrow> (\<And>x y. Q x y \<Longrightarrow> sim_post_state R (g x) (k y)) \<Longrightarrow>
    sim_post_state R (bind_post_state f g) (bind_post_state h k)"
  by (rule sim_bind_post_state'[OF sim_post_state_weaken, of Q])

lemma rel_bind_post_state':
  "rel_post_state (\<lambda>a b. rel_post_state R (g1 a) (g2 b)) f1 f2 \<Longrightarrow>
    rel_post_state R (bind_post_state f1 g1) (bind_post_state f2 g2)"
  by (auto simp: rel_post_state_eq_sim_post_state
           intro: sim_bind_post_state' sim_post_state_weaken)

lemma rel_bind_post_state:
  "rel_post_state Q f1 f2 \<Longrightarrow> (\<And>a b. Q a b \<Longrightarrow> rel_post_state R (g1 a) (g2 b)) \<Longrightarrow>
    rel_post_state R (bind_post_state f1 g1) (bind_post_state f2 g2)"
  by (rule rel_bind_post_state'[OF rel_post_state_weaken, of Q])

lemma mono_bind_post_state: "f1 \<le> f2 \<Longrightarrow> g1 \<le> g2 \<Longrightarrow> bind_post_state f1 g1 \<le> bind_post_state f2 g2"
  by (simp flip: sim_post_state_eq_iff_le add: le_fun_def sim_bind_post_state)


lemma Sup_eq_Failure[simp]: "Sup X = Failure \<longleftrightarrow> Failure \<in> X"
  by (simp add: Sup_post_state_def)

lemma Failure_inf_iff: "(Failure = x \<sqinter> y) \<longleftrightarrow> (x = Failure \<and> y = Failure)"
  by (metis Failure_le_iff le_inf_iff)

lemma Success_vimage_singleton_cancel: "Success -` {Success X} = {X}"
  by auto

lemma Success_vimage_image_cancel: "Success -` (\<lambda>x. Success (f x)) ` X = f ` X"
  by auto

lemma Success_image_comp: "(\<lambda>x. Success (g x)) ` X = Success ` (g ` X)"
  by auto

section \<open>\<open>exception_or_result\<close> type\<close>

instantiation option :: (type) default
begin

definition "default_option = None"

instance ..
end

lemma Some_ne_default[simp]:
  "Some x \<noteq> default" "default \<noteq> Some x"
  "default = None \<longleftrightarrow> True" "None = default \<longleftrightarrow> True"
  by (auto simp: default_option_def)

typedef (overloaded) ('a::default, 'b) exception_or_result =
  "Inl ` (UNIV - {default}) \<union> Inr ` UNIV :: ('a + 'b) set"
  by auto

setup_lifting type_definition_exception_or_result

context assumes "SORT_CONSTRAINT('e::default)"
begin

lift_definition Exception :: "'e \<Rightarrow> ('e, 'v) exception_or_result" is
  "\<lambda>e. if e = default then Inr undefined else Inl e"
  by auto

lift_definition Result :: "'v \<Rightarrow> ('e, 'v) exception_or_result" is
  "\<lambda>v. Inr v"
  by auto

end

lift_definition
  case_exception_or_result :: "('e::default \<Rightarrow> 'a) \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('e, 'v) exception_or_result \<Rightarrow> 'a"
  is case_sum .

declare [[case_translation case_exception_or_result Exception Result]]

lemma Result_eq_Result[simp]: "Result a = Result b \<longleftrightarrow> a = b"
  by transfer simp

lemma Exception_eq_Exception[simp]: "Exception a = Exception b \<longleftrightarrow> a = b"
  by transfer simp

lemma Result_eq_Exception[simp]: "Result a = Exception e \<longleftrightarrow> (e = default \<and> a = undefined)"
  by transfer simp

lemma Exception_eq_Result[simp]: "Exception e = Result a \<longleftrightarrow> (e = default \<and> a = undefined)"
  by (metis Result_eq_Exception)

lemma exception_or_result_cases[case_names Exception Result, cases type: exception_or_result]:
  "(\<And>e. e \<noteq> default \<Longrightarrow> x = Exception e \<Longrightarrow> P) \<Longrightarrow> (\<And>v. x = Result v \<Longrightarrow> P) \<Longrightarrow> P"
  by (transfer fixing: P) auto

lemma case_exception_or_result_Result[simp]:
  "(case Result v of Exception e \<Rightarrow> f e | Result w \<Rightarrow> g w) = g v"
  by transfer simp

lemma case_exception_or_result_Exception[simp]:
  "(case Exception e of Exception e \<Rightarrow> f e | Result w \<Rightarrow> g w) = (if e = default then g undefined else f e)"
  by transfer simp


text \<open>
Caution: for split rules don't use syntax
\<^term>\<open>(case r of Exception e \<Rightarrow> f e | Result w \<Rightarrow> g w)\<close>, as this introduces
non eta-contracted \<^term>\<open>\<lambda>e. f e\<close> and \<^term>\<open>\<lambda>w. g w\<close>, which don't work with the
splitter.
\<close>
lemma exception_or_result_split:
  "P (case_exception_or_result f g r)  \<longleftrightarrow>
    (\<forall>e. e \<noteq> default \<longrightarrow> r = Exception e \<longrightarrow> P (f e)) \<and>
    (\<forall>v. r = Result v \<longrightarrow> P (g v))"
  by (cases r) simp_all

lemma exception_or_result_split_asm:
  "P (case_exception_or_result f g r) \<longleftrightarrow>
  \<not> ((\<exists>e. r = Exception e \<and> e \<noteq> default \<and> \<not> P (f e)) \<or>
    (\<exists>v. r = Result v \<and> \<not> P (g v)))"
  by (cases r) simp_all

lemmas exception_or_result_splits = exception_or_result_split exception_or_result_split_asm

lemma split_exception_or_result: 
  "r = (case r of Exception e \<Rightarrow> Exception e | Result v \<Rightarrow> Result v)"
  by (cases r) auto

lemma exception_or_result_nchotomy:
  "\<not> ((\<forall>e. e \<noteq> default \<longrightarrow> x \<noteq> Exception e) \<and> (\<forall>v. x \<noteq> Result v))" by (cases x) auto

lemma val_split:
  fixes r::"(unit, 'a) exception_or_result"
  shows
  "P (case_exception_or_result f g r)  \<longleftrightarrow>
    (\<forall>v. r = Result v \<longrightarrow> P (g v))"
  by (cases r) simp_all

lemma val_split_asm:
  fixes r::"(unit, 'a) exception_or_result"
  shows "P (case_exception_or_result f g r) \<longleftrightarrow>
    \<not> (\<exists>v. r = Result v \<and> \<not> P (g v))"
  by (cases r) simp_all

lemmas val_splits[split] = val_split val_split_asm

instantiation exception_or_result :: ("{equal, default}", equal) equal begin

definition "equal_exception_or_result a b =
  (case a of
    Exception e \<Rightarrow> (case b of Exception e' \<Rightarrow> HOL.equal e e' | Result s \<Rightarrow> False)
  | Result r    \<Rightarrow> (case b of Exception e \<Rightarrow> False   | Result s \<Rightarrow> HOL.equal r s)
)"
instance proof qed (simp add: equal_exception_or_result_def equal_eq
    split: exception_or_result_splits)

end

definition is_Exception:: "('e::default, 'a) exception_or_result \<Rightarrow> bool" where
  "is_Exception x \<equiv> (case x of Exception e \<Rightarrow> e \<noteq> default | Result _ \<Rightarrow> False)"

definition is_Result:: "('e::default, 'a) exception_or_result \<Rightarrow> bool" where
  "is_Result x \<equiv> (case x of Exception e \<Rightarrow> e = default | Result _ \<Rightarrow> True)"

definition the_Exception::  "('e::default, 'a) exception_or_result \<Rightarrow> 'e" where
  "the_Exception x \<equiv> (case x of Exception e \<Rightarrow> e | Result _ \<Rightarrow> default)"

definition the_Result::  "('e::default, 'a) exception_or_result \<Rightarrow> 'a" where
  "the_Result x \<equiv> (case x of Exception e \<Rightarrow> undefined | Result v \<Rightarrow> v)"

lemma is_Exception_simps[simp]:
  "is_Exception (Exception e) = (e \<noteq> default)"
  "is_Exception (Result v) = False"
  by (auto simp add: is_Exception_def)

lemma is_Result_simps[simp]:
  "is_Result (Exception e) = (e = default)"
  "is_Result (Result v) = True"
  by (auto simp add: is_Result_def)

lemma the_Exception_simp[simp]:
  "the_Exception (Exception e) = e"
  by (auto simp add: the_Exception_def)

lemma the_Exception_Result:
  "the_Exception (Result v) = default"
  by (simp add: the_Exception_def)

definition undefined_unit::"unit \<Rightarrow> 'b" where "undefined_unit x \<equiv> undefined"

syntax "_Res" :: "pttrn \<Rightarrow> pttrn" (\<open>(\<open>open_block notation=\<open>prefix Res\<close>\<close>Res _)\<close>)
syntax_consts "_Res" \<rightleftharpoons> case_exception_or_result
translations "\<lambda>Res x. b" \<rightleftharpoons> "CONST case_exception_or_result (CONST undefined_unit) (\<lambda>x. b)"

term "\<lambda>Res x. f x"
term "\<lambda>Res (x, y, z). f x y z"
term "\<lambda>Res (x, y, z) s. P x y s z"


lifting_update exception_or_result.lifting
lifting_forget exception_or_result.lifting

inductive rel_exception_or_result:: "('e::default \<Rightarrow> 'f::default \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
  ('e, 'a) exception_or_result \<Rightarrow> ('f, 'b) exception_or_result \<Rightarrow> bool"
  where
Exception:
  "E e f \<Longrightarrow> e \<noteq> default \<Longrightarrow> f \<noteq> default \<Longrightarrow>
  rel_exception_or_result E R (Exception e) (Exception f)" |
Result:
  "R a b \<Longrightarrow> rel_exception_or_result E R (Result a) (Result b)"

lemma All_exception_or_result_cases:
  "(\<forall>x. P (x::(_, _) exception_or_result)) \<longleftrightarrow>
    (\<forall>err. err \<noteq> default \<longrightarrow> P (Exception err)) \<and>  (\<forall>v. P (Result v))"
  by (metis exception_or_result_cases)

lemma Ball_exception_or_result_cases:
  "(\<forall>x\<in>s. P (x::(_, _) exception_or_result)) \<longleftrightarrow>
    (\<forall>err. err \<noteq> default \<longrightarrow> Exception err \<in> s \<longrightarrow> P (Exception err)) \<and>
    (\<forall>v. Result v \<in> s \<longrightarrow> P (Result v))"
  by (metis exception_or_result_cases)

lemma Bex_exception_or_result_cases:
  "(\<exists>x\<in>s. P (x::(_, _) exception_or_result)) \<longleftrightarrow>
    (\<exists>err. err \<noteq> default \<and> Exception err \<in> s \<and> P (Exception err)) \<or>
    (\<exists>v. Result v \<in> s \<and> P (Result v))"
  by (metis exception_or_result_cases)

lemma Ex_exception_or_result_cases:
  "(\<exists>x. P (x::(_, _) exception_or_result)) \<longleftrightarrow>
    (\<exists>err. err \<noteq> default \<and> P (Exception err)) \<or>
    (\<exists>v. P (Result v))"
  by (metis exception_or_result_cases)

lemma case_distrib_exception_or_result:
  "f (case x of Exception e \<Rightarrow> E e | Result v \<Rightarrow> R v) = (case x of Exception e \<Rightarrow> f (E e) |  Result v \<Rightarrow> f (R v))"
  by (auto split: exception_or_result_split)

lemma rel_exception_or_result_Results[simp]:
  "rel_exception_or_result E R (Result a) (Result b) \<longleftrightarrow> R a b"
  by (simp add: rel_exception_or_result.simps)

lemma rel_exception_or_result_Exception[simp]:
  "e \<noteq> default \<Longrightarrow> f \<noteq> default \<Longrightarrow>
    rel_exception_or_result E R (Exception e) (Exception f) \<longleftrightarrow> E e f"
  by (simp add: rel_exception_or_result.simps)

lemma rel_exception_or_result_Result_Exception[simp]:
  "e \<noteq> default \<Longrightarrow> \<not> rel_exception_or_result E R (Exception e) (Result b)"
  "f \<noteq> default \<Longrightarrow> \<not> rel_exception_or_result E R (Result a) (Exception f)"
  by (auto simp add: rel_exception_or_result.simps)

lemma is_Exception_iff: "is_Exception x \<longleftrightarrow> (\<exists>e. e \<noteq> default \<and> x = Exception e)"
  apply (cases x)
   apply (auto)
  done

lemma rel_exception_or_result_converse:
  "(rel_exception_or_result E R)\<inverse>\<inverse> = rel_exception_or_result E\<inverse>\<inverse> R\<inverse>\<inverse>"
  apply (rule ext)+
  apply (auto simp add: rel_exception_or_result.simps)
  done

lemma rel_eception_or_result_Result[simp]:
  "rel_exception_or_result E R (Result x) (Result y) = R x y"
  by (auto simp add: rel_exception_or_result.simps)

lemma rel_exception_or_result_eq_conv: "rel_exception_or_result (=) (=) = (=)"
  apply (rule ext)+
  by (auto simp add: rel_exception_or_result.simps)
    (meson exception_or_result_cases)

lemma rel_exception_or_result_sum_eq: "rel_exception_or_result (=) (=) = (=)"
  apply (rule ext)+
  apply (subst (1) split_exception_or_result)
  apply (auto simp add: rel_exception_or_result.simps split:  exception_or_result_splits)
  done

definition
  map_exception_or_result::
    "('e::default \<Rightarrow> 'f::default) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('e, 'a) exception_or_result \<Rightarrow>
      ('f, 'b) exception_or_result"
where
  "map_exception_or_result E F x =
    (case x of Exception e \<Rightarrow> Exception (E e) | Result v \<Rightarrow> Result (F v))"

lemma map_exception_or_result_Exception[simp]:
  "e \<noteq> default \<Longrightarrow> map_exception_or_result E F (Exception e) = Exception (E e)"
  by (simp add: map_exception_or_result_def)

lemma map_exception_or_result_Result[simp]:
  "map_exception_or_result E F (Result v) = Result (F v)"
  by (simp add: map_exception_or_result_def)

lemma map_exception_or_result_id: "map_exception_or_result id id x = x"
  by (cases x; simp)

lemma map_exception_or_result_comp:
  assumes E2: "\<And>x. x \<noteq> default \<Longrightarrow> E2 x \<noteq> default"
  shows "map_exception_or_result E1 F1 (map_exception_or_result E2 F2 x) =
    map_exception_or_result (E1 \<circ> E2) (F1 \<circ> F2) x"
  by (cases x; auto dest: E2)

lemma le_bind_post_state_exception_or_result_cases[case_names Exception Result]:
  assumes
    "holds_partial_post_state (\<lambda>(x, t). \<forall>e. e \<noteq> default \<longrightarrow> x = Exception e \<longrightarrow> X e t \<le> X' e t) x"
  assumes "holds_partial_post_state (\<lambda>(x, t). \<forall>v. x = Result v \<longrightarrow> V v t \<le> V' v t) x"
  shows "bind_post_state x (\<lambda>(r, t). case r of Exception e \<Rightarrow> X e t | Result v \<Rightarrow> V v t) \<le>
    bind_post_state x (\<lambda>(r, t). case r of Exception e \<Rightarrow> X' e t| Result v \<Rightarrow> V' v t)"
  using assms
  by (cases x; force intro!: SUP_mono'' split: exception_or_result_splits prod.splits)

section \<open>\<open>spec_monad\<close> type\<close>

typedef (overloaded) ('e::default, 'a, 's) spec_monad =
  "UNIV :: ('s \<Rightarrow> (('e::default, 'a) exception_or_result \<times> 's) post_state) set"
  morphisms run Spec
  by (fact UNIV_witness)

lemma run_case_prod_distrib[simp]:
  "run (case x of (r, s) \<Rightarrow> f r s) t = (case x of (r, s) \<Rightarrow> run (f r s) t)"
  by (rule prod.case_distrib)

lemma image_case_prod_distrib[simp]:
  "(\<lambda>(r, t). f r t) ` (\<lambda>v. (g v, h v)) ` R = (\<lambda>v. (f (g v) (h v))) ` R "
  by auto

lemma run_Spec[simp]: "run (Spec p) s = p s"
  by (simp add: Spec_inverse)

setup_lifting type_definition_spec_monad

lemma spec_monad_ext: "(\<And>s. run f s = run g s) \<Longrightarrow> f = g"
  apply transfer
  apply auto
  done

lemma spec_monad_ext_iff: "f = g \<longleftrightarrow> (\<forall>s. run f s = run g s)"
  using spec_monad_ext by auto

instantiation spec_monad :: (default, type, type) complete_lattice
begin

lift_definition
  less_eq_spec_monad :: "('e::default, 'r, 's) spec_monad \<Rightarrow> ('e, 'r, 's) spec_monad \<Rightarrow> bool"
  is "(\<le>)" .

lift_definition
  less_spec_monad :: "('e::default, 'r, 's) spec_monad \<Rightarrow> ('e, 'r, 's) spec_monad \<Rightarrow> bool"
  is "(<)" .

lift_definition bot_spec_monad :: "('e::default, 'r, 's) spec_monad" is "bot" .

lift_definition top_spec_monad :: "('e::default, 'r, 's) spec_monad" is "top" .

lift_definition Inf_spec_monad :: "('e::default, 'r, 's) spec_monad set \<Rightarrow> ('e, 'r, 's) spec_monad"
  is "Inf" .

lift_definition Sup_spec_monad :: "('e::default, 'r, 's) spec_monad set \<Rightarrow> ('e, 'r, 's) spec_monad"
  is "Sup" .

lift_definition
  sup_spec_monad ::
    "('e::default, 'r, 's) spec_monad \<Rightarrow> ('e, 'r, 's) spec_monad \<Rightarrow> ('e, 'r, 's) spec_monad"
  is "sup" .

lift_definition
  inf_spec_monad ::
    "('e::default, 'r, 's) spec_monad \<Rightarrow> ('e, 'r, 's) spec_monad \<Rightarrow> ('e, 'r, 's) spec_monad"
  is "inf" .

instance
  apply (standard; transfer)
  subgoal by (rule less_le_not_le)
  subgoal by (rule order_refl)
  subgoal by (rule order_trans)
  subgoal by (rule antisym)
  subgoal by (rule inf_le1)
  subgoal by (rule inf_le2)
  subgoal by (rule inf_greatest)
  subgoal by (rule sup_ge1)
  subgoal by (rule sup_ge2)
  subgoal by (rule sup_least)
  subgoal by (rule Inf_lower)
  subgoal by (rule Inf_greatest)
  subgoal by (rule Sup_upper)
  subgoal by (rule Sup_least)
  subgoal by (rule Inf_empty)
  subgoal by (rule Sup_empty)
  done
end

lift_definition fail :: "('e::default, 'a, 's) spec_monad"
  is "\<lambda>s. Failure" .

lift_definition
  bind_exception_or_result :: 
    "('e::default, 'a, 's) spec_monad \<Rightarrow>
      (('e, 'a) exception_or_result \<Rightarrow> ('f::default, 'b, 's) spec_monad) \<Rightarrow> ('f, 'b, 's) spec_monad"
is
  "\<lambda>f h s. bind_post_state (f s) (\<lambda>(v, t). h v t)" .

lift_definition bind_handle ::
    "('e::default, 'a, 's) spec_monad \<Rightarrow>
      ('a \<Rightarrow> ('f, 'b, 's) spec_monad) \<Rightarrow> ('e \<Rightarrow> ('f, 'b, 's) spec_monad) \<Rightarrow>
      ('f::default, 'b, 's) spec_monad"
  is "\<lambda>f g h s. bind_post_state (f s) (\<lambda>(r, t). case r of Exception e \<Rightarrow> h e t | Result v \<Rightarrow> g v t)" .

lift_definition yield :: "('e, 'a) exception_or_result \<Rightarrow> ('e::default, 'a, 's) spec_monad"
  is "\<lambda>r s. pure_post_state (r, s)" .

abbreviation "return r \<equiv> yield (Result r)"

abbreviation "skip \<equiv> return ()"

abbreviation "throw_exception_or_result e \<equiv> yield (Exception e)"

lift_definition get_state :: "('e::default, 's, 's) spec_monad"
  is "\<lambda>s. pure_post_state (Result s, s)" .

lift_definition set_state :: "'s \<Rightarrow> ('e::default, unit, 's) spec_monad"
  is "\<lambda>t s. pure_post_state (Result (), t)" .

lift_definition map_value ::
    "(('e::default, 'a) exception_or_result \<Rightarrow> ('f::default, 'b) exception_or_result) \<Rightarrow>
      ('e, 'a, 's) spec_monad \<Rightarrow> ('f, 'b, 's) spec_monad"
  is "\<lambda>f g s. map_post_state (apfst f) (g s)" .

lift_definition vmap_value ::
    "(('e::default, 'a) exception_or_result \<Rightarrow> ('f::default, 'b) exception_or_result) \<Rightarrow>
      ('f, 'b, 's) spec_monad \<Rightarrow> ('e, 'a, 's) spec_monad"
  is "\<lambda>f g s. vmap_post_state (apfst f) (g s)" .

definition bind ::
    "('e::default, 'a, 's) spec_monad \<Rightarrow> ('a \<Rightarrow> ('e, 'b, 's) spec_monad) \<Rightarrow> ('e, 'b, 's) spec_monad"
where
  "bind f g = bind_handle f g throw_exception_or_result"

adhoc_overloading
  Monad_Syntax.bind bind

lift_definition lift_state ::
    "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('e::default, 'a, 't) spec_monad \<Rightarrow> ('e, 'a, 's) spec_monad"
  is "\<lambda>R p s. lift_post_state (rel_prod (=) R) (SUP t\<in>{t. R s t}. p t)" .

definition exec_concrete ::
  "('s \<Rightarrow> 't) \<Rightarrow> ('e::default, 'a, 's) spec_monad \<Rightarrow> ('e, 'a, 't) spec_monad"
where
  "exec_concrete st = lift_state (\<lambda>t s. t = st s)"

definition exec_abstract ::
  "('s \<Rightarrow> 't) \<Rightarrow> ('e::default, 'a, 't) spec_monad \<Rightarrow> ('e, 'a, 's) spec_monad"
where
  "exec_abstract st = lift_state (\<lambda>s t. t = st s)"

definition select_value :: "('e, 'a) exception_or_result set \<Rightarrow> ('e::default, 'a, 's) spec_monad" where
  "select_value R = (SUP r\<in>R. yield r)"

definition select :: "'a set \<Rightarrow> ('e::default, 'a, 's) spec_monad" where
  "select S = (SUP a\<in>S. return a)"

definition unknown :: "('e::default, 'a, 's) spec_monad" where
  "unknown \<equiv> select UNIV"

definition gets :: "('s \<Rightarrow> 'a) \<Rightarrow> ('e::default, 'a, 's) spec_monad" where
  "gets f = bind get_state (\<lambda>s. return (f s))"

definition assert_opt :: "'a option \<Rightarrow> ('e::default, 'a, 's) spec_monad" where
  "assert_opt v = (case v of None \<Rightarrow> fail | Some v \<Rightarrow> return v)"

definition gets_the :: "('s \<Rightarrow> 'a option) \<Rightarrow> ('e::default, 'a, 's) spec_monad" where
  "gets_the f = bind (gets f) assert_opt"

definition modify :: "('s \<Rightarrow> 's) \<Rightarrow> ('e::default, unit, 's) spec_monad" where
  "modify f = bind get_state (\<lambda>s. set_state (f s))"

definition "assume" :: "bool \<Rightarrow> ('e::default, unit, 's) spec_monad" where
  "assume P = (if P then return () else bot)"

definition assert :: "bool \<Rightarrow> ('e::default, unit, 's) spec_monad" where
  "assert P = (if P then return () else top)"

definition assuming :: "('s \<Rightarrow> bool) \<Rightarrow> ('e::default, unit, 's) spec_monad" where
  "assuming P = do {s  \<leftarrow> get_state; assume (P s)}"

definition guard:: "('s \<Rightarrow> bool) \<Rightarrow>  ('e::default, unit, 's) spec_monad" where
  "guard P = do {s \<leftarrow> get_state; assert (P s)}"

definition assume_result_and_state :: "('s \<Rightarrow> ('a \<times> 's) set) \<Rightarrow> ('e::default, 'a, 's) spec_monad" where
  "assume_result_and_state f = do {s \<leftarrow> get_state; (v, t) \<leftarrow> select (f s); set_state t; return v}"

(* TODO: delete *)
lift_definition assume_outcome ::
    "('s \<Rightarrow> (('e, 'a) exception_or_result \<times> 's) set) \<Rightarrow> ('e::default, 'a, 's) spec_monad"
  is "\<lambda>f s. Success (f s)" .

definition assert_result_and_state ::
    "('s \<Rightarrow> ('a \<times> 's) set) \<Rightarrow> ('e::default, 'a, 's) spec_monad"
where
  "assert_result_and_state f =
    do {s \<leftarrow> get_state; assert (f s \<noteq> {}); (v, t) \<leftarrow> select (f s); set_state t; return v}"

abbreviation state_select :: "('s \<times> 's) set \<Rightarrow> ('e::default, unit, 's) spec_monad" where
  "state_select r \<equiv> assert_result_and_state (\<lambda>s. {((), s'). (s, s') \<in> r})"

definition condition ::
    "('s \<Rightarrow> bool) \<Rightarrow> ('e::default, 'a, 's) spec_monad \<Rightarrow> ('e, 'a, 's) spec_monad \<Rightarrow>
      ('e, 'a, 's) spec_monad"
where
  "condition C T F =
    bind get_state (\<lambda>s. if C s then T else F)"

notation (output)
  condition  (\<open>(\<open>notation=\<open>prefix condition\<close>\<close>condition (_)//  (_)//  (_))\<close> [1000,1000,1000] 999)

definition "when" ::"bool \<Rightarrow> ('e::default, unit, 's) spec_monad \<Rightarrow> ('e, unit, 's) spec_monad"
  where "when c f \<equiv> condition (\<lambda>_. c) f skip"

abbreviation "unless" ::"bool \<Rightarrow> ('e::default, unit, 's) spec_monad \<Rightarrow> ('e, unit, 's) spec_monad"
  where "unless c \<equiv> when (\<not>c)"

definition on_exit' ::
    "('e::default, 'a, 's) spec_monad \<Rightarrow> ('e, unit, 's) spec_monad \<Rightarrow> ('e, 'a, 's) spec_monad"
where
  "on_exit' f c \<equiv>
     bind_exception_or_result f (\<lambda>r. do { c; yield r })"

definition on_exit ::
    "('e::default, 'a, 's) spec_monad \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('e, 'a, 's) spec_monad"
where
  "on_exit f cleanup \<equiv> on_exit' f (state_select cleanup)"

abbreviation guard_on_exit ::
    "('e::default, 'a, 's) spec_monad \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('e, 'a, 's) spec_monad"
where
  "guard_on_exit f grd cleanup \<equiv> on_exit' f (bind (guard grd) (\<lambda>_. state_select cleanup))"

abbreviation assume_on_exit ::
    "('e::default, 'a, 's) spec_monad \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<times> 's) set \<Rightarrow> ('e, 'a, 's) spec_monad"
where
  "assume_on_exit f grd cleanup \<equiv>
    on_exit' f (bind (assuming grd) (\<lambda>_. state_select cleanup))"

lift_definition run_bind ::
    "('e::default, 'a, 't) spec_monad \<Rightarrow> 't \<Rightarrow>
     (('e, 'a) exception_or_result \<Rightarrow> 't \<Rightarrow> ('f::default, 'b, 's) spec_monad) \<Rightarrow>
     ('f::default, 'b, 's) spec_monad"
  is "\<lambda>f t g s. bind_post_state (f t) (\<lambda>(r, t). g r t s)" .
    \<comment> \<open>\<^const>\<open>run_bind\<close> might be a more canonical building block compared to
   \<^const>\<open>lift_state\<close>. See subsection on \<^const>\<open>run_bind\<close> below.\<close>

type_synonym ('e, 'a, 's) predicate = "('e, 'a) exception_or_result \<Rightarrow> 's \<Rightarrow> bool"

lift_definition runs_to ::
    "('e::default, 'a, 's) spec_monad \<Rightarrow> 's \<Rightarrow> ('e, 'a, 's) predicate \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>mixfix runs_to\<close>\<close>_/ \<bullet> _ \<lbrace> _ \<rbrace>)\<close> [61, 1000, 0] 30) \<comment> \<open>syntax \<open>_do_block\<close> has 62\<close>
  is "\<lambda>f s Q. holds_post_state (\<lambda>(r, t). Q r t) (f s)" .

lift_definition runs_to_partial ::
    "('e::default, 'a, 's) spec_monad \<Rightarrow> 's \<Rightarrow> ('e, 'a, 's) predicate \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>mixfix runs_to_partial\<close>\<close>_/ \<bullet> _ ?\<lbrace> _ \<rbrace>)\<close> [61, 1000, 0] 30)
  is "\<lambda>f s Q. holds_partial_post_state (\<lambda>(r, t). Q r t) (f s)" .

lift_definition refines ::
  "('e::default, 'a, 's) spec_monad \<Rightarrow> ('f::default, 'b, 't) spec_monad \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow>
    ((('e, 'a) exception_or_result \<times> 's) \<Rightarrow> (('f, 'b) exception_or_result \<times> 't) \<Rightarrow> bool) \<Rightarrow> bool"
  is "\<lambda>f g s t R. sim_post_state R (f s) (g t)" .

lift_definition rel_spec ::
  "('e::default, 'a, 's) spec_monad \<Rightarrow> ('f::default, 'b, 't) spec_monad \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow>
     ((('e, 'a) exception_or_result \<times> 's) \<Rightarrow> (('f, 'b) exception_or_result \<times> 't) \<Rightarrow> bool)
   \<Rightarrow> bool"
is
  "\<lambda>f g s t R. rel_post_state R (f s) (g t)" .

definition rel_spec_monad ::
    "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> (('e, 'a) exception_or_result \<Rightarrow> ('f, 'b) exception_or_result \<Rightarrow> bool) \<Rightarrow>
      ('e::default, 'a, 's) spec_monad \<Rightarrow> ('f::default, 'b, 't) spec_monad \<Rightarrow> bool"
where
  "rel_spec_monad R Q f g =
    (\<forall>s t. R s t \<longrightarrow> rel_post_state (rel_prod Q R) (run f s) (run g t))"

lift_definition always_progress :: "('e::default, 'a, 's) spec_monad \<Rightarrow> bool" is
  "\<lambda>p. \<forall>s. p s \<noteq> bot" .

named_theorems run_spec_monad "Simplification rules to run a Spec monad"
named_theorems runs_to_iff "Equivalence theorems for runs to predicate"
named_theorems always_progress_intros "intro rules for always_progress predicate"

lemma runs_to_partialI: "(\<And>r x. P r x) \<Longrightarrow> f \<bullet> s ?\<lbrace> P \<rbrace>"
  by (cases "run f s") (auto simp: runs_to_partial.rep_eq)

lemma runs_to_partial_True: "f \<bullet> s ?\<lbrace> \<lambda>r s. True \<rbrace>"
  by (simp add: runs_to_partialI)

lemma runs_to_partial_conj: 
  "f \<bullet> s ?\<lbrace> P \<rbrace> \<Longrightarrow> f \<bullet> s ?\<lbrace> Q \<rbrace> \<Longrightarrow> f \<bullet> s ?\<lbrace> \<lambda>r s. P r s \<and> Q r s \<rbrace>"
  by (cases "run f s") (auto simp: runs_to_partial.rep_eq)

lemma refines_iff':
  "refines f g s t R \<longleftrightarrow> (\<forall>P. g \<bullet> t \<lbrace> \<lambda>r s. \<forall>p t. R (p, t) (r, s) \<longrightarrow> P p t \<rbrace> \<longrightarrow> f \<bullet> s \<lbrace> P \<rbrace>)"
  apply transfer
  apply (simp add: sim_post_state_iff le_fun_def split_beta' all_comm[where 'a='a])
  apply (rule all_cong_map[where f'="\<lambda>P (x, y). P x y" and f="\<lambda>P x y. P (x, y)"])
  apply auto
  done

lemma refines_weaken:
  "refines f g s t R \<Longrightarrow> (\<And>r s q t. R (r, s) (q, t) \<Longrightarrow> Q (r, s) (q, t)) \<Longrightarrow> refines f g s t Q"
  by transfer (auto intro: sim_post_state_weaken)

lemma refines_mono:
  "(\<And>r s q t. R (r, s) (q, t) \<Longrightarrow> Q (r, s) (q, t)) \<Longrightarrow> refines f g s t R \<Longrightarrow> refines f g s t Q"
  by (rule refines_weaken)

lemma refines_refl: "(\<And>r t. R (r, t) (r, t)) \<Longrightarrow> refines f f s s R"
  by transfer (auto intro: sim_post_state_refl)

lemma refines_trans:
  "refines f g s t R \<Longrightarrow> refines g h t u Q \<Longrightarrow>
    (\<And>r s p t q u. R (r, s) (p, t) \<Longrightarrow> Q (p, t) (q, u) \<Longrightarrow> S (r, s) (q, u)) \<Longrightarrow>
    refines f h s u S"
  by transfer (auto intro: sim_post_state_trans)

lemma refines_trans': "refines f g s t1 R \<Longrightarrow> refines g h t1 t2 Q \<Longrightarrow> refines f h s t2 (R OO Q)"
  by (rule refines_trans; assumption?) auto

lemma refines_strengthen:
  "refines f g s t R \<Longrightarrow> f \<bullet> s ?\<lbrace> F \<rbrace> \<Longrightarrow> g \<bullet> t ?\<lbrace> G \<rbrace> \<Longrightarrow>
    (\<And>x s y t. R (x, s) (y, t) \<Longrightarrow> F x s \<Longrightarrow> G y t \<Longrightarrow> Q (x, s) (y, t)) \<Longrightarrow>
  refines f g s t Q"
  by transfer (fastforce elim!: sim_post_state.cases simp: sim_set_def split_beta')

lemma refines_strengthen1:
  "refines f g s t R \<Longrightarrow> f \<bullet> s ?\<lbrace> F \<rbrace> \<Longrightarrow>
    (\<And>x s y t. R (x, s) (y, t) \<Longrightarrow> F x s \<Longrightarrow> Q (x, s) (y, t)) \<Longrightarrow>
  refines f g s t Q"
  by (rule refines_strengthen[OF _ _ runs_to_partial_True]; assumption?)

lemma refines_strengthen2:
  "refines f g s t R \<Longrightarrow> g \<bullet> t ?\<lbrace> G \<rbrace> \<Longrightarrow>
    (\<And>x s y t. R (x, s) (y, t) \<Longrightarrow> G y t \<Longrightarrow> Q (x, s) (y, t)) \<Longrightarrow>
  refines f g s t Q"
  by (rule refines_strengthen[OF _ runs_to_partial_True]; assumption?)

lemma refines_cong_cases:
  assumes "\<And>e s e' s'. e \<noteq> default \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    R (Exception e, s) (Exception e', s') \<longleftrightarrow> Q (Exception e, s) (Exception e', s')"
  assumes "\<And>e s x' s'. e \<noteq> default \<Longrightarrow>
    R (Exception e, s) (Result x', s') \<longleftrightarrow> Q (Exception e, s) (Result x', s')"
  assumes "\<And>x s e' s'. e' \<noteq> default \<Longrightarrow>
    R (Result x, s) (Exception e', s') \<longleftrightarrow> Q (Result x, s) (Exception e', s')"
  assumes "\<And>x s x' s'. R (Result x, s) (Result x', s') \<longleftrightarrow> Q (Result x, s) (Result x', s')"
  shows "refines f f' s s' R \<longleftrightarrow> refines f f' s s' Q"
  apply (clarsimp intro!: arg_cong[where f="refines f f' s s'"] simp: fun_eq_iff del: iffI)
  subgoal for v s v' s' by (cases v; cases v'; simp add: assms)
  done

lemma runs_to_partial_weaken[runs_to_vcg_weaken]:
  "f \<bullet> s ?\<lbrace>Q\<rbrace> \<Longrightarrow> (\<And>r t. Q r t \<Longrightarrow> Q' r t) \<Longrightarrow> f \<bullet> s ?\<lbrace>Q'\<rbrace>"
  by transfer (auto intro: holds_partial_post_state_weaken)

lemma runs_to_weaken[runs_to_vcg_weaken]: "f \<bullet> s \<lbrace>Q\<rbrace> \<Longrightarrow> (\<And>r t. Q r t \<Longrightarrow> Q' r t) \<Longrightarrow> f \<bullet> s \<lbrace>Q'\<rbrace>"
  by transfer (auto intro: holds_post_state_weaken)

lemma runs_to_partial_imp_runs_to_partial[mono]:
  "(\<And>a s. P a s \<longrightarrow> Q a s) \<Longrightarrow> f \<bullet> s ?\<lbrace> P \<rbrace> \<longrightarrow> f \<bullet> s ?\<lbrace> Q \<rbrace>"
  using runs_to_partial_weaken[of f s P Q] by auto

lemma runs_to_imp_runs_to[mono]:
  "(\<And>a s. P a s \<longrightarrow> Q a s) \<Longrightarrow> f \<bullet> s \<lbrace> P \<rbrace> \<longrightarrow> f \<bullet> s \<lbrace> Q \<rbrace>"
  using runs_to_weaken[of f s P Q] by auto

lemma refines_imp_refines[mono]:
  "(\<And>a s. P a s \<longrightarrow> Q a s) \<Longrightarrow> refines f g s t P \<longrightarrow> refines f g s t Q"
  using refines_weaken[of f g s t P Q] by auto

lemma runs_to_cong_cases:
  assumes "\<And>e s. e \<noteq> default \<Longrightarrow> P (Exception e) s \<longleftrightarrow> Q (Exception e) s"
  assumes "\<And>x s. P (Result x) s \<longleftrightarrow> Q (Result x) s"
  shows "f \<bullet> s \<lbrace> P \<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace> Q \<rbrace>"
  apply (clarsimp intro!: arg_cong[where f="runs_to _ _"] simp: fun_eq_iff del: iffI)
  subgoal for v s by (cases v; simp add: assms)
  done

lemma le_spec_monad_le_refines_iff: "f \<le> g \<longleftrightarrow> (\<forall>s. refines f g s s (=))"
  by transfer (simp add: le_fun_def sim_post_state_eq_iff_le)

lemma spec_monad_le_iff: "f \<le> g \<longleftrightarrow> (\<forall>P (s::'a). g \<bullet> s \<lbrace> P \<rbrace> \<longrightarrow> f \<bullet> s \<lbrace> P \<rbrace>)"
  by (simp add: le_spec_monad_le_refines_iff refines_iff' all_comm[where 'a='a])

lemma spec_monad_eq_iff: "f = g \<longleftrightarrow> (\<forall>P s. f \<bullet> s \<lbrace> P \<rbrace> \<longleftrightarrow> g \<bullet> s \<lbrace> P \<rbrace>)"
  by (simp add: order_eq_iff spec_monad_le_iff)

lemma spec_monad_eqI: "(\<And>P s. f \<bullet> s \<lbrace> P \<rbrace> \<longleftrightarrow> g \<bullet> s \<lbrace> P \<rbrace>) \<Longrightarrow> f = g"
  by (simp add: spec_monad_eq_iff)

lemma runs_to_Sup_iff: "(Sup X) \<bullet> s \<lbrace> P \<rbrace> \<longleftrightarrow> (\<forall>x\<in>X. x \<bullet> s \<lbrace> P \<rbrace>)"
  by transfer simp

lemma runs_to_lfp:
  assumes f: "mono f"
  assumes x_s: "P x s"
  assumes *: "\<And>p. (\<And>x s. P x s \<Longrightarrow> p x \<bullet> s \<lbrace> R \<rbrace>) \<Longrightarrow> (\<And>x s. P x s \<Longrightarrow> f p x \<bullet> s \<lbrace> R \<rbrace>)"
  shows "lfp f x \<bullet> s \<lbrace> R \<rbrace>"
proof -
  have "\<forall>x s. P x s \<longrightarrow> lfp f x \<bullet> s \<lbrace> R \<rbrace>"
    apply (rule lfp_ordinal_induct[OF f])
    subgoal using * by blast
    subgoal by (simp add: runs_to_Sup_iff)
    done
  with x_s show ?thesis by auto
qed

lemma runs_to_partial_alt:
  "f \<bullet> s ?\<lbrace> Q \<rbrace> \<longleftrightarrow> run f s = \<top> \<or> f \<bullet> s \<lbrace> Q \<rbrace>"
  by (cases "run f s"; simp add: runs_to.rep_eq runs_to_partial.rep_eq top_post_state_def)

lemma runs_to_of_runs_to_partial_runs_to':
  "f \<bullet> s \<lbrace> P \<rbrace> \<Longrightarrow> f \<bullet> s ?\<lbrace> Q \<rbrace> \<Longrightarrow> f \<bullet> s \<lbrace> Q \<rbrace>"
  by (auto simp: runs_to_partial_alt runs_to.rep_eq)

lemma runs_to_partial_of_runs_to:
  "f \<bullet> s \<lbrace> Q \<rbrace> \<Longrightarrow> f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (auto simp: runs_to_partial_alt)

lemma runs_to_partial_tivial[simp]: "f \<bullet> s ?\<lbrace> \<lambda>_ _. True \<rbrace>"
  by (cases "run f s"; simp add: runs_to_partial.rep_eq)

lemma le_spec_monad_le_run_iff: "f \<le> g \<longleftrightarrow> (\<forall>s. run f s \<le> run g s)"
  by (simp add: le_fun_def less_eq_spec_monad.rep_eq)

lemma refines_le_run_trans: "refines f g s s1 R \<Longrightarrow> run g s1 \<le> run h s2 \<Longrightarrow> refines f h s s2 R"
  by transfer (rule sim_post_state_le2)

lemma le_run_refines_trans: "run f s \<le> run g s1 \<Longrightarrow> refines g h s1 s2 R \<Longrightarrow> refines f h s s2 R"
  by transfer (rule sim_post_state_le1)

lemma refines_le_trans: "refines f g s t R \<Longrightarrow> g \<le> h \<Longrightarrow> refines f h s t R"
  by (auto simp: le_spec_monad_le_run_iff refines_le_run_trans)

lemma le_refines_trans: "f \<le> g \<Longrightarrow> refines g h s t R \<Longrightarrow> refines f h s t R"
  by (auto simp: le_spec_monad_le_run_iff intro: le_run_refines_trans)

lemma le_run_refines_iff: "run f s \<le> run g t \<longleftrightarrow> refines f g s t (=)"
  by transfer (simp add: sim_post_state_eq_iff_le)

lemma refines_top[simp]: "refines f \<top> s t R"
  unfolding top_spec_monad.rep_eq refines.rep_eq by simp

lemma refines_Sup1: "refines (Sup F) g s s' R \<longleftrightarrow> (\<forall>f\<in>F. refines f g s s' R)"
  by (simp add: refines.rep_eq Sup_spec_monad.rep_eq image_image sim_post_state_Sup1)

lemma monotone_le_iff_refines:
  "monotone R (\<le>) F \<longleftrightarrow> (\<forall>x y. R x y \<longrightarrow> (\<forall>s. refines (F x) (F y) s s (=)))"
  by (auto simp: monotone_def le_fun_def le_run_refines_iff[symmetric] le_spec_monad_le_run_iff)

lemma refines_iff_runs_to:
  "refines f g s t R \<longleftrightarrow> (\<forall>P. g \<bullet> t \<lbrace> \<lambda>r t'. \<forall>p s'. R (p, s') (r, t') \<longrightarrow> P p s' \<rbrace> \<longrightarrow> f \<bullet> s \<lbrace> P \<rbrace>)"
  by transfer (auto simp: sim_post_state_iff split_beta')

lemma runs_to_refines_weaken':
  "refines f g s t R \<Longrightarrow> g \<bullet> t \<lbrace> \<lambda>r t'. \<forall>p s'. R (p, s') (r, t') \<longrightarrow> P p s' \<rbrace> \<Longrightarrow> f \<bullet> s \<lbrace> P \<rbrace>"
  by (simp add: refines_iff_runs_to)

lemma runs_to_refines_weaken: "refines f f' s t (=) \<Longrightarrow> f' \<bullet> t \<lbrace> P \<rbrace> \<Longrightarrow> f \<bullet> s \<lbrace> P \<rbrace>"
  by (auto simp: runs_to_refines_weaken')

lemma refinesD_runs_to:
  assumes f_g: "refines f g s t R" and g: "g \<bullet> t \<lbrace> P \<rbrace>"
  shows "f \<bullet> s \<lbrace> \<lambda>r t. \<exists>r' t'. R (r, t) (r', t') \<and> P r' t' \<rbrace>"
  by (rule runs_to_refines_weaken'[OF f_g]) (auto intro: runs_to_weaken[OF g])

lemma rel_spec_iff_refines:
  "rel_spec f g s t R \<longleftrightarrow> refines f g s t R \<and> refines g f t s (R\<inverse>\<inverse>)"
  unfolding rel_spec_def by transfer (simp add: rel_post_state_eq_sim_post_state)

lemma rel_spec_symm: "rel_spec f g s t R \<longleftrightarrow> rel_spec g f t s R\<inverse>\<inverse>"
  by (simp add: rel_spec_iff_refines ac_simps)

lemma rel_specD_refines1: "rel_spec f g s t R \<Longrightarrow> refines f g s t R"
  by (simp add: rel_spec_iff_refines)

lemma rel_spec_mono: "P \<le> Q \<Longrightarrow> rel_spec f g s t P \<Longrightarrow> rel_spec f g s t Q"
  using rel_post_state_mono by (auto simp: rel_spec_def)

lemma rel_spec_eq: "rel_spec f g s t (=) \<longleftrightarrow> run f s = run g t"
  by (simp add: rel_spec_def rel_post_state_eq)

lemma rel_spec_eq_conv: "(\<forall>s. rel_spec f g s s (=)) \<longleftrightarrow> f = g"
  using rel_spec_eq spec_monad_ext by metis

lemma rel_spec_eqD: "(\<And>s. rel_spec f g s s (=)) \<Longrightarrow> f = g"
  using rel_spec_eq_conv by metis

lemma rel_spec_refl': "f \<bullet> s ?\<lbrace> \<lambda>r s. R (r, s) (r, s)\<rbrace> \<Longrightarrow> rel_spec f f s s R"
  by transfer  (simp add: rel_post_state_refl' split_beta')

lemma rel_spec_refl: "(\<And>r s. R (r, s) (r, s)) \<Longrightarrow> rel_spec f f s s R"
  by (rule rel_spec_mono[OF _ rel_spec_eq[THEN iffD2]]) auto

lemma refines_same_runs_to_partialI:
  "f \<bullet> s ?\<lbrace>\<lambda>r s'. R (r, s') (r, s')\<rbrace> \<Longrightarrow> refines f f s s R"
  by transfer
     (auto intro!: sim_post_state_refl' simp: split_beta')

lemma refines_same_runs_toI:
  "f \<bullet> s \<lbrace>\<lambda>r s'. R (r, s') (r, s')\<rbrace> \<Longrightarrow> refines f f s s R"
  by (rule refines_same_runs_to_partialI[OF runs_to_partial_of_runs_to])

lemma always_progress_case_prod[always_progress_intros]:
  "always_progress (f (fst p) (snd p)) \<Longrightarrow> always_progress (case_prod f p)"
  by (simp add: split_beta)

lemma refines_runs_to_partial_fuse:
  "refines f f' s s' Q \<Longrightarrow> f \<bullet> s ?\<lbrace>P\<rbrace> \<Longrightarrow>
    refines f f' s s' (\<lambda>(r,t) (r',t'). Q (r,t) (r',t') \<and> P r t)"
  by transfer (auto elim!: sim_post_state.cases simp: sim_set_def split_beta')

lemma runs_to_refines:
  "f' \<bullet> s' \<lbrace> P \<rbrace> \<Longrightarrow> refines f f' s s' Q \<Longrightarrow> (\<And>x s y t. P x s \<Longrightarrow> Q (y, t) (x, s) \<Longrightarrow> R y t) \<Longrightarrow>
    f \<bullet> s \<lbrace> R \<rbrace>"
  by transfer (force elim!: sim_post_state.cases simp: sim_set_def split_beta')

lemma runs_to_partial_subst_Res: "f \<bullet> s ?\<lbrace>\<lambda>r. P (the_Result r)\<rbrace> \<longleftrightarrow> f \<bullet> s ?\<lbrace>\<lambda>Res r. P r\<rbrace>"
  by (intro arg_cong[where f="\<lambda>P. f \<bullet> s ?\<lbrace> P \<rbrace>"]) (auto simp: fun_eq_iff the_Result_def)

lemma runs_to_subst_Res: "f \<bullet> s \<lbrace>\<lambda>r. P (the_Result r)\<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace>\<lambda>Res r. P r\<rbrace>"
  by (intro arg_cong[where f="\<lambda>P. f \<bullet> s \<lbrace> P \<rbrace>"]) (auto simp: fun_eq_iff the_Result_def)

lemma runs_to_Res[simp]: "f \<bullet> s \<lbrace>\<lambda>r t. \<forall>v. r = Result v \<longrightarrow> P v t\<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace>\<lambda>Res v t. P v t\<rbrace>"
  by (intro arg_cong[where f="\<lambda>P. f \<bullet> s \<lbrace> P \<rbrace>"]) (auto simp: fun_eq_iff the_Result_def)

lemma runs_to_partial_Res[simp]:
  "f \<bullet> s ?\<lbrace>\<lambda>r t. \<forall>v. r = Result v \<longrightarrow> P v t\<rbrace> \<longleftrightarrow> f \<bullet> s ?\<lbrace>\<lambda>Res v t. P v t\<rbrace>"
  by (intro arg_cong[where f="\<lambda>P. f \<bullet> s ?\<lbrace> P \<rbrace>"]) (auto simp: fun_eq_iff the_Result_def)

lemma rel_spec_runs_to:
  assumes f: "f \<bullet> s \<lbrace> P \<rbrace>" "always_progress f"
    and g: "g \<bullet> t \<lbrace> Q \<rbrace>" "always_progress g"
    and P: "(\<And>r s' p t'. P r s' \<Longrightarrow> Q p t' \<Longrightarrow> R (r, s') (p, t'))"
  shows "rel_spec f g s t R"
  using assms unfolding rel_spec_def always_progress.rep_eq runs_to.rep_eq
  by (cases "run f s"; cases "run g t"; simp add: rel_set_def split_beta')
     (metis all_not_in_conv bot_post_state_def prod.exhaust_sel)

lemma runs_to_res_independent_res: "f \<bullet> s \<lbrace>\<lambda>_. P\<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace>\<lambda>Res _. P\<rbrace>"
  by (rule runs_to_subst_Res)

lemma lift_state_spec_monad_eq[simp]: "lift_state (=) p = p"
  by transfer (simp add: prod.rel_eq fun_eq_iff rel_post_state_eq)

lemma rel_post_state_Sup:
  "rel_set (\<lambda>x y. rel_post_state Q (f x) (g y)) X Y \<Longrightarrow> rel_post_state Q (\<Squnion>x\<in>X. f x) (\<Squnion>x\<in>Y. g x)"
  by (force simp: rel_post_state_eq_sim_post_state rel_set_def intro!: sim_post_state_Sup)

lemma rel_set_Result_image_iff:
  "rel_set (rel_prod (\<lambda>Res v1 Res v2. (P v1 v2)) R)
     ((\<lambda>x. case x of (v, s) \<Rightarrow> (Result v, s)) ` Vals1)
     ((\<lambda>x. case x of (v, s) \<Rightarrow> (Result v, s)) ` Vals2)
   \<longleftrightarrow>
   rel_set (rel_prod P R) Vals1 Vals2"
  by (force simp add: rel_set_def)

lemma rel_post_state_converse_iff:
  "rel_post_state R X Y \<longleftrightarrow> rel_post_state R\<inverse>\<inverse> Y X"
  by (metis conversep_conversep rel_post_state_eq_sim_post_state)

lemma runs_to_le_post_state_iff: "runs_to f s Q \<longleftrightarrow> run f s \<le> Success {(r, s). Q r s}"
  by (cases "run f s") (auto simp add: runs_to.rep_eq)

lemma runs_to_partial_runs_to_iff: "runs_to_partial f s Q \<longleftrightarrow> (run f s = Failure \<or> runs_to f s Q)"
  by (cases "run f s"; simp add: runs_to_partial.rep_eq runs_to.rep_eq)

lemma run_runs_to_extensionality:
  "run f s = run g s \<longleftrightarrow> (\<forall>P. f \<bullet> s \<lbrace>P\<rbrace> \<longleftrightarrow> g \<bullet> s \<lbrace>P\<rbrace>)"
  apply transfer
  apply (simp add: post_state_eq_iff)
  apply (rule all_cong_map[where f'="\<lambda>P (x, y). P x y" and f="\<lambda>P x y. P (x, y)"])
  apply auto
  done

lemma le_spec_monad_runI: "(\<And>s. run f s \<le> run g s) \<Longrightarrow> f \<le> g"
  by transfer (simp add: le_fun_def)

subsection \<open>\<^const>\<open>rel_spec_monad\<close>\<close>

lemma rel_spec_monad_iff_rel_spec:
  "rel_spec_monad R Q f g \<longleftrightarrow> (\<forall>s t. R s t \<longrightarrow> rel_spec f g s t (rel_prod Q R))"
  unfolding rel_spec_monad_def rel_fun_def rel_spec.rep_eq ..

lemma rel_spec_monadI:
  "(\<And>s t. R s t \<Longrightarrow> rel_spec f g s t (rel_prod Q R)) \<Longrightarrow> rel_spec_monad R Q f g"
  by (auto simp: rel_spec_monad_iff_rel_spec)

lemma rel_spec_monadD:
  "rel_spec_monad R Q f g \<Longrightarrow> R s t \<Longrightarrow> rel_spec f g s t (rel_prod Q R)"
  by (auto simp: rel_spec_monad_iff_rel_spec)

lemma rel_spec_monad_eq_conv: "rel_spec_monad (=) (=) = (=)"
  unfolding rel_spec_monad_def by transfer (simp add: fun_eq_iff prod.rel_eq rel_post_state_eq)

lemma rel_spec_monad_converse_iff:
  "rel_spec_monad R Q f g \<longleftrightarrow> rel_spec_monad R\<inverse>\<inverse> Q\<inverse>\<inverse> g f"
  using rel_post_state_converse_iff
  by (metis conversep.cases conversep.intros prod.rel_conversep rel_spec_monad_def)

lemma rel_spec_monad_iff_refines:
  "rel_spec_monad S R f g \<longleftrightarrow>
    (\<forall>s t. S s t \<longrightarrow> (refines f g s t (rel_prod R S) \<and> refines g f t s (rel_prod R\<inverse>\<inverse> S\<inverse>\<inverse>)))"
  using rel_spec_iff_refines rel_spec_monad_iff_rel_spec
  by (metis prod.rel_conversep)

lemma rel_spec_monad_rel_exception_or_resultI:
  "rel_spec_monad R (rel_exception_or_result (=) (=)) f g \<Longrightarrow> rel_spec_monad R (=) f g"
  by (simp add: rel_exception_or_result_sum_eq)

lemma runs_to_partial_runs_to_fuse: 
  assumes part: "f \<bullet> s ?\<lbrace>Q\<rbrace>"
  assumes tot: "f \<bullet> s \<lbrace>P\<rbrace>"
  shows "f \<bullet> s \<lbrace>\<lambda>r t. Q r t \<and> P r t\<rbrace>"
  using assms
  apply (cases "run f s")
   apply (auto simp add: runs_to_def runs_to_partial_def)
  done

section \<open>VCG basic setup\<close>

lemma runs_to_cong_pred_only:
  "P = Q \<Longrightarrow> (p \<bullet> s \<lbrace> P \<rbrace>) \<longleftrightarrow> (p \<bullet> s \<lbrace> Q \<rbrace>)"
  by simp

lemma runs_to_cong_state_only[runs_to_vcg_cong_state_only]:
  "s = t \<Longrightarrow> (p \<bullet> s \<lbrace> Q \<rbrace>) \<longleftrightarrow> (p \<bullet> t \<lbrace> Q \<rbrace>)"
  by simp

lemma runs_to_partial_cong_state_only[runs_to_vcg_cong_state_only]:
  "s = t \<Longrightarrow> (p \<bullet> s ?\<lbrace> Q \<rbrace>) \<longleftrightarrow> (p \<bullet> t ?\<lbrace> Q \<rbrace>)"
  by simp

lemma runs_to_cong_program_only[runs_to_vcg_cong_program_only]:
  "p = q \<Longrightarrow> (p \<bullet> s \<lbrace> Q \<rbrace>) \<longleftrightarrow> (q \<bullet> s \<lbrace> Q \<rbrace>)"
  by simp

lemma runs_to_partial_cong_program_only[runs_to_vcg_cong_program_only]:
  "p = q \<Longrightarrow> (p \<bullet> s ?\<lbrace> Q \<rbrace>) \<longleftrightarrow> (q \<bullet> s ?\<lbrace> Q \<rbrace>)"
  by simp

lemma runs_to_case_conv[simp]:
  "((case (a, b) of (x, y) \<Rightarrow> f x y) \<bullet> s \<lbrace> Q \<rbrace>) \<longleftrightarrow> ((f a b) \<bullet> s \<lbrace> Q \<rbrace>)"
  by simp

lemma runs_to_partial_case_conv[simp]:
  "((case (a, b) of (x, y) \<Rightarrow> f x y) \<bullet> s ?\<lbrace> Q \<rbrace>) \<longleftrightarrow> ((f a b) \<bullet> s ?\<lbrace> Q \<rbrace>)"
  by simp

lemma always_progress_prod_case[always_progress_intros]:
  "always_progress (f (fst p) (snd p)) \<Longrightarrow> always_progress (case p of (x, y) \<Rightarrow> f x y)"
  by (auto simp add: always_progress_def split: prod.splits)

lemma runs_to_conj:
  "(f \<bullet> s \<lbrace> \<lambda>r s. P r s \<and> Q r s\<rbrace>) \<longleftrightarrow> (f \<bullet> s \<lbrace> \<lambda>r s. P r s \<rbrace>) \<and> (f \<bullet> s \<lbrace> \<lambda>r s. Q r s\<rbrace>)"
  by (cases "run f s") (auto simp: runs_to.rep_eq)

lemma runs_to_all:
  "(f \<bullet> s \<lbrace> \<lambda>r s. \<forall>x. P x r s \<rbrace>) \<longleftrightarrow> (\<forall>x. f \<bullet> s \<lbrace> \<lambda>r s. P x r s \<rbrace>)"
  by (cases "run f s") (auto simp: runs_to.rep_eq)

lemma runs_to_imp_const:
  "(f \<bullet> s \<lbrace> \<lambda>r s. P r s \<longrightarrow> Q \<rbrace>) \<longleftrightarrow> (Q \<and> (f \<bullet> s \<lbrace>\<lambda>_ _. True \<rbrace>)) \<or> (\<not> Q \<and> (f \<bullet> s \<lbrace> \<lambda>r s. \<not> P r s\<rbrace>))"
  by (cases "run f s") (auto simp: runs_to.rep_eq)

subsection \<open>\<open>res_monad\<close> and \<open>exn_monad\<close> Types\<close>

type_synonym 'a val = "(unit, 'a) exception_or_result"
type_synonym ('e, 'a) xval = "('e option, 'a) exception_or_result"
type_synonym ('a, 's) res_monad = "(unit, 'a , 's) spec_monad"
type_synonym ('e, 'a, 's) exn_monad = "('e option, 'a, 's) spec_monad"

definition Exn :: "'e \<Rightarrow> ('e, 'a) xval" where
  "Exn e = Exception (Some e)"

definition
  case_xval :: "('e \<Rightarrow> 'a) \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('e, 'v) xval \<Rightarrow> 'a" where
  "case_xval f g x =
    (case x of
       Exception v \<Rightarrow> (case v of Some e \<Rightarrow> f e | None \<Rightarrow> undefined)
     | Result v \<Rightarrow> g v)"

declare [[case_translation case_xval Exn Result]]

inductive rel_xval:: "('e \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
  ('e, 'a) xval \<Rightarrow> ('f, 'b) xval \<Rightarrow> bool"
  where
Exn: "E e f \<Longrightarrow> rel_xval E R (Exn e) (Exn f)" | 
Result: "R a b \<Longrightarrow> rel_xval E R (Result a) (Result b)"

definition map_xval :: "('e \<Rightarrow> 'f) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('e, 'a) xval \<Rightarrow> ('f, 'b) xval" where
  "map_xval f g x \<equiv> case x of Exn e \<Rightarrow> Exn (f e) | Result v \<Rightarrow> Result (g v)"

lemma rel_xval_eq: "rel_xval (=) (=) = (=)"
  apply (rule ext)+
  subgoal for x y
    apply (cases x)
    apply (auto simp add: rel_xval.simps default_option_def Exn_def)
    done
  done

lemma rel_xval_rel_exception_or_result_conv: 
  "rel_xval E R = rel_exception_or_result (rel_map the OO E OO rel_map Some) R"
  apply (rule ext)+
  subgoal for x y
    apply (cases x)
    subgoal
      by (auto simp add: rel_exception_or_result.simps rel_xval.simps Exn_def default_option_def rel_map_def)
        (metis option.sel rel_map_direct relcomppI)+
    subgoal
      by (auto simp add: rel_exception_or_result.simps rel_xval.simps Exn_def default_option_def rel_map_def)
    done
  done

lemmas rel_xval_Exn = rel_xval.intros(1)
lemmas rel_xval_Result = rel_xval.intros(2)

lemma case_xval_simps[simp]:
  "case_xval f g (Exn v) = f v"
  "case_xval f g (Result e) = g e"
   by (auto simp add: case_xval_def Exn_def)

lemma case_exception_or_result_Exn[simp]:
  "case_exception_or_result f g (Exn x) = f (Some x)"
  by (simp add: Exn_def)

lemma xval_split:
  "P (case_xval f g r) \<longleftrightarrow>
    (\<forall>e. r = Exn e \<longrightarrow> P (f e)) \<and>
    (\<forall>v. r = Result v \<longrightarrow> P (g v))"
  by (auto simp add: case_xval_def Exn_def split: exception_or_result_splits option.splits)

lemma xval_split_asm:
  "P (case_xval f g r) \<longleftrightarrow>
  \<not> ((\<exists>e. r = Exn e \<and> \<not> P (f e)) \<or>
    (\<exists>v. r = Result v \<and> \<not> P (g v)))"
  by (auto simp add: case_xval_def Exn_def split: exception_or_result_splits option.splits)

lemmas xval_splits = xval_split xval_split_asm

lemma Exn_eq_Exn[simp]: "Exn x = Exn y \<longleftrightarrow> x = y"
  by (simp add: Exn_def)

lemma Exn_neq_Result[simp]: "Exn x = Result e \<longleftrightarrow> False"
  by (simp add: Exn_def)

lemma Result_neq_Exn[simp]: "Result e = Exn x \<longleftrightarrow> False"
  by (simp add: Exn_def)

lemma Exn_eq_Exception[simp]:
  "Exn x = Exception a \<longleftrightarrow> a = Some x"
  "Exception a = Exn x  \<longleftrightarrow> a = Some x"
  by (auto simp: Exn_def)

lemma map_exception_or_result_Exn[simp]:
  "(\<And>x. f (Some x) \<noteq> None) \<Longrightarrow> map_exception_or_result f g (Exn x) = Exn (the (f (Some x)))"
  by (simp add: Exn_def)

lemma case_xval_Exception_Some_simp[simp]: "(case Exception (Some y) of Exn e \<Rightarrow> f e | Result v \<Rightarrow> g v) = f y "
  by (metis Exn_def case_xval_simps(1))

lemma rel_xval_simps[simp]: 
  "rel_xval E R (Exn e) (Exn f) = E e f"
  "rel_xval E R (Result v) (Result w) = R v w"
  "rel_xval E R (Exn e) (Result w) = False"
  "rel_xval E R (Result v) (Exn f) = False"
  by (auto simp add: rel_xval.simps)

lemma map_xval_simps[simp]: 
  "map_xval f g (Exn e) = Exn (f e)"
  "map_xval f g (Result v) = Result (g v)"
  by (auto simp add: map_xval_def)

lemma map_xval_Exn: "map_xval f g x = Exn y \<longleftrightarrow> (\<exists>e. x = Exn e \<and> y = f e)"
  by (auto simp add: map_xval_def split: xval_splits)

lemma map_xval_Result: "map_xval f g x = Result y \<longleftrightarrow> (\<exists>v. x = Result v \<and> y = g v)"
  by (auto simp add: map_xval_def split: xval_splits)

lemma Result_unit_eq: "(x:: unit val) = Result ()"
  by (cases x) auto

simproc_setup Result_unit_eq ("x::(unit val)") = \<open>
let
  fun is_Result_unit \<^Const>\<open>Result \<open>@{typ "unit"}\<close> \<open>@{typ "unit"}\<close> for \<^Const>\<open>Product_Type.Unity\<close>\<close> = true
    | is_Result_unit _ = false
  in
    K (K (fn ct =>
      if is_Result_unit (Thm.term_of ct) then NONE
      else SOME (mk_meta_eq @{thm Result_unit_eq})))
  end
\<close>

lemma ex_val_Result1:
  "\<exists>v1. (x::'v1 val) = Result v1"
  by (cases x) auto

lemma ex_val_Result2:
  "\<exists>v1 v2. (x::('v1 * 'v2) val) = Result (v1, v2)"
  by (cases x) auto

lemma ex_val_Result3:
  "\<exists>v1 v2 v3. (x::('v1 * 'v2 * 'v3) val) = Result (v1, v2, v3)"
  by (cases x) auto

lemma ex_val_Result4:
  "\<exists>v1 v2 v3 v4. (x::('v1 * 'v2 * 'v3 * 'v4) val) = Result (v1, v2, v3, v4)"
  by (cases x) auto

lemma ex_val_Result5:
  "\<exists>v1 v2 v3 v4 v5. (x::('v1 * 'v2 * 'v3 * 'v4 * 'v5) val) = Result (v1, v2, v3, v4, v5)"
  by (cases x) auto

lemma ex_val_Result6:
  "\<exists>v1 v2 v3 v4 v5 v6. (x::('v1 * 'v2 * 'v3 * 'v4 * 'v5  * 'v6) val) = Result (v1, v2, v3, v4, v5, v6)"
  by (cases x) auto

lemma ex_val_Result7:
  "\<exists>v1 v2 v3 v4 v5 v6 v7. (x::('v1 * 'v2 * 'v3 * 'v4 * 'v5  * 'v6 * 'v7) val) = Result (v1, v2, v3, v4, v5, v6, v7)"
  by (cases x) auto

lemma ex_val_Result8:
  "\<exists>v1 v2 v3 v4 v5 v6 v7 v8. (x::('v1 * 'v2 * 'v3 * 'v4 * 'v5  * 'v6 * 'v7 * 'v8) val) = Result (v1, v2, v3, v4, v5, v6, v7, v8)"
  by (cases x) auto

lemma ex_val_Result9:
  "\<exists>v1 v2 v3 v4 v5 v6 v7 v8 v9. (x::('v1 * 'v2 * 'v3 * 'v4 * 'v5  * 'v6 * 'v7 * 'v8 * 'v9) val) = Result (v1, v2, v3, v4, v5, v6, v7, v8, v9)"
  by (cases x) auto

lemma ex_val_Result10:
  "\<exists>v1 v2 v3 v4 v5 v6 v7 v8 v9 v10. (x::('v1 * 'v2 * 'v3 * 'v4 * 'v5  * 'v6 * 'v7 * 'v8 * 'v9 * 'v10) val) = Result (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10)"
  by (cases x) auto


lemma ex_val_Result11:
  "\<exists>v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11. (x::('v1 * 'v2 * 'v3 * 'v4 * 'v5  * 'v6 * 'v7 * 'v8 * 'v9 * 'v10 * 'v11) val) = Result (v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11)"
  by (cases x) auto


lemmas ex_val_Result[simp] =
  ex_val_Result1
  ex_val_Result2
  ex_val_Result3
  ex_val_Result4
  ex_val_Result5
  ex_val_Result6
  ex_val_Result7
  ex_val_Result8
  ex_val_Result9
  ex_val_Result10
  ex_val_Result11

lemma all_val_imp_iff: "(\<forall>v. (r::'a val) = Result v \<longrightarrow> P) \<longleftrightarrow> P"
  by (cases r) auto

definition map_exn :: "('e \<Rightarrow> 'f) \<Rightarrow> ('e, 'a) xval \<Rightarrow> ('f, 'a) xval" where
  "map_exn f x =
    (case x of
       Exn e \<Rightarrow> Exn (f e)
     | Result v \<Rightarrow> Result v)"

lemma map_exn_simps[simp]:
  "map_exn f (Exn e) = Exn (f e)"
  "map_exn f (Result v) = Result v"
  "map_exn f x = Result v \<longleftrightarrow> x = Result v"
  by (auto simp add: map_exn_def split: xval_splits)

lemma map_exn_id[simp]: "map_exn (\<lambda>x. x) = (\<lambda>x. x)"
  by (auto simp add: map_exn_def split: xval_splits)

definition unnest_exn :: "('e + 'a, 'a) xval \<Rightarrow> ('e, 'a) xval" where
  "unnest_exn x =
     (case x of
        Exn e \<Rightarrow> (case e of Inl l \<Rightarrow> Exn l | Inr r \<Rightarrow> Result r)
      | Result v \<Rightarrow> Result v)"

lemma unnest_exn_simps[simp]:
  "unnest_exn (Exn (Inl l)) = Exn l"
  "unnest_exn (Exn (Inr r)) = Result r"
  "unnest_exn (Result v) = Result v"
   by (auto simp add: unnest_exn_def split: xval_splits)

lemma unnest_exn_eq_simps[simp]:
  "unnest_exn (Result r) = Result r' \<longleftrightarrow> r = r'"
  "unnest_exn (Result e) \<noteq> Exn e"
  "unnest_exn (Exn e) = Result r \<longleftrightarrow> e = Inr r"
  "unnest_exn (Exn e) = Exn e' \<longleftrightarrow> e = Inl e'"
  by (auto simp: unnest_exn_def split: xval_splits sum.splits)

definition the_Exn :: "('e, 'a) xval \<Rightarrow> 'e" where
  "the_Exn x \<equiv> (case x of Exn e \<Rightarrow> e | Result _ \<Rightarrow> undefined)"

abbreviation the_Res :: "'a val \<Rightarrow> 'a" where "the_Res \<equiv> the_Result"

lemma is_Exception_val[simp]: "is_Exception (x::'a val) = False"
  by (auto simp add: is_Exception_def)

lemma is_Exception_Exn[simp]: "is_Exception (Exn x)"
  by (simp add: Exn_def)

lemma is_Result_val[simp]: "is_Result (v::'a val)"
  by (auto simp add: is_Result_def)

lemma the_Exception_Exn[simp]: "the_Exception (Exn e) = Some e"
  by (auto simp add: the_Exception_def)

lemma the_Exn_Exn[simp]:
  "the_Exn (Exn e) = e"
  "the_Exn (Exception (Some e)) = e"
   by (auto simp add: the_Exn_def case_xval_def)

lemma the_Result_simp[simp]:
  "the_Result (Result v) = v"
  by (auto simp add: the_Result_def)

lemma Result_the_Result_val[simp]: "Result (the_Result (x::'a val)) = x"
  by (auto simp add: the_Result_def)

lemma rel_exception_or_result_val_apply:
  fixes x::"'a val"
  fixes y ::"'b val"
  shows "rel_exception_or_result E R x y \<longleftrightarrow> rel_exception_or_result E' R x y"
  by (auto simp add: rel_exception_or_result.simps)

lemma rel_exception_or_result_val:
  shows "((rel_exception_or_result E R)::'a val \<Rightarrow> 'b val \<Rightarrow> bool) = rel_exception_or_result E' R"
  apply (rule ext)+
  apply (auto simp add: rel_exception_or_result.simps)
  done

lemma rel_exception_or_result_Res_val:
  "(\<lambda>Res x Res y. R x y) = rel_exception_or_result (\<lambda>_ _. False) R"
  apply (rule ext)+
  apply auto
  done

definition unite:: "('a, 'a) xval \<Rightarrow> 'a val" where
  "unite x = (case x of Exn v \<Rightarrow> Result v | Result v \<Rightarrow> Result v)"

lemma unite_simps[simp]:
  "unite (Exn v) = Result v"
  "unite (Result v) = Result v"
  by (auto simp add: unite_def)

lemma val_exhaust: "(\<And>v. (x::'a val) = Result v \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases x) auto

lemma val_iff: "P (x::'a val) \<longleftrightarrow> (\<exists>v. x = Result v \<and> P (Result v))"
  by (cases x) auto

lemma val_nchotomy: "\<forall>(x::'a val). \<exists>v. x = Result v"
  by (meson val_exhaust)

lemma "(\<And>x::'a val. PROP P x) \<Longrightarrow> PROP P (Result (v::'a))"
  by (rule meta_spec)

lemma val_Result_the_Result_conv: "(x::'a val) = Result (the_Result x)"
  by (cases x) (auto simp add: the_Result_def)

lemma split_val_all[simp]: "(\<And>x::'a val. PROP P x) \<equiv> (\<And>v::'a. PROP P (Result v))"
proof
  fix v::'a
  assume "\<And>x::'a val. PROP P x"
  then show "PROP P (Result v)" .
next
  fix x::"'a val"
  assume "\<And>v::'a. PROP P (Result v)"
  hence "PROP P (Result (the_Result x))" .
  thus "PROP P x"
    apply (subst val_Result_the_Result_conv)
    apply (assumption)
    done
qed

lemma split_val_Ex[simp]: "(\<exists>(x::'a val). P x) \<longleftrightarrow> (\<exists>(v::'a). P (Result v))"
  by (auto)

lemma split_val_All[simp]: "(\<forall>(x::'a val). P x) \<longleftrightarrow> (\<forall>(v::'a). P (Result v))"
  by (auto)

definition to_xval :: "('e + 'a) \<Rightarrow> ('e, 'a) xval" where
 "to_xval x = (case x of Inl e \<Rightarrow> Exn e | Inr v \<Rightarrow> Result v)"

lemma to_xval_simps[simp]:
  "to_xval (Inl e) = Exn e"
  "to_xval (Inr v) = Result v"
   by (auto simp add: to_xval_def)

lemma to_xval_Result_iff[simp]: "to_xval x = Result v \<longleftrightarrow> x = Inr v"
  apply (cases x)
   apply (auto simp add: to_xval_def default_option_def)
  done

lemma to_xval_Exn_iff[simp]: 
 "to_xval x = Exn v \<longleftrightarrow>
    (x  = Inl v)"
  apply (cases x)
   apply (auto simp add: to_xval_def default_option_def Exn_def)
  done

lemma to_xval_Exception_iff[simp]: 
 "to_xval x = Exception v \<longleftrightarrow>
    ((v = None \<and> x = Inr undefined) \<or> (\<exists>e. v = Some e \<and> x  = Inl e))"
  apply (cases x)
   apply (auto simp add: to_xval_def default_option_def Exn_def)
  done


definition from_xval :: "('e, 'a) xval \<Rightarrow> ('e + 'a)" where
 "from_xval x = (case x of Exn e \<Rightarrow> Inl e | Result v \<Rightarrow> Inr v)"

lemma from_xval_simps[simp]:
  "from_xval (Exn e) = Inl e"
  "from_xval (Result v) = Inr v"
  by (auto simp add: from_xval_def)

lemma from_xval_Inr_iff[simp]: "from_xval x = Inr v \<longleftrightarrow> x = Result v"
  apply (cases x)
   apply (auto simp add: from_xval_def split: xval_splits)
  done

lemma from_xval_Inl_iff[simp]: "from_xval x = Inl e \<longleftrightarrow> x = Exn e"
  apply (cases x)
   apply (auto simp add: from_xval_def split: xval_splits)
  done

lemma to_xval_from_xval[simp]: "to_xval (from_xval x) = x"
  apply (cases x)
   apply (auto simp add: Exn_def default_option_def)
  done

lemma from_xval_to_xval[simp]: "from_xval (to_xval x) = x"
  apply (cases x)
   apply (auto simp add: Exn_def default_option_def)
  done

lemma rel_map_to_xval_Exn_iff[simp]:  "rel_map to_xval y (Exn e) \<longleftrightarrow> y = Inl e"
  by (auto simp add: rel_map_def to_xval_def split: sum.splits)

lemma rel_map_to_xval_Inr_iff[simp]:  "rel_map to_xval (Inr r) x \<longleftrightarrow> x = Result r"
  by (auto simp add: rel_map_def)

lemma rel_map_to_xval_Inl_iff[simp]:  "rel_map to_xval (Inl l) x \<longleftrightarrow> x = Exn l"
  by (auto simp add: rel_map_def)

lemma rel_map_to_xval_Result_iff[simp]:  "rel_map to_xval y (Result r) \<longleftrightarrow> y = Inr r"
  by (auto simp add: rel_map_def to_xval_def split: sum.splits)

lemma rel_map_from_xval_Exn_iff[simp]:  "rel_map from_xval (Exn l) x \<longleftrightarrow> x = Inl l"
  by (auto simp add: rel_map_def)

lemma rel_map_from_xval_Inl_iff[simp]:  "rel_map from_xval y (Inl e) \<longleftrightarrow> y = Exn e"
  by (auto simp add: rel_map_def from_xval_def split: xval_splits)

lemma rel_map_from_xval_Result_iff[simp]:  "rel_map from_xval (Result r) x \<longleftrightarrow> x = Inr r"
  by (auto simp add: rel_map_def)

lemma rel_map_from_xval_Inr_iff[simp]:  "rel_map from_xval y (Inr r) \<longleftrightarrow> y = Result r"
  by (auto simp add: rel_map_def from_xval_def split: xval_splits)

section \<open>\<open>res_monad\<close> and \<open>exn_monad\<close> functions\<close>

abbreviation "throw e \<equiv> yield (Exn e)"

definition "try" :: "('e + 'a, 'a, 's) exn_monad \<Rightarrow> ('e, 'a, 's) exn_monad" where
  "try = map_value unnest_exn"

definition "finally" :: "('a, 'a, 's) exn_monad \<Rightarrow> ('a, 's) res_monad" where
  "finally = map_value unite"

definition
  catch :: "('e, 'a, 's) exn_monad \<Rightarrow>
            ('e \<Rightarrow> ( 'f::default, 'a, 's) spec_monad) \<Rightarrow>
            ('f::default, 'a, 's) spec_monad" (infix \<open><catch>\<close> 10)
where
  "f <catch> handler \<equiv> bind_handle f return (handler o the)"

abbreviation bind_finally ::
  "('e, 'a, 's) exn_monad \<Rightarrow> (('e, 'a) xval \<Rightarrow> ('b, 's) res_monad) \<Rightarrow> ('b, 's) res_monad"
where
  "bind_finally \<equiv> bind_exception_or_result"

definition ignoreE ::"('e, 'a, 's) exn_monad \<Rightarrow> ('a, 's) res_monad" where
  "ignoreE f = catch f (\<lambda>_. bot)"

definition liftE :: "('a, 's) res_monad \<Rightarrow> ('e, 'a, 's) exn_monad" where
  "liftE = map_value (map_exception_or_result (\<lambda>x. undefined) id)"

definition check:: "'e \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('e, 'a, 's) exn_monad" where
  "check e p =
    condition (\<lambda>s. \<exists>x. p s x)
    (do { s \<leftarrow> get_state; select {x. p s x} })
    (throw e)"

abbreviation check' :: "'e \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, unit, 's) exn_monad" where
  "check' e p \<equiv> check e (\<lambda>s _. p s)"

section "Monad operations"

subsection \<open>\<^const>\<open>top\<close>\<close>

declare top_spec_monad.rep_eq[run_spec_monad, simp]

lemma always_progress_top[always_progress_intros]: "always_progress \<top>"
  by transfer simp

lemma runs_to_top[simp]: "\<top> \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> False"
  by transfer simp

lemma runs_to_partial_top[simp]: "\<top> \<bullet> s ?\<lbrace> Q \<rbrace> \<longleftrightarrow> True"
  by transfer simp

subsection \<open>\<^const>\<open>bot\<close>\<close>

declare bot_spec_monad.rep_eq[run_spec_monad, simp]

lemma always_progress_bot_iff[iff]: "always_progress \<bottom> \<longleftrightarrow> False"
  by transfer simp

lemma runs_to_bot[simp]: "\<bottom> \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> True"
  by transfer simp

lemma runs_to_partial_bot[simp]: "\<bottom> \<bullet> s ?\<lbrace> Q \<rbrace> \<longleftrightarrow> True"
  by transfer simp

subsection \<open>\<^const>\<open>fail\<close>\<close>

lemma always_progress_fail[always_progress_intros]: "always_progress fail"
  by transfer (simp add: bot_post_state_def)

lemma run_fail[run_spec_monad, simp]: "run fail s = \<top>"
  by transfer (simp add: top_post_state_def)

lemma runs_to_fail[simp]: "fail \<bullet> s \<lbrace> R \<rbrace> \<longleftrightarrow> False"
  by transfer simp

lemma runs_to_partial_fail[simp]: "fail \<bullet> s ?\<lbrace> R \<rbrace> \<longleftrightarrow> True"
  by transfer simp

lemma refines_fail[simp]: "refines f fail s t R"
  by (simp add: refines.rep_eq)

lemma rel_spec_fail[simp]: "rel_spec fail fail s t R"
  by (simp add: rel_spec_def)

subsection \<open>\<^const>\<open>yield\<close>\<close>

lemma run_yield[run_spec_monad, simp]: "run (yield r) s = pure_post_state (r, s)"
  by transfer simp

lemma always_progress_yield[always_progress_intros]: "always_progress (yield r)"
  by (simp add: always_progress_def)

lemma yield_inj[simp]: "yield x = yield y \<longleftrightarrow> x = y"
  by transfer (auto simp: fun_eq_iff)

lemma runs_to_yield_iff[simp]: "((yield r) \<bullet> s \<lbrace> Q \<rbrace>) \<longleftrightarrow> Q r s"
  by transfer simp

lemma runs_to_yield[runs_to_vcg]: "Q r s \<Longrightarrow> yield r \<bullet> s \<lbrace> Q \<rbrace>"
  by simp

lemma runs_to_partial_yield_iff[simp]: "((yield r) \<bullet> s ?\<lbrace> Q \<rbrace>) \<longleftrightarrow> Q r s"
  by transfer simp

lemma runs_to_partial_yield[runs_to_vcg]: "Q r s \<Longrightarrow> yield r \<bullet> s ?\<lbrace> Q \<rbrace>"
  by simp

lemma refines_yield_iff[simp]: "refines (yield r) (yield r') s s' R \<longleftrightarrow> R (r, s) (r', s')"
  by transfer simp

lemma refines_yield: "R (a, s) (b, t) \<Longrightarrow> refines (yield a) (yield b) s t R"
  by simp

lemma refines_yield_right_iff:
  "refines f (yield e) s t R \<longleftrightarrow> (f \<bullet> s \<lbrace> \<lambda>r s'. R (r, s') (e, t) \<rbrace>)"
  by (auto simp: refines.rep_eq runs_to.rep_eq sim_post_state_pure_post_state2 split_beta')

lemma rel_spec_yield: "R (a, s) (b, t) \<Longrightarrow> rel_spec (yield a) (yield b) s t R"
  by (simp add: rel_spec_def)

lemma rel_spec_yield_iff[simp]: "rel_spec (yield x) (yield y) s t Q \<longleftrightarrow> Q (x, s) (y, t)"
  by (simp add: rel_spec.rep_eq)

lemma rel_spec_monad_yield: "Q x y \<Longrightarrow> rel_spec_monad R Q (yield x) (yield y)"
  by (auto simp add: rel_spec_monad_iff_rel_spec)

subsection \<open>\<^const>\<open>throw_exception_or_result\<close>\<close>

lemma throw_exception_or_result_bind[simp]:
  "e \<noteq> default \<Longrightarrow> throw_exception_or_result e >>= f = throw_exception_or_result e"
  unfolding bind_def by transfer auto

subsection \<open>\<^const>\<open>throw\<close>\<close>

lemma throw_bind[simp]: "throw e >>= f = throw e"
  by (simp add: Exn_def)

subsection \<open>\<^const>\<open>get_state\<close>\<close>

lemma always_progress_get_state[always_progress_intros]: "always_progress get_state"
  by transfer simp

lemma run_get_state[run_spec_monad, simp]: "run get_state s = pure_post_state (Result s, s)"
  by transfer simp

lemma runs_to_get_state[runs_to_vcg]: "get_state \<bullet> s \<lbrace>\<lambda>r t. r = Result s \<and> t = s\<rbrace>"
  by transfer simp

lemma runs_to_get_state_iff[runs_to_iff]: "get_state \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (Q (Result s) s)"
  by transfer simp

lemma runs_to_partial_get_state[runs_to_vcg]: "get_state \<bullet> s ?\<lbrace>\<lambda>r t. r = Result s \<and> t = s\<rbrace>"
  by transfer simp

lemma refines_get_state: "R (Result s, s) (Result t, t) \<Longrightarrow> refines get_state get_state s t R"
  by transfer simp

lemma rel_spec_get_state: "R (Result s, s) (Result t, t) \<Longrightarrow> rel_spec get_state get_state s t R"
  by (auto simp: rel_spec_iff_refines intro: refines_get_state)

subsection \<open>\<^const>\<open>set_state\<close>\<close>

lemma always_progress_set_state[always_progress_intros]: "always_progress (set_state t)"
  by transfer simp

lemma set_state_inj[simp]: "set_state x = set_state y \<longleftrightarrow> x = y"
  by transfer (simp add: fun_eq_iff)

lemma run_set_state[run_spec_monad, simp]: "run (set_state t) s = pure_post_state (Result (), t)"
  by transfer simp

lemma runs_to_set_state[runs_to_vcg]: "set_state t \<bullet> s \<lbrace>\<lambda>r t'. t' = t\<rbrace>"
  by transfer simp

lemma runs_to_set_state_iff[runs_to_iff]: "set_state t \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> Q (Result ()) t"
  by transfer simp

lemma runs_to_partial_set_state[runs_to_vcg]: "set_state t \<bullet> s ?\<lbrace>\<lambda>r t'. t' = t\<rbrace>"
  by transfer simp

lemma refines_set_state:
  "R (Result (), s') (Result (), t') \<Longrightarrow> refines (set_state s') (set_state t') s t R"
  by transfer simp

lemma rel_spec_set_state:
  "R (Result (), s') (Result (), t') \<Longrightarrow> rel_spec (set_state s') (set_state t') s t R"
  by (auto simp add: rel_spec_iff_refines intro: refines_set_state)

subsection \<open>\<^const>\<open>select\<close>\<close>

lemma always_progress_select[always_progress_intros]: "S \<noteq> {} \<Longrightarrow> always_progress (select S)"
  unfolding select_def by transfer simp

lemma runs_to_select[runs_to_vcg]: "(\<And>x. x \<in> S \<Longrightarrow> Q (Result x) s) \<Longrightarrow> select S \<bullet> s \<lbrace> Q \<rbrace>"
  unfolding select_def by transfer simp

lemma runs_to_select_iff[runs_to_iff]: "select S \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (\<forall>x\<in>S. Q (Result x) s)"
  unfolding select_def by transfer auto

lemma runs_to_partial_select[runs_to_vcg]: "(\<And>x. x \<in> S \<Longrightarrow> Q (Result x) s) \<Longrightarrow> select S \<bullet> s ?\<lbrace> Q \<rbrace>"
  using runs_to_select by (rule runs_to_partial_of_runs_to)

lemma run_select[run_spec_monad, simp]: "run (select S) s = Success ((\<lambda>v. (Result v, s)) ` S)"
  unfolding select_def by transfer (auto simp add: image_image pure_post_state_def Sup_Success)

lemma refines_select:
  "(\<And>x. x \<in> P \<Longrightarrow> \<exists>xa\<in>Q. R (Result x, s) (Result xa, t)) \<Longrightarrow> refines (select P) (select Q) s t R"
  unfolding select_def by transfer (auto intro!: sim_post_state_Sup)

lemma rel_spec_select:
  "rel_set (\<lambda>a b. R (Result a, s) (Result b, t)) P Q \<Longrightarrow> rel_spec (select P) (select Q) s t R"
  by (auto simp add: rel_spec_def rel_set_def)

subsection \<open>\<^const>\<open>unknown\<close>\<close>

lemma runs_to_unknown[runs_to_vcg]: "(\<And>x. Q (Result x) s) \<Longrightarrow> unknown \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: unknown_def runs_to_select_iff)

lemma runs_to_unknown_iff[runs_to_iff]: "unknown \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (\<forall>x. Q (Result x) s)"
  by (simp add: unknown_def runs_to_select_iff)

lemma runs_to_partial_unknown[runs_to_vcg]: "(\<And>x. Q (Result x) s) \<Longrightarrow> unknown \<bullet> s ?\<lbrace> Q \<rbrace>"
  using runs_to_unknown by (rule runs_to_partial_of_runs_to)

lemma run_unknown[run_spec_monad, simp]: "run unknown s = Success ((\<lambda>v. (Result v, s)) ` UNIV)"
  unfolding unknown_def by simp

lemma always_progress_unknown[always_progress_intros]: "always_progress unknown"
  unfolding unknown_def by (simp add: always_progress_intros)

subsection \<open>\<^const>\<open>lift_state\<close>\<close>

lemma run_lift_state[run_spec_monad]:
  "run (lift_state R f) s = lift_post_state (rel_prod (=) R) (SUP t\<in>{t. R s t}. run f t)"
  by transfer standard

lemma runs_to_lift_state_iff[runs_to_iff]:
  "(lift_state R f) \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (\<forall>s'. R s s' \<longrightarrow> f \<bullet> s' \<lbrace>\<lambda>r t'. \<forall>t. R t t' \<longrightarrow> Q r t\<rbrace>)"
  by (simp add: runs_to.rep_eq lift_state.rep_eq rel_prod_sel split_beta')

lemma runs_to_lift_state[runs_to_vcg]:
  "(\<And>s'. R s s' \<Longrightarrow> f \<bullet> s' \<lbrace>\<lambda>r t'. \<forall>t. R t t' \<longrightarrow> Q r t\<rbrace>) \<Longrightarrow> lift_state R f \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_lift_state_iff)

lemma runs_to_partial_lift_state[runs_to_vcg]:
  "(\<And>s'. R s s' \<Longrightarrow> f \<bullet> s' ?\<lbrace>\<lambda>r t'.  \<forall>t. R t t' \<longrightarrow> Q r t\<rbrace>) \<Longrightarrow> lift_state R f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (cases "\<forall>s'. R s s' \<longrightarrow> run f s' \<noteq> Failure")
     (auto simp: runs_to_partial_alt run_lift_state lift_post_state_Sup image_image
                 image_iff runs_to_lift_state_iff top_post_state_def)

lemma mono_lift_state: "f \<le> f' \<Longrightarrow> lift_state R f \<le> lift_state R f'"
  by transfer (auto simp: le_fun_def intro!: lift_post_state_mono SUP_mono)

subsection \<open>const\<open>exec_concrete\<close>\<close>

lemma run_exec_concrete[run_spec_monad]:
  "run (exec_concrete st f) s = map_post_state (apsnd st) (\<Squnion> (run f ` st -` {s}))"
  by (auto simp add: exec_concrete_def lift_state_def map_post_state_eq_lift_post_state fun_eq_iff
           intro!: arg_cong2[where f=lift_post_state] SUP_cong)

lemma runs_to_exec_concrete_iff[runs_to_iff]:
  "exec_concrete st f \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (\<forall>t. s = st t \<longrightarrow> f \<bullet> t \<lbrace>\<lambda>r t.  Q r (st t)\<rbrace>)"
  by (auto simp: runs_to.rep_eq run_exec_concrete split_beta')

lemma runs_to_exec_concrete[runs_to_vcg]:
  "(\<And>t. s = st t \<Longrightarrow> f \<bullet> t \<lbrace>\<lambda>r t.  Q r (st t)\<rbrace>) \<Longrightarrow> exec_concrete st f \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_exec_concrete_iff)

lemma runs_to_partial_exec_concrete[runs_to_vcg]:
  "(\<And>t. s = st t \<Longrightarrow> f \<bullet> t ?\<lbrace>\<lambda>r t.  Q r (st t)\<rbrace>) \<Longrightarrow> exec_concrete st f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: exec_concrete_def runs_to_partial_lift_state)

lemma mono_exec_concrete: "f \<le> f' \<Longrightarrow> exec_concrete st f \<le> exec_concrete st f'"
  unfolding exec_concrete_def by (rule mono_lift_state)

lemma monotone_exec_concrete_le[partial_function_mono]:
  "monotone Q (\<le>) f \<Longrightarrow> monotone Q (\<le>) (\<lambda>f'. exec_concrete st (f f'))"
  using mono_exec_concrete
  by (fastforce simp add: monotone_def le_fun_def)

lemma monotone_exec_concrete_ge[partial_function_mono]:
  "monotone Q (\<ge>) f \<Longrightarrow> monotone Q (\<ge>) (\<lambda>f'. exec_concrete st (f f'))"
  using mono_exec_concrete
  by (fastforce simp add: monotone_def le_fun_def)

subsection \<open>const\<open>exec_abstract\<close>\<close>

lemma run_exec_abstract[run_spec_monad]:
  "run (exec_abstract st f) s = vmap_post_state (apsnd st) (run f (st s))"
  by (auto simp add: exec_abstract_def vmap_post_state_eq_lift_post_state lift_state_def fun_eq_iff
           intro!: arg_cong2[where f=lift_post_state])

lemma runs_to_exec_abstract_iff[runs_to_iff]:
  "exec_abstract st f \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> f \<bullet> (st s) \<lbrace>\<lambda>r t. \<forall>s'. t = st s' \<longrightarrow> Q r s'\<rbrace> "
  by (simp add: runs_to.rep_eq run_exec_abstract split_beta' prod_eq_iff eq_commute)

lemma runs_to_exec_abstract[runs_to_vcg]:
  "f \<bullet> (st s) \<lbrace>\<lambda>r t. \<forall>s'. t = st s' \<longrightarrow> Q r s'\<rbrace> \<Longrightarrow> exec_abstract st f \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_exec_abstract_iff)

lemma runs_to_partial_exec_abstract[runs_to_vcg]:
  "f \<bullet> (st s) ?\<lbrace>\<lambda>r t. \<forall>s'. t = st s' \<longrightarrow> Q r s'\<rbrace> \<Longrightarrow> exec_abstract st f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: runs_to_partial.rep_eq run_exec_abstract split_beta' prod_eq_iff eq_commute)

lemma mono_exec_abstract: "f \<le> f' \<Longrightarrow> exec_abstract st f \<le> exec_abstract st f'"
  unfolding exec_abstract_def by (rule mono_lift_state)

lemma monotone_exec_abstract_le[partial_function_mono]:
  "monotone Q (\<le>) f \<Longrightarrow> monotone Q (\<le>) (\<lambda>f'. exec_abstract st (f f'))"
  by (simp add: monotone_def mono_exec_abstract)

lemma monotone_exec_abstract_ge[partial_function_mono]:
  "monotone Q (\<ge>) f \<Longrightarrow> monotone Q (\<ge>) (\<lambda>f'. exec_abstract st (f f'))"
  by (simp add: monotone_def mono_exec_abstract)

subsection \<open>\<^const>\<open>bind_exception_or_result\<close>\<close>

lemma runs_to_bind_exception_or_result_iff[runs_to_iff]:
  "bind_exception_or_result f g \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace> \<lambda>r t. g r \<bullet> t \<lbrace> Q \<rbrace>\<rbrace>"
  by transfer (simp add: split_beta')

lemma runs_to_bind_exception_or_result[runs_to_vcg]:
  "f \<bullet> s \<lbrace> \<lambda>r t. g r \<bullet> t \<lbrace> Q \<rbrace>\<rbrace> \<Longrightarrow> bind_exception_or_result f g \<bullet> s \<lbrace> Q \<rbrace>"
  by (auto simp: runs_to_bind_exception_or_result_iff)

lemma runs_to_partial_bind_exception_or_result[runs_to_vcg]:
  "f \<bullet> s ?\<lbrace> \<lambda>r t. g r \<bullet> t ?\<lbrace> Q \<rbrace>\<rbrace> \<Longrightarrow> bind_exception_or_result f g \<bullet> s ?\<lbrace> Q \<rbrace>"
  by transfer (simp add: split_beta' holds_partial_bind_post_state)

lemma refines_bind_exception_or_result:
  "refines f f' s s' (\<lambda>(r, t) (r', t'). refines (g r) (g' r') t t' R) \<Longrightarrow>
    refines (bind_exception_or_result f g) (bind_exception_or_result f' g') s s' R"
  by transfer (auto intro: sim_bind_post_state)

lemma refines_bind_exception_or_result':
  assumes f: "refines f f' s s' Q"
  assumes g: "\<And>r t r' t'. Q (r, t) (r', t') \<Longrightarrow> refines (g r) (g' r') t t' R"
  shows "refines (bind_exception_or_result f g) (bind_exception_or_result f' g') s s' R"
  by (auto intro: refines_bind_exception_or_result refines_mono[OF _ f] g)

lemma mono_bind_exception_or_result:
  "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> bind_exception_or_result f g \<le> bind_exception_or_result f' g'"
  unfolding le_fun_def
  by transfer (auto simp add: le_fun_def intro!: mono_bind_post_state)

lemma monotone_bind_exception_or_result_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>v. monotone R (\<le>) (\<lambda>f'. g f' v)) \<Longrightarrow>
    monotone R (\<le>) (\<lambda>f'. bind_exception_or_result (f f') (g f'))"
  by (simp add: monotone_def) (metis le_fun_def mono_bind_exception_or_result)

lemma monotone_bind_exception_or_result_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>v. monotone R (\<ge>) (\<lambda>f'. g f' v)) \<Longrightarrow>
    monotone R (\<ge>) (\<lambda>f'. bind_exception_or_result (f f') (g f'))"
  by (simp add: monotone_def) (metis le_fun_def mono_bind_exception_or_result)

lemma run_bind_exception_or_result_cong:
  assumes *: "run f s = run f' s"
  assumes **: "f \<bullet> s ?\<lbrace> \<lambda>x s'. run (g x) s' = run (g' x) s' \<rbrace>"
  shows "run (bind_exception_or_result f g) s = run (bind_exception_or_result f' g') s"
  using assms
  by (cases "run f' s")
     (auto simp: bind_exception_or_result_def runs_to_partial.rep_eq
           intro!: SUP_cong split: exception_or_result_splits)

subsection \<open>\<^const>\<open>bind_handle\<close>\<close>

lemma bind_handle_eq:
  "bind_handle f g h =
    bind_exception_or_result f (\<lambda>r. case r of Exception e \<Rightarrow> h e | Result v \<Rightarrow> g v)"
  unfolding spec_monad_ext_iff bind_handle.rep_eq bind_exception_or_result.rep_eq
  by (intro allI arg_cong[where f="bind_post_state _"] ext)
     (auto split: exception_or_result_split)

lemma runs_to_bind_handle_iff[runs_to_iff]:
  "bind_handle f g h \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace> \<lambda>r t.
    (\<forall>v. r = Result v \<longrightarrow> g v \<bullet> t \<lbrace> Q \<rbrace>) \<and>
    (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> h e \<bullet> t \<lbrace> Q \<rbrace>)\<rbrace>"
  by transfer
     (auto intro!: arg_cong[where f="\<lambda>p. holds_post_state p _"] simp: fun_eq_iff
           split: prod.splits exception_or_result_splits)

lemma runs_to_bind_handle[runs_to_vcg]:
  "f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> g v \<bullet> t \<lbrace> Q \<rbrace>) \<and>
                 (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> h e \<bullet> t \<lbrace> Q \<rbrace>)\<rbrace> \<Longrightarrow>
  bind_handle f g h \<bullet> s \<lbrace> Q \<rbrace>"
  by (auto simp: runs_to_bind_handle_iff)

lemma runs_to_bind_handle_exeption_monad[runs_to_vcg]:
  fixes f :: "('e, 'a, 's) exn_monad"
  assumes f:
    "f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> (g v \<bullet> t \<lbrace> Q \<rbrace>)) \<and>
                   (\<forall>e. r = Exception (Some e) \<longrightarrow> (h (Some e) \<bullet> t \<lbrace> Q \<rbrace>))\<rbrace>"
  shows "bind_handle f g h \<bullet> s \<lbrace> Q \<rbrace>"
  by (rule runs_to_bind_handle[OF runs_to_weaken[OF f]]) (auto simp: default_option_def)

lemma runs_to_bind_handle_res_monad[runs_to_vcg]:
  fixes f :: "('a, 's) res_monad"
  assumes f: "f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> (g v \<bullet> t \<lbrace> Q \<rbrace>))\<rbrace>"
  shows "bind_handle f g h \<bullet> s \<lbrace> Q \<rbrace>"
  by (rule runs_to_bind_handle[OF runs_to_weaken[OF f]]) (auto simp: default_option_def)

lemma runs_to_partial_bind_handle[runs_to_vcg]:
  "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> g v \<bullet> t ?\<lbrace> Q \<rbrace>) \<and>
                 (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> h e \<bullet> t ?\<lbrace> Q \<rbrace>)\<rbrace> \<Longrightarrow>
  bind_handle f g h \<bullet> s ?\<lbrace> Q \<rbrace>"
  by transfer
     (auto intro!: holds_partial_bind_post_stateI intro: holds_partial_post_state_weaken
           split: exception_or_result_splits prod.splits)

lemma runs_to_partial_bind_handle_exeption_monad[runs_to_vcg]:
  fixes f :: "('e, 'a, 's) exn_monad"
  assumes f: "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> (g v \<bullet> t ?\<lbrace> Q \<rbrace>)) \<and>
    (\<forall>e. r = Exception (Some e) \<longrightarrow> (h (Some e) \<bullet> t ?\<lbrace> Q \<rbrace>))\<rbrace>"
  shows "bind_handle f g h \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (rule runs_to_partial_bind_handle[OF runs_to_partial_weaken[OF f]])
     (auto simp: default_option_def)

lemma runs_to_partial_bind_handle_res_monad[runs_to_vcg]:
  fixes f :: "('a, 's) res_monad"
  assumes f: "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> (g v \<bullet> t ?\<lbrace> Q \<rbrace>))\<rbrace>"
  shows "bind_handle f g h \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (rule runs_to_partial_bind_handle[OF runs_to_partial_weaken[OF f]])
     (auto simp: default_option_def)

lemma mono_bind_handle:
  "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> h \<le> h' \<Longrightarrow> bind_handle f g h \<le> bind_handle f' g' h'"
  unfolding le_fun_def
  by transfer
     (auto simp add: le_fun_def intro!: mono_bind_post_state split: exception_or_result_splits)

lemma monotone_bind_handle_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>v. monotone R (\<le>) (\<lambda>f'. g f' v)) \<Longrightarrow>
    (\<And>e. monotone R (\<le>) (\<lambda>f'. h f' e)) \<Longrightarrow>
    monotone R (\<le>) (\<lambda>f'. bind_handle (f f') (g f') (h f'))"
  by (simp add: monotone_def) (metis le_fun_def mono_bind_handle)

lemma monotone_bind_handle_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>v. monotone R (\<ge>) (\<lambda>f'. g f' v)) \<Longrightarrow>
    (\<And>e. monotone R (\<ge>) (\<lambda>f'. h f' e)) \<Longrightarrow>
    monotone R (\<ge>) (\<lambda>f'. bind_handle (f f') (g f') (h f'))"
  by (simp add: monotone_def) (metis le_fun_def mono_bind_handle)

lemma run_bind_handle[run_spec_monad]:
  "run (bind_handle f g h) s = bind_post_state (run f s)
    (\<lambda>(r, t). case r of Exception e \<Rightarrow> run (h e) t | Result v \<Rightarrow> run (g v) t)"
  by transfer simp

lemma always_progress_bind_handle[always_progress_intros]:
  "always_progress f \<Longrightarrow> (\<And>v. always_progress (g v)) \<Longrightarrow> (\<And>e. always_progress (h e))
  \<Longrightarrow>  always_progress (bind_handle f g h)"
  by (auto simp: always_progress.rep_eq run_bind_handle bind_post_state_eq_bot prod_eq_iff
                 exception_or_result_nchotomy holds_post_state_False
           split: exception_or_result_splits prod.splits)

lemma refines_bind_handle':
  "refines f f' s s' (\<lambda>(r, t) (r', t').
    (\<forall>e e'. e \<noteq> default \<longrightarrow> e' \<noteq> default \<longrightarrow> r = Exception e \<longrightarrow> r' = Exception e' \<longrightarrow>
      refines (h e) (h' e') t t' R) \<and>
    (\<forall>e x'. e \<noteq> default \<longrightarrow> r = Exception e \<longrightarrow> r' = Result x' \<longrightarrow>
      refines (h e) (g' x') t t' R) \<and>
    (\<forall>x e'. e' \<noteq> default \<longrightarrow> r = Result x \<longrightarrow> r' = Exception e' \<longrightarrow>
      refines (g x) (h' e') t t' R) \<and>
    (\<forall>x x'. r = Result x \<longrightarrow> r' = Result x' \<longrightarrow>
      refines (g x) (g' x') t t' R)) \<Longrightarrow>
  refines (bind_handle f g h) (bind_handle f' g' h') s s' R"
  apply transfer
  apply (auto intro!: sim_bind_post_state')[1]
  apply (rule sim_post_state_weaken, assumption)
  apply (auto split: exception_or_result_splits prod.splits)
  done

lemma refines_bind_handle_bind_handle:
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'. Q (Exception e, t) (Exception e', t') \<Longrightarrow>
    e \<noteq> default \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    refines (h e) (h' e') t t' R"
  assumes lr: "\<And>e v' t t'. Q (Exception e, t) (Result v', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow>
    refines (h e) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exception e', t') \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    refines (g v) (h' e') t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    refines (g v) (g' v') t t' R"
  shows "refines (bind_handle f g h) (bind_handle f' g' h') s s' R"
  apply (rule refines_bind_handle')
  apply (rule refines_weaken[OF f])
  apply (auto split: exception_or_result_splits prod.splits intro: ll lr rl rr)
  done

lemma refines_bind_handle_bind_handle_exn:
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'. Q (Exn e, t) (Exn e', t') \<Longrightarrow>
    refines (h (Some e)) (h' (Some e')) t t' R"
  assumes lr: "\<And>e v' t t'. Q (Exn e, t) (Result v', t') \<Longrightarrow>
    refines (h (Some e)) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exn e', t') \<Longrightarrow>
    refines (g v) (h' (Some e')) t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    refines (g v) (g' v') t t' R"
  shows "refines (bind_handle f g h) (bind_handle f' g' h') s s' R"
  apply (rule refines_bind_handle')
  apply (rule refines_weaken[OF f])
  using ll lr rl rr
  apply (auto split: exception_or_result_splits prod.splits simp: Exn_def default_option_def)
  done

lemma bind_handle_return_spec_monad[simp]: "bind_handle (return v) g h = g v"
  by transfer simp

lemma bind_handle_throw_spec_monad[simp]:
  "v \<noteq> default \<Longrightarrow> bind_handle (throw_exception_or_result v) g h = h v"
  by transfer simp

lemma bind_handle_bind_handle_spec_monad:
  "bind_handle (bind_handle f g1 h1) g2 h2 =
    bind_handle f
      (\<lambda>v. bind_handle (g1 v) g2 h2)
      (\<lambda>e. bind_handle (h1 e) g2 h2)"
  apply transfer
  apply (auto simp: fun_eq_iff intro!: arg_cong[where f="bind_post_state _"])[1]
  subgoal for g1 h1 g2 h2 r v by (cases r) simp_all
  done

lemma mono_bind_handle_spec_monad:
  "mono f \<Longrightarrow> (\<And>v. mono (\<lambda>x. g x v)) \<Longrightarrow> (\<And>e. mono (\<lambda>x. h x e)) \<Longrightarrow>
    mono (\<lambda>x. bind_handle (f x) (g x) (h x))"
  unfolding mono_def
  apply transfer
  apply (auto simp: le_fun_def intro!: mono_bind_post_state)[1]
  subgoal for f g h x y r q by (cases r) simp_all
  done

lemma rel_spec_bind_handle:
  "rel_spec f f' s s' (\<lambda>(r, t) (r', t').
    (\<forall>e e'. e \<noteq> default \<longrightarrow> e' \<noteq> default \<longrightarrow> r = Exception e \<longrightarrow> r' = Exception e' \<longrightarrow>
      rel_spec (h e) (h' e') t t' R) \<and>
    (\<forall>e x'. e \<noteq> default \<longrightarrow> r = Exception e \<longrightarrow> r' = Result x' \<longrightarrow>
      rel_spec (h e) (g' x') t t' R) \<and>
    (\<forall>x e'. e' \<noteq> default \<longrightarrow> r = Result x \<longrightarrow> r' = Exception e' \<longrightarrow>
      rel_spec (g x) (h' e') t t' R) \<and>
    (\<forall>x x'. r = Result x \<longrightarrow> r' = Result x' \<longrightarrow>
      rel_spec (g x) (g' x') t t' R)) \<Longrightarrow>
  rel_spec (bind_handle f g h) (bind_handle f' g' h') s s' R"
  by (auto simp: rel_spec_iff_refines intro!: refines_bind_handle' intro: refines_weaken)

lemma bind_finally_bind_handle_conv: "bind_finally f g = bind_handle f (\<lambda>v. g (Result v)) (\<lambda>e. g (Exception e))"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff Exn_def [symmetric] default_option_def elim!: runs_to_weaken)[1]
  using exception_or_result_nchotomy by force

subsection \<open>\<^const>\<open>bind\<close>\<close>

lemma run_bind[run_spec_monad]: "run (bind f g) s =
    bind_post_state (run f s) (\<lambda>(r, t). case r of
      Exception e \<Rightarrow> pure_post_state (Exception e, t)
    | Result v \<Rightarrow> run (g v) t)"
  by (auto simp add: bind_def run_bind_handle )

lemma run_bind_eq_top_iff:
  "run (bind f g) s = \<top> \<longleftrightarrow> \<not> (f \<bullet> s \<lbrace> \<lambda>x s. \<forall>a. x = Result a \<longrightarrow> run (g a) s \<noteq> \<top> \<rbrace>)"
  by (simp add: run_bind bind_post_state_eq_top runs_to.rep_eq prod_eq_iff split_beta'
           split: exception_or_result_splits prod.splits)

lemma always_progress_bind[always_progress_intros]:
  "always_progress f \<Longrightarrow> (\<And>v. always_progress (g v)) \<Longrightarrow> always_progress (bind f g)"
  by (simp add: always_progress_intros bind_def)

lemma run_bind_cong:
  assumes *: "run f s = run f' s"
  assumes **: "f \<bullet> s ?\<lbrace> \<lambda>x s'. \<forall>v. x = (Result v) \<longrightarrow> run (g v) s' = run (g' v) s' \<rbrace>"
  shows "run (bind f g) s = run (bind f' g') s"
  using assms
  by (cases "run f' s")
     (auto simp: run_bind runs_to_partial.rep_eq
           intro!: SUP_cong split: exception_or_result_splits)

lemma runs_to_bind_iff[runs_to_iff]:
  "bind f g \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace> \<lambda>r t.
    (\<forall>v. r = Result v \<longrightarrow> g v \<bullet> t \<lbrace> Q \<rbrace>) \<and>
    (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> Q (Exception e) t)\<rbrace>"
  by (simp add: bind_def runs_to_bind_handle_iff)

lemma runs_to_bind[runs_to_vcg]:
  "f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> g v \<bullet> t \<lbrace> Q \<rbrace>) \<and>
                 (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> Q (Exception e) t)\<rbrace> \<Longrightarrow>
      bind f g \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_bind_iff)

lemma runs_to_bind_exception[runs_to_vcg]:
  fixes f :: "('e, 'a, 's) exn_monad"
  assumes [runs_to_vcg]: "f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> g v \<bullet> t \<lbrace> Q \<rbrace>) \<and>
                 (\<forall>e. r = Exn e \<longrightarrow> Q (Exn e) t)\<rbrace>"
  shows "bind f g \<bullet> s \<lbrace> Q \<rbrace>"
  supply runs_to_bind[runs_to_vcg]
  by runs_to_vcg (auto simp: Exn_def default_option_def)

lemma runs_to_bind_res[runs_to_vcg]:
  fixes f :: "('a, 's) res_monad"
  assumes [runs_to_vcg]: "f \<bullet> s \<lbrace> \<lambda>Res v t. g v \<bullet> t \<lbrace> Q \<rbrace>\<rbrace>"
  shows "bind f g \<bullet> s \<lbrace> Q \<rbrace>"
  supply runs_to_bind[runs_to_vcg]
  by runs_to_vcg

lemma runs_to_partial_bind[runs_to_vcg]:
  "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> g v \<bullet> t ?\<lbrace> Q \<rbrace>) \<and>
                 (\<forall>e. r = Exception e \<longrightarrow> e \<noteq> default \<longrightarrow> Q (Exception e) t)\<rbrace> \<Longrightarrow>
      bind f g \<bullet> s ?\<lbrace> Q \<rbrace>"
  apply (simp add: bind_def)
  apply (rule runs_to_partial_bind_handle)
  apply simp
  done

lemma runs_to_partial_bind_exeption_monad[runs_to_vcg]:
  fixes f :: "('e, 'a, 's) exn_monad"
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> g v \<bullet> t ?\<lbrace> Q \<rbrace>) \<and>
    (\<forall>e. r = Exn e \<longrightarrow> Q (Exn e) t)\<rbrace>"
  shows "bind f g \<bullet> s ?\<lbrace> Q \<rbrace>"
  by runs_to_vcg (auto simp add: default_option_def Exn_def)

lemma runs_to_partial_bind_res_monad[runs_to_vcg]:
  fixes f :: "('a, 's) res_monad"
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace> \<lambda>Res v t. g v \<bullet> t ?\<lbrace> Q \<rbrace>\<rbrace>"
  shows "bind f g \<bullet> s ?\<lbrace> Q \<rbrace>"
  by runs_to_vcg

lemma bind_return[simp]: "(bind m return) = m"
  apply (clarsimp simp: spec_monad_eq_iff runs_to_bind_iff fun_eq_iff
                  intro!: runs_to_cong_pred_only)
  subgoal for P r t
    by (cases r) auto
  done

lemma bind_skip[simp]: "bind m (\<lambda>x. skip) = m"
  using bind_return[of m] by simp

lemma return_bind[simp]: "bind (return x) f = f x"
  unfolding bind_def by transfer simp

lemma bind_assoc: "bind (bind f g) h = bind f (\<lambda>x. bind (g x) h)"
  apply (rule spec_monad_ext)
  apply (auto simp: split_beta' run_bind intro!: arg_cong[where f="bind_post_state _"]
              split: exception_or_result_splits)
  done

lemma mono_bind: "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> bind f g \<le> bind f' g'"
  unfolding bind_def
  by (auto intro: mono_bind_handle)

lemma mono_bind_spec_monad:
  "mono f \<Longrightarrow> (\<And>v. mono (\<lambda>x. g x v)) \<Longrightarrow> mono (\<lambda>x. bind (f x) (g x))"
  unfolding bind_def
  by (intro mono_bind_handle_spec_monad mono_const) auto

lemma monotone_bind_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>v. monotone R (\<le>) (\<lambda>f'. g f' v))
  \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. bind (f f') (g f'))"
  unfolding bind_def
  by (auto intro: monotone_bind_handle_le)

lemma monotone_bind_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>v. monotone R (\<ge>) (\<lambda>f'. g f' v))
  \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. bind (f f') (g f'))"
  unfolding bind_def
  by (auto intro: monotone_bind_handle_ge)

lemma refines_bind':
  assumes f: "refines f f' s s' (\<lambda>(x, t) (x', t').
    (\<forall>e. e \<noteq> default \<longrightarrow> x = Exception e \<longrightarrow>
      ((\<forall>e'. e' \<noteq> default \<longrightarrow> x' = Exception e' \<longrightarrow> R (Exception e, t) (Exception e', t')) \<and>
      (\<forall>v'. x' = Result v' \<longrightarrow> refines (throw_exception_or_result e) (g' v') t t' R))) \<and>
    (\<forall>v. x = Result v \<longrightarrow>
      ((\<forall>e'. e' \<noteq> default \<longrightarrow> x' = Exception e' \<longrightarrow>
        refines (g v) (throw_exception_or_result e') t t' R) \<and>
      (\<forall>v'. x' = Result v' \<longrightarrow> refines (g v) (g' v') t t' R))))"
  shows "refines (bind f g) (bind f' g') s s' R"
  unfolding bind_def
  by (rule refines_bind_handle'[OF refines_weaken, OF f]) auto

lemma refines_bind:
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'.
    Q (Exception e, t) (Exception e', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    R (Exception e, t) (Exception e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exception e, t) (Result v', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow>
    refines (yield (Exception e)) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exception e', t') \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    refines (g v) (yield (Exception e')) t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    refines (g v) (g' v') t t' R"
  shows "refines (bind f g) (bind f' g') s s' R"
  by (rule refines_bind'[OF refines_weaken[OF f]])
     (auto simp: ll lr rl rr)

lemma refines_bind_bind_exn:
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'. Q (Exn e, t) (Exn e', t') \<Longrightarrow> R (Exn e, t) (Exn e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exn e, t) (Result v', t') \<Longrightarrow> refines (throw e) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exn e', t') \<Longrightarrow> refines (g v) (throw e') t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow> refines (g v) (g' v') t t' R"
  shows "refines (f \<bind> g) (f' \<bind> g') s s' R"
  using ll lr rl rr
  by (intro refines_bind[OF f])
     (auto simp: Exn_def default_option_def)

lemma refines_bind_res:
  assumes f: "refines f f' s s' (\<lambda>(Res r, t) (Res r', t'). refines (g r) (g' r') t t' R) "
  shows "refines ((bind f g)::('a,'s) res_monad) ((bind f' g')::('b, 't) res_monad) s s' R"
  by (rule refines_bind[OF f]) auto

lemma refines_bind_res':
  assumes f: "refines f f' s s' Q"
  assumes g: "\<And>r t r' t'. Q (Result r, t) (Result r', t') \<Longrightarrow> refines (g r) (g' r') t t' R"
  shows "refines ((bind f g)::('a,'s) res_monad) ((bind f' g')::('b, 't) res_monad) s s' R"
  by (auto intro!: refines_bind_res refines_weaken[OF f] g)

lemma refines_bind_bind_exn_wp: 
  assumes f: "refines f f' s s' (\<lambda>(r, t) (r',t'). 
     (case r of 
        Exn e \<Rightarrow> (case r' of Exn e' \<Rightarrow> R (Exn e, t) (Exn e', t') | Result v' \<Rightarrow> refines (throw e) (g' v') t t' R)
      | Result v \<Rightarrow> (case r' of Exn e' \<Rightarrow> refines (g v) (throw e') t t' R | Result v' \<Rightarrow> refines (g v) (g' v') t t' R)))"
   shows "refines (f \<bind> g) (f' \<bind> g') s s' R"
  apply (rule refines_bind')
  apply (rule refines_weaken [OF f])
  apply (auto simp add: Exn_def default_option_def split: xval_splits )
  done

lemma rel_spec_bind_res:
  "rel_spec f f' s s' (\<lambda>(Res r, t) (Res r', t'). rel_spec (g r) (g' r') t t' R) \<Longrightarrow>
    rel_spec ((bind f g)::('a,'s) res_monad) ((bind f' g')::('b, 't) res_monad) s s' R"
  unfolding rel_spec_iff_refines
  by (safe intro!: refines_bind_res; (rule refines_weaken, assumption, simp))

lemma rel_spec_bind_res':
  assumes f: "rel_spec f f' s s' Q"
  assumes g: "\<And>r t r' t'. Q (Result r, t) (Result r', t') \<Longrightarrow> rel_spec (g r) (g' r') t t' R"
  shows "rel_spec ((bind f g)::('a,'s) res_monad) ((bind f' g')::('b, 't) res_monad) s s' R"
  by (auto intro!: rel_spec_bind_res rel_spec_mono[OF _ f] g)

lemma rel_spec_bind_bind:
  assumes f: "rel_spec f f' s s' Q"
  assumes ll: "\<And>e e' t t'.
    Q (Exception e, t) (Exception e', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    R (Exception e, t) (Exception e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exception e, t) (Result v', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow>
    rel_spec (yield (Exception e)) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exception e', t') \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    rel_spec (g v) (yield (Exception e')) t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    rel_spec (g v) (g' v') t t' R"
  shows "rel_spec (bind f g) (bind f' g') s s' R"
  using assms unfolding rel_spec_iff_refines
  apply (intro conjI)
  subgoal by (rule refines_bind[where Q=Q]) auto
  subgoal by (rule refines_bind[where Q="Q\<inverse>\<inverse>"]) auto
  done

lemma rel_spec_bind_exn:
  assumes f: "rel_spec f f' s s' Q"
  assumes ll: "\<And>e e' t t'. Q (Exn e, t) (Exn e', t') \<Longrightarrow> R (Exn e, t) (Exn e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exn e, t) (Result v', t') \<Longrightarrow> rel_spec (throw e) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exn e', t') \<Longrightarrow> rel_spec (g v) (throw e') t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow> rel_spec (g v) (g' v') t t' R"
  shows "rel_spec (bind f g) (bind f' g') s s' R"
  using ll lr rl rr
  by (intro rel_spec_bind_bind[OF f])
     (auto simp: Exn_def default_option_def)

lemma refines_bind_right:
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'.
    Q (Exception e, t) (Exception e', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    R (Exception e, t) (Exception e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exception e, t) (Result v', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow>
    refines (yield (Exception e)) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exception e', t') \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    R (Result v, t) (Exception e', t')"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    refines (return v) (g' v') t t' R"
  shows "refines f (bind f' g') s s' R"
proof -
  have "refines (bind f return) (bind f' g') s s' R"
    using ll lr rl rr by (intro refines_bind[OF f]) auto
  then show ?thesis by simp
qed

lemma refines_bind_left:
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'.
    Q (Exception e, t) (Exception e', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    R (Exception e, t) (Exception e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exception e, t) (Result v', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow>
    R (Exception e, t) (Result v', t')"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exception e', t') \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    refines (g v) (yield (Exception e')) t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    refines (g v) (return v') t t' R"
  shows "refines (bind f g) f' s s' R"
proof -
  have "refines (bind f g) (bind f' return) s s' R"
    using ll lr rl rr by (intro refines_bind[OF f]) auto
  then show ?thesis by simp
qed

lemma rel_spec_bind_right:
  assumes f: "rel_spec f f' s s' Q"
  assumes ll: "\<And>e e' t t'.
    Q (Exception e, t) (Exception e', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    R (Exception e, t) (Exception e', t')"
  assumes lr: "\<And>e v' t t'. Q (Exception e, t) (Result v', t') \<Longrightarrow> e \<noteq> default \<Longrightarrow>
    rel_spec (yield (Exception e)) (g' v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exception e', t') \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
    R (Result v, t) (Exception e', t')"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    rel_spec (return v) (g' v') t t' R"
  shows "rel_spec f (bind f' g') s s' R"
  using assms unfolding rel_spec_iff_refines
  apply (intro conjI)
  subgoal by (rule refines_bind_right[where Q=Q]) auto
  subgoal by (rule refines_bind_left[where Q ="Q\<inverse>\<inverse>"]) auto
  done

lemma refines_bind_handle_left':
  "f \<bullet> s \<lbrace> \<lambda>v s'. (\<forall>r. v = Result r \<longrightarrow> refines (g r) k s' t R) \<and>
    (\<forall>e. e \<noteq> default \<longrightarrow> v = Exception e \<longrightarrow> refines (h e) k s' t R) \<rbrace> \<Longrightarrow>
  refines (bind_handle f g h) k s t R"
  by (auto simp: runs_to.rep_eq refines.rep_eq run_bind_handle split_beta' ac_simps
           intro!: sim_bind_post_state_left split: prod.splits exception_or_result_splits)

lemma refines_bind_left_res:
  "f \<bullet> s \<lbrace> \<lambda>Res r s'. refines (g r) h s' t R \<rbrace> \<Longrightarrow> refines (f >>= g) h s t R"
  unfolding bind_def by (rule refines_bind_handle_left') simp

lemma refines_bind_left_exn:
  "f \<bullet> s \<lbrace> \<lambda>r s'. (\<forall>a. r = Result a \<longrightarrow> refines (g a) h s' t R) \<and>
    (\<forall>e. r = Exn e \<longrightarrow> refines (throw e) h s' t R) \<rbrace> \<Longrightarrow>
    refines (f >>= g) h s t R"
  unfolding bind_def
  by (rule refines_bind_handle_left')
     (auto simp add: Exn_def default_option_def imp_ex)

lemma runs_to_partial_bind1:
  "(\<And>r s. (g r) \<bullet> s ?\<lbrace>P\<rbrace>) \<Longrightarrow> ((f >>= g)::('a, 's) res_monad) \<bullet> s ?\<lbrace>P\<rbrace>"
  apply (rule runs_to_partial_bind)
  apply (rule runs_to_partial_weaken[OF runs_to_partial_True])
  apply auto
  done

lemma unknown_bind_const[simp]: "unknown >>= (\<lambda>x. f) = f"
  by (rule spec_monad_ext) (simp add: run_bind)

lemma bind_cong_left:
  fixes f::"('e::default, 'a, 's) spec_monad"
  shows "(\<And>r. g r = g' r) \<Longrightarrow> (f >>= g) = (f >>= g')"
  by (rule spec_monad_ext) (simp add: run_bind)

lemma bind_cong_right:
  fixes f::"('e::default, 'a, 's) spec_monad"
  shows "f = f' \<Longrightarrow> (f >>= g) = (f' >>= g)"
  by (rule spec_monad_ext) (simp add: run_bind)

lemma rel_spec_bind_res'':
  fixes f::"('a, 's) res_monad"
  shows "f \<bullet> s ?\<lbrace> \<lambda>Res r t. rel_spec (g r) (g' r) t t R\<rbrace> \<Longrightarrow> rel_spec (f >>= g) (f >>= g') s s R"
  by (intro rel_spec_bind_res rel_spec_refl') (auto simp: split_beta')

lemma rel_spec_monad_bind_rel_exception_or_result:
  assumes mn: "rel_spec_monad R (rel_exception_or_result E P) m n"
    and fg: "rel_fun P (rel_spec_monad R (rel_exception_or_result E Q)) f g"
  shows "rel_spec_monad R (rel_exception_or_result E Q) (m >>= f) (n >>= g)"
  by (intro rel_spec_monadI rel_spec_bind_bind[OF rel_spec_monadD[OF mn]])
     (simp_all add: fg[THEN rel_funD, THEN rel_spec_monadD])

lemma rel_spec_monad_bind_rel_exception_or_result':
  "(\<And>x. rel_spec_monad (=) (rel_exception_or_result (=) Q) (f x) (g x)) \<Longrightarrow>
    rel_spec_monad (=) (rel_exception_or_result (=) Q) (m >>= f) (m >>= g)"
  apply (rule rel_spec_monad_bind_rel_exception_or_result[where P="(=)"])
  apply (auto simp add: rel_exception_or_result_eq_conv rel_spec_monad_eq_conv)
  done

lemma rel_spec_monad_bind:
  "rel_spec_monad R (\<lambda>Res v1 Res v2. P v1 v2) m n \<Longrightarrow> rel_fun P (rel_spec_monad R Q) f g \<Longrightarrow>
    rel_spec_monad R Q (m >>= f) (n >>= g)"
  apply (clarsimp simp add: rel_spec_monad_iff_rel_spec[abs_def] rel_fun_def
                  intro!: rel_spec_bind_res)
  subgoal premises prems for s t
    by (rule rel_spec_mono[OF _ prems(1)[rule_format, OF prems(3)]])
       (clarsimp simp: le_fun_def prems(2)[rule_format])
  done

lemma rel_spec_monad_bind_left:
  assumes mn: "rel_spec_monad R (\<lambda>Res v1 Res v2. P v1 v2) m n"
    and fg: "rel_fun P (rel_spec_monad R Q) f return"
  shows "rel_spec_monad R Q (m >>= f) n"
proof -
  from mn fg
  have "rel_spec_monad R Q (m >>= f) (n >>= return)"
    by (rule rel_spec_monad_bind)
  then show ?thesis
    by (simp)
qed

lemma rel_spec_monad_bind':
  fixes m:: "('a, 's) res_monad"
  shows "(\<And>x. rel_spec_monad (=) Q (f x) (g x)) \<Longrightarrow> rel_spec_monad (=) Q (m >>= f) (m >>= g)"
  by (rule rel_spec_monad_bind[where R="(=)" and P="(=)"])
     (auto simp: rel_fun_def rel_spec_monad_iff_rel_spec intro!: rel_spec_refl)

lemma run_bind_cong_simple:
  "run f s = run f' s \<Longrightarrow> (\<And>v s. run (g v) s = run (g' v) s) \<Longrightarrow>
    run (bind f g) s = run (bind f' g') s"
  by (simp add: run_bind)

lemma run_bind_cong_simple_same_head:  "(\<And>v s. run (g v) s = run (g' v) s) \<Longrightarrow>
  run (bind f g) s = run (bind f g') s"
  by (rule run_bind_cong_simple) auto

lemma refines_bind_same:
  "refines (f >>= g) (f >>= g') s s R" if "f \<bullet> s \<lbrace>\<lambda>Res y t. refines (g y) (g' y) t t R \<rbrace>"
  apply (rule refines_bind_res)
  apply (rule refines_same_runs_toI)
  apply (rule runs_to_weaken[OF that])
  apply auto
  done

lemma refines_bind_handle_right_runs_to_partialI:
  "g \<bullet> t ?\<lbrace> \<lambda>r t'. (\<forall>e. e \<noteq> default \<longrightarrow> r = Exception e \<longrightarrow> refines f (k e) s t' R) \<and>
     (\<forall>a. r = Result a \<longrightarrow> refines f (h a) s t' R) \<rbrace> \<Longrightarrow> always_progress g \<Longrightarrow>
  refines f (bind_handle g h k) s t R"
  by transfer
     (auto simp: prod_eq_iff split_beta'
           intro!: sim_bind_post_state_right
           split: exception_or_result_splits prod.splits)

lemma refines_bind_right_runs_to_partialI:
  "g \<bullet> t ?\<lbrace> \<lambda>r t'. (\<forall>e. e \<noteq> default \<longrightarrow> r = Exception e \<longrightarrow>
      refines f (throw_exception_or_result e) s t' R) \<and>
     (\<forall>a. r = Result a \<longrightarrow> refines f (h a) s t' R) \<rbrace> \<Longrightarrow> always_progress g \<Longrightarrow>
  refines f (bind g h) s t R"
  unfolding bind_def by (rule refines_bind_handle_right_runs_to_partialI)

lemma refines_bind_right_runs_toI:
  "g \<bullet> t \<lbrace> \<lambda>Res r t'. refines f (h r) s t' R \<rbrace> \<Longrightarrow> always_progress g \<Longrightarrow>
    refines f (g >>= h) s t R"
  unfolding bind_def
  by (rule refines_bind_handle_right_runs_to_partialI)
     (auto intro: runs_to_partial_of_runs_to)

lemma refines_bind_left_refine:
  "refines (f >>= g) h s t R"
  if "refines f f' s s (=)" "refines (f' >>= g) h s t R"
  by (rule refines_trans[OF refines_bind[OF that(1)] that(2), where R="(=)"])
     (auto simp add: refines_refl)

lemma refines_bind_right_single:
  assumes x: "pure_post_state (Result x, u) \<le> run g t" and h: "refines f (h x) s u R"
  shows "refines f (g \<bind> h) s t R"
  apply (rule refines_le_run_trans[OF h])
  apply (simp add: run_bind)
  apply (rule order_trans[OF _ mono_bind_post_state, OF _ x order_refl])
  apply simp
  done

lemma return_let_bind: " (return (let v = f' in (g' v))) = do {v <- return f'; return (g' v)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma rel_spec_monad_rel_xval_bind:
  assumes f_f': "rel_spec_monad S (rel_xval L P) f f'"
  assumes Res_Res: "\<And>v v'. P v v' \<Longrightarrow> rel_spec_monad S (rel_xval L R) (g v) (g' v')"
  shows "rel_spec_monad S (rel_xval L R) (f \<bind> g) (f' \<bind> g')"
  apply (intro rel_spec_monadI rel_spec_bind_exn)
  apply (rule f_f'[THEN rel_spec_monadD], assumption)
  using Res_Res[THEN rel_spec_monadD]
  apply auto
  done

lemma rel_spec_monad_rel_xval_same_bind:
  assumes f_f': "rel_spec_monad S (rel_xval L R) f f'"
  assumes Res_Res: "\<And>v v'. R v v' \<Longrightarrow>  rel_spec_monad S (rel_xval L R) (g v) (g' v')"
  shows "rel_spec_monad S (rel_xval L R) (f \<bind> g) (f' \<bind> g')"
  using assms by (rule rel_spec_monad_rel_xval_bind)

lemma rel_spec_monad_rel_xval_result_eq_bind:
  assumes f_f': "rel_spec_monad S (rel_xval L (=)) f f'"
  assumes Res_Res: "\<And>v. rel_spec_monad S (rel_xval L (=)) (g v) (g' v)"
  shows "rel_spec_monad S (rel_xval L (=)) (f \<bind> g) (f' \<bind> g')"
  apply (rule rel_spec_monad_rel_xval_bind [OF f_f'])
  subgoal using Res_Res by auto
  done

lemma rel_spec_monad_fail: "rel_spec_monad Q R fail fail"
  by (auto simp add: rel_spec_monad_def rel_set_def)

lemma bind_fail[simp]: "fail \<bind> X = fail"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind)
  done

subsection \<open>\<^const>\<open>assert\<close>\<close>

lemma assert_simps[simp]:
  "assert True = return ()"
  "assert False = top"
   by (auto simp add: assert_def)

lemma always_progress_assert[always_progress_intros]: "always_progress (assert P)"
  by (simp add: always_progress_def assert_def)

lemma run_assert[run_spec_monad]:
  "run (assert P) s = (if P then pure_post_state (Result (), s) else \<top>)"
  by (simp add: assert_def)

lemma runs_to_assert_iff[simp]: "assert P \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> P \<and> Q (Result ()) s"
  by (simp add: runs_to.rep_eq run_assert)

lemma runs_to_assert[runs_to_vcg]: "P \<Longrightarrow> Q (Result ()) s \<Longrightarrow> assert P \<bullet> s \<lbrace> Q \<rbrace>"
  by simp

lemma runs_to_partial_assert_iff[simp]: "assert P \<bullet> s ?\<lbrace> Q \<rbrace> \<longleftrightarrow> (P \<longrightarrow> Q (Result ()) s)"
  by (simp add: runs_to_partial.rep_eq run_assert)

lemma refines_top_iff[simp]: "refines \<top> g s t R \<longleftrightarrow> run g t = \<top>"
  by transfer auto

lemma refines_assert: 
  "refines (assert P) (assert Q) s t R \<longleftrightarrow> (Q \<longrightarrow> P \<and> R (Result (), s) (Result (), t))"
  by (simp add: assert_def)

subsection "\<^const>\<open>assume\<close>"

lemma assume_simps[simp]:
  "assume True = return ()"
  "assume False = bot"
   by (auto simp add: assume_def)

lemma always_progress_assume[always_progress_intros]: "P \<Longrightarrow> always_progress (assume P)"
  by (simp add: always_progress_def assume_def)

lemma run_assume[run_spec_monad]:
  "run (assume P) s = (if P then pure_post_state (Result (), s) else \<bottom>)"
  by (simp add: assume_def)

lemma run_assume_simps[run_spec_monad, simp]:
  "P \<Longrightarrow> run (assume P) s = pure_post_state (Result (), s)"
  "\<not> P \<Longrightarrow> run (assume P) s = \<bottom>"
  by (simp_all add: run_assume)

lemma runs_to_assume_iff[simp]: "assume P \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (P \<longrightarrow> Q (Result ()) s)"
  by (simp add: runs_to.rep_eq run_assume)

lemma runs_to_partial_assume_iff[simp]: "assume P \<bullet> s ?\<lbrace> Q \<rbrace> \<longleftrightarrow> (P \<longrightarrow> Q (Result ()) s)"
  by (simp add: runs_to_partial.rep_eq run_assume)

lemma runs_to_assume[runs_to_vcg]: "(P \<Longrightarrow> Q (Result ()) s) \<Longrightarrow> assume P \<bullet> s \<lbrace> Q \<rbrace>"
  by simp

subsection \<open>\<^const>\<open>assume_outcome\<close>\<close>

lemma run_assume_outcome[run_spec_monad, simp]: "run (assume_outcome f) s = Success (f s)"
  apply transfer
  apply simp
  done

lemma always_progress_assume_outcome[always_progress_intros]:
  "(\<And>s. f s \<noteq> {}) \<Longrightarrow> always_progress (assume_outcome f)"
  by (auto simp add: always_progress_def bot_post_state_def)

lemma runs_to_assume_outcome[runs_to_vcg]:
  "(assume_outcome f) \<bullet> s \<lbrace>\<lambda>r t. (r, t) \<in> f s\<rbrace>"
  by (simp add: runs_to.rep_eq)

lemma runs_to_assume_outcome_iff[runs_to_iff]:
  "(assume_outcome f) \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (\<forall>(r, t) \<in> f s. Q r t)"
  by (auto simp add: runs_to.rep_eq)

lemma runs_to_partial_assume_outcome[runs_to_vcg]:
  "(assume_outcome f) \<bullet> s ?\<lbrace>\<lambda>r t. (r, t) \<in> f s\<rbrace>"
  by (simp add: runs_to_partial.rep_eq)

lemma assume_outcome_elementary:
  "assume_outcome f = do {s \<leftarrow> get_state; (r, t) \<leftarrow> select (f s); set_state t; yield r}"
  apply (rule spec_monad_ext)
  apply (simp add: run_bind Sup_Success pure_post_state_def)
  done

subsection \<open>\<^const>\<open>assume_result_and_state\<close>\<close>

lemma run_assume_result_and_state[run_spec_monad, simp]:
  "run (assume_result_and_state f) s = Success ((\<lambda>(v, t). (Result v, t)) `  f s)"
  by (auto simp add: assume_result_and_state_def run_bind Sup_Success_pair pure_post_state_def)

lemma always_progress_assume_result_and_state[always_progress_intros]:
  "(\<And>s. f s \<noteq> {}) \<Longrightarrow> always_progress (assume_result_and_state f)"
  by (simp add: always_progress_def)

lemma runs_to_assume_result_and_state[runs_to_vcg]:
  "assume_result_and_state f \<bullet> s \<lbrace>\<lambda>r t. \<exists>v. r = Result v \<and> (v, t) \<in> f s\<rbrace>"
  by (auto simp add: runs_to.rep_eq)

lemma runs_to_assume_result_and_state_iff[runs_to_iff]:
  "assume_result_and_state f \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (\<forall>(v, t) \<in> f s. Q (Result v) t)"
  by (auto simp add: runs_to.rep_eq)

lemma runs_to_partial_assume_result_and_state[runs_to_vcg]:
  "assume_result_and_state f \<bullet> s ?\<lbrace>\<lambda>r t. \<exists>v. r = Result v \<and> (v, t) \<in> f s\<rbrace>"
  by (auto simp add: runs_to_partial.rep_eq)

lemma refines_assume_result_and_state_right:
  "f \<bullet> s \<lbrace>\<lambda>r s'. \<exists>r' t'.  (r', t') \<in> g t \<and> R (r, s') (Result r', t') \<rbrace> \<Longrightarrow>
  refines f (assume_result_and_state g) s t R"
  by (simp add: refines.rep_eq runs_to.rep_eq sim_post_state_Success2 split_beta' Bex_def)

lemma refines_assume_result_and_state:
  "sim_set R (P s) (Q t) \<Longrightarrow>
    refines (assume_result_and_state P) (assume_result_and_state Q) s t
     (\<lambda>(Res v, s) (Res w, t). R (v, s) (w, t))"
  by (force simp: refines.rep_eq sim_set_def)

lemma refines_assume_result_and_state_iff:
  "refines (assume_result_and_state A) (assume_result_and_state B) s t Q \<longleftrightarrow> 
        sim_set (\<lambda>(v, s') (w, t'). Q (Result v, s') (Result w, t')) (A s) (B t) "
  apply (simp add: refines.rep_eq, intro iffI)
  subgoal
    by (fastforce simp add: sim_set_def)
  subgoal
    by (force simp add: sim_set_def)
  done

subsection \<open>\<^const>\<open>gets\<close>\<close>

lemma run_gets[run_spec_monad, simp]:"run (gets f) s = pure_post_state (Result (f s), s)"
  by (simp add: gets_def run_bind)

lemma always_progress_gets[always_progress_intros]: "always_progress (gets f)"
  by (simp add: always_progress_def)

lemma runs_to_gets[runs_to_vcg]: "gets f \<bullet> s \<lbrace>\<lambda>r t. r = Result (f s) \<and> t = s\<rbrace>"
  by (simp add: runs_to.rep_eq)

lemma runs_to_gets_iff[runs_to_iff]: "gets f \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> Q (Result (f s)) s"
  by (simp add: runs_to.rep_eq)

lemma runs_to_partial_gets[runs_to_vcg]: "gets f \<bullet> s ?\<lbrace>\<lambda>r t. r = Result (f s) \<and> t = s\<rbrace>"
  by (simp add: runs_to_partial.rep_eq)

lemma refines_gets: "R (Result (f s), s) (Result (g t), t) \<Longrightarrow> refines (gets f) (gets g) s t R"
  by (auto simp add: refines.rep_eq)

lemma rel_spec_gets: "R (Result (f s), s) (Result (g t), t) \<Longrightarrow> rel_spec (gets f) (gets g) s t R"
  by (auto simp add: rel_spec_iff_refines intro: refines_gets)

lemma runs_to_always_progress_to_gets:
  "(\<And>s. f \<bullet> s \<lbrace>\<lambda>r t. t = s \<and> r = Result (v s)\<rbrace>) \<Longrightarrow> always_progress f \<Longrightarrow> f = gets v"
  apply (clarsimp simp: spec_monad_ext_iff runs_to.rep_eq always_progress.rep_eq)
  subgoal premises prems for s
    using prems[rule_format, of s]
    by (cases "run f s"; auto simp add: pure_post_state_def Ball_def)
  done

lemma gets_let_bind: "(gets (\<lambda>s. let v = f' s in (g' v s))) = do {v <- gets f'; gets (g' v)}"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

subsection \<open>\<^const>\<open>assert_result_and_state\<close>\<close>

lemma run_assert_result_and_state[run_spec_monad]:
  "run (assert_result_and_state f) s =
    (if f s = {} then \<top> else Success ((\<lambda>(v, t). (Result v, t)) `  f s))"
  by (auto simp add: assert_result_and_state_def run_bind pure_post_state_def Sup_Success_pair)

lemma always_progress_assert_result_and_state[always_progress_intros]:
  "always_progress (assert_result_and_state f)"
  by (auto simp add: always_progress_def run_assert_result_and_state)

lemma runs_to_assert_result_and_state_iff[runs_to_iff]:
  "assert_result_and_state f \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (f s \<noteq> {} \<and> (\<forall>(v,t) \<in> f s. Q (Result v) t))"
  by (auto simp add: runs_to.rep_eq run_assert_result_and_state)

lemma runs_to_assert_result_and_state[runs_to_vcg]:
  "f s \<noteq> {} \<Longrightarrow> assert_result_and_state f \<bullet> s \<lbrace>\<lambda>r t. \<exists>v. r = Result v \<and> (v, t) \<in> f s\<rbrace>"
  by (simp add: runs_to_assert_result_and_state_iff)

lemma runs_to_partial_assert_result_and_state[runs_to_vcg]:
  "assert_result_and_state f \<bullet> s ?\<lbrace>\<lambda>r t. \<exists>v. r = Result v \<and> (v, t) \<in> f s\<rbrace>"
  by (auto simp add: runs_to_partial.rep_eq run_assert_result_and_state)

lemma runs_to_state_select[runs_to_vcg]:
  "\<exists>t. (s, t) \<in> R \<Longrightarrow> state_select R \<bullet> s \<lbrace> \<lambda>r t. r = Result () \<and> (s, t) \<in> R \<rbrace>"
  by (auto intro!: runs_to_assert_result_and_state[THEN runs_to_weaken])

lemma runs_to_partial_state_select[runs_to_vcg]:
  "state_select R \<bullet> s ?\<lbrace> \<lambda>r t. r = Result () \<and> (s, t) \<in> R \<rbrace>"
  by (simp add: runs_to_partial.rep_eq run_assert_result_and_state)

lemma refines_assert_result_and_state:
  assumes sim: "(\<And>r' s'. (r', s') \<in> f s \<Longrightarrow> (\<exists>v' t'. (v', t') \<in> g t \<and> R (Result r', s') (Result v', t')))" 
  assumes emp: "f s = {} \<Longrightarrow> g t = {}"
  shows "refines (assert_result_and_state f) (assert_result_and_state g) s t R"
  using sim emp by (fastforce simp add: refines_iff_runs_to runs_to_iff)

lemma refines_state_select: 
  assumes sim: "(\<And>s'. (s, s') \<in> f \<Longrightarrow> (\<exists>t'. (t, t') \<in> g \<and> R (Result (), s') (Result (), t')))" 
  assumes emp: "\<nexists>s'. (s, s') \<in> f \<Longrightarrow> \<nexists>t'. (t, t') \<in> g"
  shows "refines (state_select f) (state_select g) s t R"
  using sim emp by (intro refines_assert_result_and_state) auto

subsection "\<^const>\<open>assuming\<close>"

lemma run_assuming[run_spec_monad]:
  "run (assuming g) s = (if g s then pure_post_state (Result (), s) else \<bottom>)"
  by (simp add: assuming_def run_bind)

lemma always_progress_assuming[always_progress_intros]: "always_progress (assuming g) \<longleftrightarrow> (\<forall>s. g s)"
  by (auto simp add: always_progress_def run_assuming)

lemma runs_to_assuming[runs_to_vcg]: "assuming g \<bullet> s \<lbrace>\<lambda>r t. g s \<and> r = Result () \<and> t = s\<rbrace>"
  by (simp add: runs_to.rep_eq run_assuming)

lemma runs_to_assuming_iff[runs_to_iff]: "assuming g \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (g s \<longrightarrow> Q (Result ()) s)"
  by (auto simp add: runs_to.rep_eq run_assuming)

lemma runs_to_partial_assuming[runs_to_vcg]:
  "assuming g \<bullet> s ?\<lbrace>\<lambda>r t. g s \<and> r = Result () \<and> t = s \<and> g s\<rbrace>"
  by (simp add: runs_to_partial.rep_eq run_assuming)

lemma assuming_state_assume:
  "assuming P = assume_result_and_state (\<lambda>s. (if P s then {((), s)} else {}))"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma assuming_True[simp]: "assuming (\<lambda>s. True) = skip"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma refines_assuming:
  "(P s \<Longrightarrow> Q t) \<Longrightarrow> (P s \<Longrightarrow> Q t \<Longrightarrow> R (Result (), s) (Result (), t)) \<Longrightarrow>
    refines (assuming P) (assuming Q) s t R"
  by (auto simp add: refines.rep_eq run_assuming)

lemma rel_spec_assuming:
  "(Q t \<longleftrightarrow> P s) \<Longrightarrow> (P s \<Longrightarrow> Q t \<Longrightarrow> R (Result (), s) (Result (), t)) \<Longrightarrow>
    rel_spec (assuming P) (assuming Q) s t R"
  by (auto simp add: rel_spec_def run_assuming rel_set_def)

lemma refines_bind_assuming_right:
  "P t \<Longrightarrow> (P t \<Longrightarrow> refines f (g ()) s t R) \<Longrightarrow> refines f (assuming P \<bind> g) s t R"
  by (simp add: refines.rep_eq run_assuming run_bind)

lemma refines_bind_assuming_left:
  "(P s \<Longrightarrow> refines (f ()) g s t R) \<Longrightarrow> refines (assuming P >>= f) g s t R"
  by (simp add: refines.rep_eq run_assuming run_bind)

subsection "\<^const>\<open>guard\<close>"

lemma run_guard[run_spec_monad]:
  "run (guard g) s = (if g s then pure_post_state (Result (), s) else \<top>)"
  by (simp add: guard_def run_bind)

lemma always_progress_guard[always_progress_intros]: "always_progress (guard g)"
  by (auto simp add: always_progress_def run_guard)

lemma runs_to_guard[runs_to_vcg]: "g s \<Longrightarrow> guard g \<bullet> s \<lbrace>\<lambda>r t. r = Result () \<and> t = s\<rbrace>"
  by (simp add: runs_to.rep_eq run_guard)

lemma runs_to_guard_iff[runs_to_iff]: "guard g \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (g s \<and> Q (Result ()) s)"
  by (auto simp add: runs_to.rep_eq run_guard)

lemma runs_to_partial_guard[runs_to_vcg]: "guard g \<bullet> s ?\<lbrace>\<lambda>r t. r = Result () \<and> t = s \<and> g s\<rbrace>"
  by (simp add: runs_to_partial.rep_eq run_guard)

lemma refines_guard:
  "(Q t \<Longrightarrow> P s) \<Longrightarrow> (P s \<Longrightarrow> Q t \<Longrightarrow> R (Result (), s) (Result (), t)) \<Longrightarrow>
    refines (guard P) (guard Q) s t R"
  by (auto simp add: refines.rep_eq run_guard)

lemma rel_spec_guard:
  "(Q t \<longleftrightarrow> P s) \<Longrightarrow> (P s \<Longrightarrow> Q t \<Longrightarrow> R (Result (), s) (Result (), t)) \<Longrightarrow>
    rel_spec (guard P) (guard Q) s t R"
  by (auto simp add: rel_spec_def run_guard rel_set_def)

lemma refines_bind_guard_right:
  "refines f (guard P \<bind> g) s t R" if "P t \<Longrightarrow> refines f (g ()) s t R"
  using that
  by (auto simp: refines.rep_eq run_guard run_bind)

lemma guard_False_fail: "guard (\<lambda>_. False) = fail"
  by (simp add: spec_monad_ext run_guard)

lemma rel_spec_monad_bind_guard:
  shows "(\<And>x. rel_spec_monad (=) Q (f x) (g x)) \<Longrightarrow>
    rel_spec_monad (=) Q (guard P >>= f) (guard P >>= g)"
  by (auto simp add: rel_spec_monad_def run_bind run_guard)

lemma runs_to_guard_bind_iff: "((guard P >>= f) \<bullet> s \<lbrace> Q \<rbrace>) \<longleftrightarrow> P s \<and> ((f ()) \<bullet> s \<lbrace> Q \<rbrace>)"
  by (simp add: runs_to_iff)

lemma refines_bind_guard_right_iff:
  "refines f (guard P \<bind> g) s t R \<longleftrightarrow> (P t \<longrightarrow> refines f (g ()) s t R)"
  by (auto simp: refines.rep_eq run_guard run_bind)

lemma refines_bind_guard_right_end:
  assumes f_g: "refines f g s t R"
  shows "refines f (do {res <- g; guard G; return res}) s t 
            (\<lambda>(r, s) (q, t). R (r, s) (q, t) \<and> 
                (case q of Exception e \<Rightarrow> True | Result _ \<Rightarrow> G t))"
  apply (subst bind_return[symmetric])
  apply (rule refines_bind[OF f_g])
  apply (auto simp: refines_bind_guard_right_iff)
  done

lemma refines_bind_guard_right_end':
  assumes f_g: "refines f g s t R"
  shows "refines f (do {res <- g; guard (G res); return res}) s t 
            (\<lambda>(r, s) (q, t). R (r, s) (q, t) \<and> 
                (case q of Exception e \<Rightarrow> True | Result v \<Rightarrow> G v t))"
  apply (subst bind_return[symmetric])
  apply (rule refines_bind[OF f_g])
  apply (auto simp: refines_bind_guard_right_iff)
  done

subsection "\<^const>\<open>assert_opt\<close>"

lemma run_assert_opt[run_spec_monad, simp]:
  "run (assert_opt x) s = (case x of Some v \<Rightarrow> pure_post_state (Result v, s) | None \<Rightarrow> \<top>)"
  by (simp add: assert_opt_def run_bind split: option.splits)

lemma always_progress_assert_opt[always_progress_intros]: "always_progress (assert_opt x)"
  by (simp add: always_progress_intros assert_opt_def split: option.splits)

lemma runs_to_assert_opt[runs_to_vcg]: "(\<exists>v. x = Some v \<and> Q (Result v) s) \<Longrightarrow> assert_opt x \<bullet> s \<lbrace>Q\<rbrace>"
  by (auto simp add: runs_to.rep_eq)

lemma runs_to_assert_opt_iff[runs_to_iff]:
  "assert_opt x \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (\<exists>v. x = Some v \<and> Q (Result v) s)"
  by (auto simp add: runs_to.rep_eq split: option.split)

lemma runs_to_partial_assert_opt[runs_to_vcg]:
  "(\<And>v. x = Some v \<Longrightarrow> Q (Result v) s) \<Longrightarrow> assert_opt x \<bullet> s ?\<lbrace>Q\<rbrace>"
  by (auto simp add: runs_to_partial.rep_eq split: option.split)

subsection "\<^const>\<open>gets_the\<close>"

lemma run_gets_the':
  "run (gets_the f) s = (case f s of Some v \<Rightarrow> pure_post_state (Result v, s) | None \<Rightarrow> \<top>)"
  by (simp add: gets_the_def run_bind top_post_state_def pure_post_state_def split: option.split)

lemma run_gets_the[run_spec_monad, simp]:
  "run (gets_the f) s = (case (f s) of Some v \<Rightarrow> pure_post_state (Result v, s) | None \<Rightarrow> \<top>)"
  by (simp add: gets_the_def run_bind)

lemma always_progress_gets_the[always_progress_intros]: "always_progress (gets_the f)"
  by (simp add: always_progress_intros gets_the_def split: option.splits)

lemma runs_to_gets_the[runs_to_vcg]: "(\<exists>v. f s = Some v \<and> Q (Result v) s) \<Longrightarrow> gets_the f \<bullet> s \<lbrace>Q\<rbrace>"
  by (auto simp add: runs_to.rep_eq)

lemma runs_to_gets_the_iff[runs_to_iff]:
  "gets_the f \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (\<exists>v. f s = Some v \<and> Q (Result v) s)"
  by (auto simp add: runs_to.rep_eq split: option.split)

lemma runs_to_partial_gets_the[runs_to_vcg]:
  "(\<And>v. f s = Some v \<Longrightarrow> Q (Result v) s) \<Longrightarrow> gets_the f \<bullet> s ?\<lbrace>Q\<rbrace>"
  by (auto simp add: runs_to_partial.rep_eq split: option.split)

subsection \<open>\<^const>\<open>modify\<close>\<close>

lemma run_modify[run_spec_monad, simp]: "run (modify f) s = pure_post_state (Result (), f s)"
  by (simp add: modify_def run_bind)

lemma always_progress_modifiy[always_progress_intros]: "always_progress (modify f)"
  by (simp add: modify_def always_progress_intros)

lemma runs_to_modify[runs_to_vcg]: "modify f \<bullet> s \<lbrace> \<lambda>r t. r = Result () \<and> t = f s \<rbrace>"
  by (simp add: runs_to.rep_eq)

lemma runs_to_modify_res[runs_to_vcg]: "((modify f)::(unit, 's) res_monad) \<bullet> s \<lbrace> \<lambda>r t. t = f s \<rbrace>"
  by (simp add: runs_to.rep_eq)

lemma runs_to_modify_iff[runs_to_iff]: "modify f \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> Q (Result ()) (f s)"
  by (simp add: runs_to.rep_eq)

lemma runs_to_partial_modify[runs_to_vcg]: "modify f \<bullet> s ?\<lbrace> \<lambda>r t. r = Result () \<and> t = f s \<rbrace>"
  by (simp add: runs_to_partial.rep_eq)

lemma runs_to_partial_modify_res[runs_to_vcg]:
  "((modify f)::(unit, 's) res_monad) \<bullet> s ?\<lbrace> \<lambda>r t. t = f s \<rbrace>"
  by (simp add: runs_to_partial.rep_eq)

lemma refines_modify:
  "R (Result (), f s) (Result (), g t) \<Longrightarrow> refines (modify f) (modify g) s t R"
  by (auto simp add: refines.rep_eq)

lemma rel_spec_modify:
  "R (Result (), f s) (Result (), g t) \<Longrightarrow> rel_spec (modify f) (modify g) s t R"
  by (auto simp add: rel_spec_iff_refines intro: refines_modify)

subsection \<open>condition\<close>

lemma run_condition[run_spec_monad]: "run (condition c f g) s = (if c s then run f s else run g s)"
  by (simp add: condition_def run_bind)

lemma run_condition_True[run_spec_monad, simp]: "c s \<Longrightarrow> run (condition c f g) s = run f s"
  by (simp add: run_condition)

lemma run_condition_False[run_spec_monad, simp]: "\<not>c s \<Longrightarrow> run (condition c f g) s = run g s"
  by (simp add: run_condition)

lemma always_progress_condition[always_progress_intros]:
  "always_progress f \<Longrightarrow> always_progress g \<Longrightarrow> always_progress (condition c f g)"
  by (auto simp add: always_progress_def run_condition)

lemma condition_swap: "(condition C A B) = (condition (\<lambda>s. \<not> C s) B A)"
  by (rule spec_monad_ext) (clarsimp simp add: run_condition)

lemma condition_fail_rhs: "(condition C X fail) = (guard C >>= (\<lambda>_. X))"
  by (rule spec_monad_ext) (simp add: run_bind run_guard run_condition)

lemma condition_fail_lhs: "(condition C fail X) = (guard (\<lambda>s. \<not> C s) >>= (\<lambda>_. X))"
  by (metis condition_fail_rhs condition_swap)

lemma condition_bind_fail[simp]:
  "(condition C A B >>= (\<lambda>_. fail)) = condition C (A >>= (\<lambda>_. fail)) (B >>= (\<lambda>_. fail))"
  apply (rule spec_monad_ext)
  apply (clarsimp simp add: run_condition run_bind)
  done

lemma condition_True[simp]: "condition (\<lambda>_. True) f g = f"
  apply (rule spec_monad_ext)
  apply (clarsimp simp add: run_condition run_bind)
  done

lemma condition_False[simp]: "condition (\<lambda>_. False) f g = g"
  apply (rule spec_monad_ext)
  apply (clarsimp simp add: run_condition run_bind)
  done

lemma le_condition_runI:
  "(\<And>s. c s \<Longrightarrow> run h s \<le> run f s) \<Longrightarrow> (\<And>s. \<not> c s \<Longrightarrow> run h s \<le> run g s)
  \<Longrightarrow> h \<le> condition c f g"
  by (simp add: le_spec_monad_runI run_condition)

lemma mono_condition_spec_monad:
  "mono T \<Longrightarrow> mono F \<Longrightarrow> mono (\<lambda>x. condition C (F x) (T x))"
  by (auto simp: condition_def intro!: mono_bind_spec_monad mono_const)

lemma mono_condition: "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> condition c f g \<le> condition c f' g'"
  by (simp add: le_fun_def less_eq_spec_monad.rep_eq run_condition)

lemma monotone_condition_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> (monotone R (\<le>) (\<lambda>f'. g f'))
  \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. condition c (f f') (g f'))"
  by (auto simp add: monotone_def intro!: mono_condition)

lemma monotone_condition_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> (monotone R (\<ge>) (\<lambda>f'. g f'))
  \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. condition c (f f') (g f'))"
  by (auto simp add: monotone_def intro!: mono_condition)

lemma runs_to_condition[runs_to_vcg]:
  "(c s \<Longrightarrow> f \<bullet> s \<lbrace> Q \<rbrace>) \<Longrightarrow> (\<not> c s \<Longrightarrow> g \<bullet> s \<lbrace> Q \<rbrace>) \<Longrightarrow> condition c f g \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to.rep_eq run_condition)

lemma runs_to_condition_iff[runs_to_iff]:
  "condition c f g \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (if c s then f \<bullet> s \<lbrace> Q \<rbrace> else g \<bullet> s \<lbrace> Q \<rbrace>)"
  by (simp add: runs_to.rep_eq run_condition)

lemma runs_to_partial_condition[runs_to_vcg]:
  "(c s \<Longrightarrow> f \<bullet> s ?\<lbrace> Q \<rbrace>) \<Longrightarrow> (\<not> c s \<Longrightarrow> g \<bullet> s ?\<lbrace> Q \<rbrace>) \<Longrightarrow> condition c f g \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: runs_to_partial.rep_eq run_condition)

lemma refines_condition_iff:
  assumes "c' s' \<longleftrightarrow> c s"
  shows "refines (condition c f g) (condition c' f' g') s s' R \<longleftrightarrow>
   (if c' s' then refines f f' s s' R else refines g g' s s' R)"
  using assms
  by (auto simp add: refines.rep_eq run_condition)

lemma refines_condition:
  "P s \<longleftrightarrow> P' s' \<Longrightarrow>
    (P s \<Longrightarrow> P' s' \<Longrightarrow> refines f f' s s' R) \<Longrightarrow>
    (\<not> P s \<Longrightarrow> \<not> P' s' \<Longrightarrow> refines g g' s s' R) \<Longrightarrow>
    refines (condition P f g) (condition P' f' g') s s' R"
  using refines_condition_iff
  by metis

lemma refines_condition_TrueI:
  assumes "c' s' = c s" and "c' s'" "refines f f' s s' R"
  shows "refines (condition c f g) (condition c' f' g') s s' R"
  by (simp add:  refines_condition_iff[where c'=c' and c=c and s'=s' and s=s, OF assms(1)] assms(2, 3))

lemma refines_condition_FalseI:
  assumes "c' s' = c s" and "\<not>c' s'" "refines g g' s s' R"
  shows "refines (condition c f g) (condition c' f' g') s s' R"
  by (simp add:  refines_condition_iff[where c'=c' and c=c and s'=s' and s=s, OF assms(1)] assms(2, 3))

lemma refines_condition_bind_left:
  "refines (condition C T F \<bind> X) Y s t R \<longleftrightarrow>
    (C s \<longrightarrow> refines (T \<bind> X) Y s t R) \<and> (\<not> C s \<longrightarrow> refines (F \<bind> X) Y s t R)"
  by (simp add: refines.rep_eq run_bind run_condition)

lemma refines_condition_bind_right:
  "refines X (condition C T F \<bind> Y) s t R \<longleftrightarrow>
    (C t \<longrightarrow> refines X (T \<bind> Y) s t R) \<and> (\<not> C t \<longrightarrow> refines X (F \<bind> Y) s t R)"
  by (simp add: refines.rep_eq run_bind run_condition)

lemma rel_spec_condition_iff:
  assumes "c' s' \<longleftrightarrow> c s"
  shows "rel_spec (condition c f g) (condition c' f' g') s s' R \<longleftrightarrow>
   (if c' s' then rel_spec f f' s s' R else rel_spec g g' s s' R)"
  using assms
  by (auto simp add: rel_spec_def run_condition)

lemma rel_spec_condition:
  "P s \<longleftrightarrow> P' s' \<Longrightarrow>
    (P s \<Longrightarrow> P' s' \<Longrightarrow> rel_spec f f' s s' R) \<Longrightarrow>
    (\<not> P s \<Longrightarrow> \<not> P' s' \<Longrightarrow> rel_spec g g' s s' R) \<Longrightarrow>
    rel_spec (condition P f g) (condition P' f' g') s s' R"
  using rel_spec_condition_iff
  by metis

lemma rel_spec_condition_TrueI:
  assumes "c' s' = c s" and "c' s'" "rel_spec f f' s s' R"
  shows "rel_spec (condition c f g) (condition c' f' g') s s' R"
  by (simp add:  rel_spec_condition_iff[where c'=c' and c=c and s'=s' and s=s, OF assms(1)] assms(2, 3))

lemma rel_spec_condition_FalseI:
  assumes "c' s' = c s" and "\<not>c' s'" "rel_spec g g' s s' R"
  shows "rel_spec (condition c f g) (condition c' f' g') s s' R"
  by (simp add:  rel_spec_condition_iff[where c'=c' and c=c and s'=s' and s=s, OF assms(1)] assms(2, 3))

lemma refines_condition_left:
  "(P s \<Longrightarrow> refines f h s t R) \<Longrightarrow> (\<not> P s \<Longrightarrow> refines g h s t R) \<Longrightarrow>
    refines (condition P f g) h s t R"
  by (simp add: refines.rep_eq run_condition)

lemma rel_spec_condition_left:
  "(P s \<Longrightarrow> rel_spec f h s t R) \<Longrightarrow> (\<not> P s \<Longrightarrow> rel_spec g h s t R) \<Longrightarrow>
    rel_spec (condition P f g) h s t R"
  by (auto simp add: rel_spec_def run_condition)

lemma refines_condition_true:
  "P t \<Longrightarrow> refines f g s t R \<Longrightarrow> refines f (condition P g h) s t R"
  by (simp add: refines.rep_eq run_condition)

lemma rel_spec_condition_true:
  "P t \<Longrightarrow> rel_spec f g s t R \<Longrightarrow>
    rel_spec f (condition P g h) s t R"
  by (auto simp add: rel_spec_def run_condition)

lemma refines_condition_false:
  "\<not> P t \<Longrightarrow> refines f h s t R \<Longrightarrow>
    refines f (condition P g h) s t R"
  by (simp add: refines.rep_eq run_condition)

lemma rel_spec_condition_false:
  "\<not> P t \<Longrightarrow> rel_spec f h s t R \<Longrightarrow>
    rel_spec f (condition P g h) s t R"
  by (auto simp add: rel_spec_def run_condition)

lemma condition_bind:
  "(condition P f g >>= h) = condition P (f >>= h) (g >>= h)"
  by (simp add: spec_monad_ext_iff run_condition run_bind)

lemma rel_spec_monad_condition:
  assumes "rel_fun R (=) P P'"
    and "rel_spec_monad R Q f f'"
    and "rel_spec_monad R Q g g'"
  shows "rel_spec_monad R Q (condition P f g) (condition P' f' g')"
  using assms
  by (auto simp add: rel_spec_monad_def run_condition rel_fun_def)

lemma rel_spec_monad_condition_const:
  "P \<longleftrightarrow> P' \<Longrightarrow> (P \<Longrightarrow> rel_spec_monad R Q f f') \<Longrightarrow>
    (\<not> P \<Longrightarrow> rel_spec_monad R Q g g') \<Longrightarrow>
  rel_spec_monad R Q (condition (\<lambda>_. P) f g) (condition (\<lambda>_. P') f' g')"
  by (cases P) (auto simp add: condition_def)

subsection "\<^const>\<open>when\<close>"

lemma run_when[run_spec_monad]:
  "run (when c f) s = (if c then run f s else pure_post_state (Result (), s))"
  unfolding when_def by simp

lemma always_progress_when[always_progress_intros]:
  "always_progress f \<Longrightarrow> always_progress (when c f)"
  unfolding when_def by (simp add: always_progress_intros)

lemma runs_to_when[runs_to_vcg]:
  "(c \<Longrightarrow> f \<bullet> s \<lbrace> Q \<rbrace>) \<Longrightarrow> (\<not> c \<Longrightarrow> Q (Result ()) s) \<Longrightarrow> when c f \<bullet> s \<lbrace> Q \<rbrace>"
  by (auto simp add: runs_to.rep_eq run_when)

lemma runs_to_when_iff[runs_to_iff]: "
  (when c f) \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (if c then f \<bullet> s \<lbrace> Q \<rbrace> else Q (Result ()) s)"
  by (auto simp add: runs_to.rep_eq run_when)

lemma runs_to_partial_when[runs_to_vcg]:
  "(c \<Longrightarrow> f \<bullet> s ?\<lbrace> Q \<rbrace>) \<Longrightarrow> (\<not> c \<Longrightarrow> Q (Result ()) s) \<Longrightarrow> when c f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (auto simp add: runs_to_partial.rep_eq run_when)

lemma mono_when: "f \<le> f' \<Longrightarrow> when c f \<le> when c f'"
  unfolding when_def by (simp add: mono_condition)

lemma monotone_when_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f')
  \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. when c (f f'))"
  unfolding when_def by (simp add: monotone_condition_le)

lemma monotone_when_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f')
  \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. when c (f f'))"
  unfolding when_def by (simp add: monotone_condition_ge)

lemma when_True[simp]: "when True f = f"
  apply (rule spec_monad_ext)
  apply (simp add: run_when)
  done

lemma when_False[simp]: "when False f = return ()"
  apply (rule spec_monad_ext)
  apply (simp add: run_when)
  done

subsection \<open>While\<close>

context fixes C :: "'a \<Rightarrow> 's \<Rightarrow> bool" and B :: "'a \<Rightarrow> ('e::default, 'a, 's) spec_monad"
begin

definition whileLoop :: "'a \<Rightarrow> ('e, 'a, 's) spec_monad" where
  "whileLoop =
    gfp (\<lambda>W a. condition (C a) (bind (B a) W) (return a))"
  \<comment> \<open>Collapses to \<^const>\<open>Failure\<close> in case of any non terminating computation.\<close>

definition whileLoop_finite :: "'a \<Rightarrow> ('e, 'a, 's) spec_monad" where
  "whileLoop_finite =
    lfp (\<lambda>W a. condition (C a) (bind (B a) W) (return a))"
  \<comment> \<open>Does not collapse to \<^const>\<open>Failure\<close> in presence of a non terminating computation.
    \<^const>\<open>Failure\<close> can still occur when the body fails in some iteration. It
    captures the outcomes of all terminating and thus finite computations.\<close>

inductive whileLoop_terminates :: "'a \<Rightarrow> 's \<Rightarrow> bool" where
  step: "\<And>a s. (C a s \<Longrightarrow> B a \<bullet> s ?\<lbrace> \<lambda>v s. \<forall>a. v = Result a \<longrightarrow> whileLoop_terminates a s \<rbrace>) \<Longrightarrow>
    whileLoop_terminates a s"
  \<comment> \<open> This is weaker than \<open>run (whileLoop a) s \<noteq> \<top>\<close>: as it uses partial correctness \<close>

lemma mono_whileLoop_functional:
  "mono (\<lambda>W a. condition (C a) (bind (B a) W) (return a))"
  by (intro mono_app mono_lam mono_const mono_bind_spec_monad mono_condition_spec_monad)

lemma whileLoop_unroll:
  "whileLoop a =
    condition (C a) (bind (B a) whileLoop) (return a)"
  unfolding whileLoop_def
  by (subst gfp_unfold[OF mono_whileLoop_functional]) simp

lemma whileLoop_finite_unfold:
  "whileLoop_finite a =
    condition (C a) (bind (B a) whileLoop_finite) (return a)"
  unfolding whileLoop_finite_def
  by (subst lfp_unfold[OF mono_whileLoop_functional]) simp

lemma whileLoop_ne_Failure:
  "(C a s \<Longrightarrow> B a \<bullet> s \<lbrace> \<lambda>x s. \<forall>a. x = Result a \<longrightarrow> run (whileLoop a) s \<noteq> Failure \<rbrace>) \<Longrightarrow>
    run (whileLoop a) s \<noteq> Failure"
  by (subst whileLoop_unroll)
     (simp add: run_condition run_bind_eq_top_iff flip: top_post_state_def)

lemma whileLoop_ne_top_induct[consumes 1, case_names step]:
  assumes a_s: "run (whileLoop a) s \<noteq> \<top>"
    and step: "\<And>a s. (C a s \<Longrightarrow> B a \<bullet> s \<lbrace> \<lambda>x s. \<forall>a. x = Result a \<longrightarrow> P a s \<rbrace>) \<Longrightarrow> P a s"
  shows "P a s"
proof -
  have "(\<lambda>a. Spec (\<lambda>s. if P a s then \<bottom> else \<top>)) \<le> whileLoop"
    unfolding whileLoop_def
    by (intro gfp_upperbound)
       (auto intro: step runs_to_weaken
         simp: le_fun_def less_eq_spec_monad.rep_eq run_condition top_unique run_bind_eq_top_iff)
  with a_s show ?thesis
    by (auto simp add: le_fun_def less_eq_spec_monad.rep_eq top_unique top_post_state_def
             split: if_splits)
qed

lemma runs_to_whileLoop:
  assumes R: "wf R"
  assumes *: "I (Result a) s"
  assumes P_Result: "\<And>a s. \<not> C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> P (Result a) s"
  assumes P_Exception: "\<And>a s. a \<noteq> default \<Longrightarrow> I (Exception a) s \<Longrightarrow> P (Exception a) s"
  assumes B: "\<And>a s. C a s \<Longrightarrow> I (Result a) s \<Longrightarrow>
    B a  \<bullet> s \<lbrace>\<lambda>r t. I r t \<and> (\<forall>b. r = Result b \<longrightarrow> ((b, t), (a, s)) \<in> R)\<rbrace>"
  shows "whileLoop a \<bullet> s \<lbrace>P\<rbrace>"
proof (use R * in \<open>induction x\<equiv>"(a, s)" arbitrary: a s\<close>)
  case (less a s)
  show ?case
    by (auto simp: P_Result P_Exception whileLoop_unroll[of a]
                   runs_to_condition_iff runs_to_bind_iff less
             intro!: runs_to_weaken[OF B])
qed

lemma runs_to_whileLoop_finite:
  assumes *: "I (Result a) s"
  assumes P_Result: "\<And>a s. \<not> C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> P (Result a) s"
  assumes P_Exception: "\<And>a s. a \<noteq> default \<Longrightarrow> I (Exception a) s \<Longrightarrow> P (Exception a) s"
  assumes B: "\<And>a s. C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> B a \<bullet> s \<lbrace> I \<rbrace>"
  shows "whileLoop_finite a \<bullet> s \<lbrace>P\<rbrace>"
proof -
  have "whileLoop_finite a \<bullet> s
    \<lbrace> \<lambda>x s. I x s \<and> (\<forall>a. x = Result a \<longrightarrow> C a s \<longrightarrow> P (Result a) s) \<rbrace>"
    unfolding whileLoop_finite_def
    apply (rule runs_to_lfp[OF mono_whileLoop_functional, of "\<lambda>a. I (Result a)", OF *])
    subgoal premises prems for W x s
      using prems(2)
      by (intro runs_to_condition runs_to_bind runs_to_yield_iff
                runs_to_weaken[OF B] runs_to_weaken[OF prems(1)] conjI allI impI)
         simp_all
    done
  then show ?thesis
    apply (rule runs_to_weaken)
    subgoal for r s
      by (cases r; cases "\<exists>a. r = Result a \<and> C a s"; simp add: P_Result P_Exception)
    done
qed

lemma runs_to_partial_whileLoop_finite:
  assumes *: "I (Result a) s"
  assumes B: "\<And>a s. C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> (B a) \<bullet> s ?\<lbrace> I \<rbrace>"
  assumes P_Result: "\<And>a s. \<not> C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> P (Result a) s"
  assumes P_Exception: "\<And>a s. a \<noteq> default \<Longrightarrow> I (Exception a) s \<Longrightarrow> P (Exception a) s"
  shows "whileLoop_finite a \<bullet> s ?\<lbrace> P \<rbrace>"
proof -
  have "whileLoop_finite a \<bullet> s \<lbrace>P\<rbrace>" if **: "run (whileLoop_finite a) s \<noteq> \<top>"
    apply (rule runs_to_whileLoop_finite[where
          I="\<lambda>x s. I x s \<and> (\<forall>a. x = Result a \<longrightarrow> run (whileLoop_finite a) s \<noteq> \<top>)"])
       apply (auto simp: * ** P_Result P_Exception)[3]
    subgoal for a s using B[of a s]
      by (subst (asm) whileLoop_finite_unfold)
        (auto simp: runs_to_conj run_bind_eq_top_iff  dest: runs_to_of_runs_to_partial_runs_to')
    done
  then show ?thesis
    by (auto simp: runs_to_partial_alt top_post_state_def)
qed

lemma whileLoop_finite_eq_whileLoop_of_whileLoop_terminates:
  assumes "whileLoop_terminates a s"
  shows "run (whileLoop_finite a) s = run (whileLoop a) s"
proof (use assms in \<open>induction\<close>)
  case (step a s)
  show ?case
    apply (subst whileLoop_unroll)
    apply (subst whileLoop_finite_unfold)
    apply (auto simp: run_condition intro!: run_bind_cong[OF refl runs_to_partial_weaken, OF step])
    done
qed

lemma whileLoop_terminates_of_succeeds:
  "run (whileLoop a) s \<noteq> \<top> \<Longrightarrow> whileLoop_terminates a s"
  by (induction rule: whileLoop_ne_top_induct)
     (auto intro: whileLoop_terminates.step runs_to_partial_of_runs_to)

lemma whileLoop_finite_eq_whileLoop:
  "run (whileLoop a) s \<noteq> \<top> \<Longrightarrow> run (whileLoop_finite a) s = run (whileLoop a) s"
  by (rule whileLoop_finite_eq_whileLoop_of_whileLoop_terminates[OF
    whileLoop_terminates_of_succeeds])

lemma runs_to_whileLoop_of_runs_to_whileLoop_finite_if_terminates:
  "whileLoop_terminates i s \<Longrightarrow> whileLoop_finite i \<bullet> s \<lbrace>Q\<rbrace> \<Longrightarrow> whileLoop i \<bullet> s \<lbrace>Q\<rbrace>"
  unfolding runs_to.rep_eq  whileLoop_finite_eq_whileLoop_of_whileLoop_terminates .

lemma whileLoop_finite_le_whileLoop: "whileLoop_finite a \<le> whileLoop a"
  using le_fun_def lfp_le_gfp mono_whileLoop_functional
  unfolding whileLoop_finite_def whileLoop_def
  by fastforce

lemma runs_to_partial_whileLoop_finite_whileLoop:
  "whileLoop_finite i \<bullet> s ?\<lbrace>Q\<rbrace> \<Longrightarrow> whileLoop i \<bullet> s ?\<lbrace>Q\<rbrace>"
  by (cases "run (whileLoop i) s = \<top>")
     (auto simp:
       runs_to.rep_eq runs_to_partial_alt whileLoop_finite_eq_whileLoop top_post_state_def)

lemma runs_to_partial_whileLoop:
  assumes "I (Result a) s"
  assumes "\<And>a s. \<not> C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> P (Result a) s"
  assumes "\<And>a s. a \<noteq> default \<Longrightarrow> I (Exception a) s \<Longrightarrow> P (Exception a) s"
  assumes "\<And>a s. C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> (B a) \<bullet> s ?\<lbrace> I \<rbrace>"
  shows "whileLoop a \<bullet> s ?\<lbrace> P \<rbrace>"
  using assms(1,4,2,3)
  by (rule runs_to_partial_whileLoop_finite_whileLoop[OF runs_to_partial_whileLoop_finite])

lemma always_progress_whileLoop[always_progress_intros]:
  assumes B: "(\<And>v. always_progress (B v))"
  shows "always_progress (whileLoop a)"
  unfolding always_progress.rep_eq
proof
  fix s have "run (whileLoop a) s \<noteq> \<bottom>" if *: "run (whileLoop a) s \<noteq> \<top>"
  proof (use * in \<open>induction rule: whileLoop_ne_top_induct\<close>)
    case (step a s) then show ?case
      apply (subst whileLoop_unroll)
      apply (simp add: run_condition run_bind bind_post_state_eq_bot prod_eq_iff runs_to.rep_eq
                  split: prod.splits exception_or_result_splits)
      apply clarsimp
      subgoal premises prems
        using holds_post_state_combine[OF prems(1,3), where R="\<lambda>x. False"] B
        by (auto simp: holds_post_state_False exception_or_result_nchotomy always_progress.rep_eq)
      done
  qed
  then show "run (whileLoop a) s \<noteq> \<bottom>"
    by (cases "run (whileLoop a) s = Failure") (auto simp: bot_post_state_def)
qed

lemma runs_to_partial_whileLoop_cond_false:
  "(whileLoop I) \<bullet> s ?\<lbrace> \<lambda>r t. \<forall>a. r = Result a \<longrightarrow> \<not> C a t \<rbrace>"
  by (rule runs_to_partial_whileLoop[of "\<lambda>_ _. True"]) simp_all

end

context
  fixes R
  fixes C :: "'a \<Rightarrow> 's \<Rightarrow> bool" and B :: "'a \<Rightarrow> ('e::default, 'a, 's) spec_monad"
    and C' :: "'b \<Rightarrow> 't \<Rightarrow> bool" and B' :: "'b \<Rightarrow> ('f::default, 'b, 't) spec_monad"
  assumes C: "\<And>x s x' s'. R (Result x, s) (Result x', s') \<Longrightarrow> C x s \<longleftrightarrow> C' x' s'"
  assumes B: "\<And>x s x' s'. R (Result x, s) (Result x', s') \<Longrightarrow> C x s \<Longrightarrow> C' x' s' \<Longrightarrow>
    refines (B x) (B' x') s s' R"
  assumes R: "\<And>v s v' s'. R (v, s) (v', s') \<Longrightarrow> (\<exists>x. v = Result x) \<longleftrightarrow> (\<exists>x'. v' = Result x')"
begin

lemma refines_whileLoop_finite_strong:
  assumes x_x': "R (Result x, s) (Result x', s')"
  shows "refines (whileLoop_finite C B x) (whileLoop_finite C' B' x') s s'
    (\<lambda>(r, s) (r', s'). (\<forall>v. r = Result v \<longrightarrow> (\<exists>v'. r' = Result v' \<and> \<not> C v s \<and> \<not> C' v' s')) \<and>
     R (r, s) (r', s'))"
    (is "refines _ _ _ _ ?R")
proof -
  let ?P = "\<lambda>p. \<forall>x s x' s'. R (Result x, s) (Result x', s') \<longrightarrow>
    refines (p x) (whileLoop_finite C' B' x') s s' ?R"

  have "?P (whileLoop_finite C B)"
    unfolding whileLoop_finite_def[of C B]
  proof (rule lfp_ordinal_induct[OF mono_whileLoop_functional], intro allI impI)
    fix S x s x' s' assume S: "?P S" and x_x': "R (Result x, s) (Result x', s')"
    from x_x' show
      "refines (condition (C x) (B x \<bind> S) (return x)) (whileLoop_finite C' B' x') s s' ?R"
      by (subst whileLoop_finite_unfold)
         (auto dest: R simp: C[OF x_x'] refines_condition_iff
               intro!: refines_bind'[OF refines_mono[OF _ B[OF x_x']]] S[rule_format])
  qed (simp add: refines_Sup1)
  with x_x' show ?thesis by simp
qed

lemma refines_whileLoop_finite:
  assumes x_x': "R (Result x, s) (Result x', s')"
  shows "refines (whileLoop_finite C B x) (whileLoop_finite C' B' x') s s' R"
  by (rule refines_mono[OF _ refines_whileLoop_finite_strong, OF _ x_x']) simp

lemma whileLoop_succeeds_terminates_of_refines:
  assumes "run (whileLoop C' B' x') s' \<noteq> \<top>"
  shows "R (Result x, s) (Result x', s') \<Longrightarrow> run (whileLoop C B x) s \<noteq> Failure"
proof (use assms in \<open>induction arbitrary: x s rule: whileLoop_ne_top_induct\<close>)
  case (step a' s' a s)

  show ?case
  proof (rule whileLoop_ne_Failure)
    assume "C a s"
    with C[of a s a' s'] step.prems have "C' a' s'" by simp

    show "B a \<bullet> s \<lbrace> \<lambda>x s. \<forall>a. x = Result a \<longrightarrow> run (whileLoop C B a) s \<noteq> Failure \<rbrace>"
      using step.IH[OF \<open>C' a' s'\<close>] B[OF step.prems \<open>C a s\<close> \<open>C' a' s'\<close>]
      by (rule runs_to_refines) (metis R)
  qed
qed

lemma refines_whileLoop_strong:
  assumes x_x': "R (Result x, s) (Result x', s')"
  shows "refines (whileLoop C B x) (whileLoop C' B' x') s s'
      (\<lambda>(r, s) (r', s'). (\<forall>v. r = Result v \<longrightarrow> (\<exists>v'. r' = Result v' \<and> \<not> C v s \<and> \<not> C' v' s')) \<and>
     R (r, s) (r', s'))"
  apply (cases "run (whileLoop C' B' x') s' = Failure")
  subgoal by (simp add: refines.rep_eq )
  subgoal
    using
      whileLoop_succeeds_terminates_of_refines[OF _ x_x']
      refines_whileLoop_finite_strong[OF x_x']
    by (simp add: refines.rep_eq whileLoop_finite_eq_whileLoop top_post_state_def)
  done

lemma refines_whileLoop:
  assumes x_x': "R (Result x, s) (Result x', s')"
  shows "refines (whileLoop C B x) (whileLoop C' B' x') s s' R"
  by (rule refines_mono[OF _ refines_whileLoop_strong, OF _ x_x']) simp

end

lemma runs_to_whileLoop_res':
  assumes R: "wf R"
  assumes *: "I a s"
  assumes P_Result: "\<And>a s. \<not> C a s \<Longrightarrow> I a s \<Longrightarrow> P (Result a) s"
  assumes B: "\<And>a s. C a s \<Longrightarrow> I a s \<Longrightarrow>
    B a  \<bullet> s \<lbrace>\<lambda>r t. (\<forall>b. r = Result b \<longrightarrow> I b t \<and> ((b, t), (a, s)) \<in> R)\<rbrace>"
  shows "(whileLoop C B a::('a, 's) res_monad) \<bullet> s \<lbrace>P\<rbrace>"
  apply (rule runs_to_whileLoop[OF R, where I = "\<lambda>Exception _ \<Rightarrow> (\<lambda>_. False) | Result v \<Rightarrow> I v"])
  subgoal using * by auto
  subgoal using P_Result by auto
  subgoal by auto
  subgoal for a b by (rule B[of a b, THEN runs_to_weaken]) auto
  done

lemma runs_to_whileLoop_res:
  assumes B: "\<And>a s. C a s \<Longrightarrow> I a s \<Longrightarrow>
    B a  \<bullet> s \<lbrace>\<lambda>Res r t. I r t \<and> ((r, t), (a, s)) \<in> R\<rbrace>"
  assumes P_Result: "\<And>a s. I a s \<Longrightarrow> \<not> C a s \<Longrightarrow> P a s"
  assumes R: "wf R"
  assumes *: "I a s"
  shows "(whileLoop C B a::('a, 's) res_monad) \<bullet> s \<lbrace>\<lambda>Res r. P r\<rbrace>"
  apply (rule runs_to_whileLoop_res' [where R = R and I = I and B = B,  OF R *])
  using B P_Result by auto

lemma runs_to_whileLoop_variant_res:
  assumes I: "\<And>r s c. I r s c \<Longrightarrow>
    C r s \<Longrightarrow> (B r) \<bullet> s \<lbrace> \<lambda>Res q t. \<exists>c'. I q t c' \<and> (c', c) \<in> R \<rbrace>"
  assumes Q: "\<And>r s c. I r s c \<Longrightarrow> \<not> C r s \<Longrightarrow> Q r s"
  assumes R: "wf R"
  shows "I r s c \<Longrightarrow> (whileLoop C B r::('a, 's) res_monad) \<bullet> s \<lbrace>\<lambda>Res r. Q r \<rbrace>"
proof (induction arbitrary: r s rule: wf_induct[OF R])
  case (1 c) show ?case
    apply (subst whileLoop_unroll)
    supply I[where c=c, runs_to_vcg]
    apply (runs_to_vcg)
    subgoal by (simp add: 1)
    subgoal using 1 by simp
    subgoal using Q 1 by blast
    done
qed

lemma runs_to_whileLoop_inc_res:
  assumes *: "\<And>i. i < M \<Longrightarrow> (B (F i)) \<bullet> (S i) \<lbrace> \<lambda>Res r' t'. r' = (F (Suc i)) \<and> t' = (S (Suc i)) \<rbrace>"
      and [simp]: "\<And>i. i \<le> M \<Longrightarrow> C (F i) (S i) \<longleftrightarrow> i < M"
      and [simp]: "i = F 0" "si = S 0" "t = F M" "st = S M"
    shows "(whileLoop C B i::('a, 's) res_monad) \<bullet> si \<lbrace> \<lambda>Res r' t'. r' = t \<and> t' = st \<rbrace>"
  apply (rule runs_to_whileLoop_variant_res[where I="\<lambda>r t i. r = F i \<and> t = S i \<and> i \<le> M" and c=0,
    OF _ _ wf_nat_bound[of M]])
  apply simp_all
  apply (rule runs_to_weaken[OF *])
   apply auto
  done

lemma runs_to_whileLoop_dec_res:
  assumes *: "\<And>i::nat. i > 0 \<Longrightarrow> i \<le> M \<Longrightarrow>
        (B (F i)) \<bullet> (S i) \<lbrace> \<lambda>Res r' t'. r' = (F (i - 1)) \<and> t' = (S (i - 1)) \<rbrace>"
      and [simp]: "\<And>i. C (F i) (S i) \<longleftrightarrow> i > 0"
      and [simp]: "i = F M" "si = S M" "t = F 0" "st = S 0"
    shows "(whileLoop C B i::('a, 's) res_monad) \<bullet> si \<lbrace> \<lambda>Res r' t'. r' = t \<and> t' = st \<rbrace>"
  apply (rule runs_to_whileLoop_variant_res[where I="\<lambda>r t i. r = F i \<and> t = S i \<and> i \<le> M" and c=M,
        OF _ _ wf_measure[of "\<lambda>x. x"]])
    apply (fastforce intro!: runs_to_weaken[OF *])+
  done


lemma runs_to_whileLoop_exn:
  assumes R: "wf R"
  assumes *: "I (Result a) s"
  assumes P_Result: "\<And>a s. \<not> C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> P (Result a) s"
  assumes P_Exn: "\<And>a s. I (Exn a) s \<Longrightarrow> P (Exn a) s"
  assumes B: "\<And>a s. C a s \<Longrightarrow> I (Result a) s \<Longrightarrow>
    B a  \<bullet> s \<lbrace>\<lambda>r t. I r t \<and> (\<forall>b. r = Result b \<longrightarrow> ((b, t), (a, s)) \<in> R)\<rbrace>"
  shows "whileLoop C B a \<bullet> s \<lbrace>P\<rbrace>"
  apply (rule runs_to_whileLoop[where I = I, OF R *])
  subgoal using P_Result by auto
  subgoal using P_Exn by (auto simp add: default_option_def Exn_def)
  subgoal using B by blast
  done

lemma runs_to_whileLoop_exn':
  assumes B: "\<And>a s. I (Result a) s \<Longrightarrow> C a s \<Longrightarrow>
    B a  \<bullet> s \<lbrace>\<lambda>r t. I r t \<and> (\<forall>b. r = Result b \<longrightarrow> ((b, t), (a, s)) \<in> R)\<rbrace>"
  assumes P_Result: "\<And>a s.  I (Result a) s  \<Longrightarrow> \<not> C a s \<Longrightarrow> P (Result a) s"
  assumes P_Exn: "\<And>a s. I (Exn a) s \<Longrightarrow> P (Exn a) s"
  assumes R: "wf R"
  assumes *: "I (Result a) s"
  shows "whileLoop C B a \<bullet> s \<lbrace>P\<rbrace>"
  by (rule runs_to_whileLoop_exn[where R=R and I=I and B=B and C=C and P=P,
        OF R * P_Result P_Exn B])

lemma runs_to_partial_whileLoop_res:
  assumes *: "I a s"
  assumes P_Result: "\<And>a s. \<not> C a s \<Longrightarrow> I a s \<Longrightarrow> P (Result a) s"
  assumes B: "\<And>a s. C a s \<Longrightarrow> I a s \<Longrightarrow>
    (B a) \<bullet> s ?\<lbrace>\<lambda>r t. (\<forall>b. r = Result b \<longrightarrow> I b t)\<rbrace>"
  shows "(whileLoop C B a::('a, 's) res_monad) \<bullet> s ?\<lbrace>P\<rbrace>"
  apply (rule runs_to_partial_whileLoop[where I = "\<lambda>Exception _ \<Rightarrow> (\<lambda>_. False) | Result v \<Rightarrow> I v"])
  subgoal using * by auto
  subgoal using P_Result by auto
  subgoal by auto
  subgoal by (rule B[THEN runs_to_partial_weaken]) auto
  done

lemma runs_to_partial_whileLoop_exn:
  assumes *: "I (Result a) s"
  assumes P_Result: "\<And>a s. \<not> C a s \<Longrightarrow> I (Result a) s \<Longrightarrow> P (Result a) s"
  assumes P_Exn: "\<And>a s. I (Exn a) s \<Longrightarrow> P (Exn a) s"
  assumes B: "\<And>a s. C a s \<Longrightarrow> I (Result a) s \<Longrightarrow>
    (B a) \<bullet> s ?\<lbrace>\<lambda>r t. I r t\<rbrace>"
  shows "whileLoop C B a \<bullet> s ?\<lbrace>P\<rbrace>"
  apply (rule runs_to_partial_whileLoop[where I = I, OF *])
  subgoal using P_Result by auto
  subgoal using P_Exn by (auto simp add: default_option_def Exn_def)
  subgoal using B by blast
  done

notation (output)
  whileLoop  (\<open>(\<open>notation=\<open>prefix whileLoop\<close>\<close>whileLoop (_)//  (_))\<close> [1000, 1000] 1000)

lemma whileLoop_mono: "b \<le> b' \<Longrightarrow> whileLoop c b i \<le> whileLoop c b' i"
  unfolding whileLoop_def
  by (simp add: gfp_mono le_funD le_funI mono_bind mono_condition)

lemma whileLoop_finite_mono: "b \<le> b' \<Longrightarrow> whileLoop_finite c b i \<le> whileLoop_finite c b' i"
  unfolding whileLoop_finite_def
  by (simp add: le_funD le_funI lfp_mono mono_bind mono_condition)

lemma monotone_whileLoop_le[partial_function_mono]:
  "(\<And>x. monotone R (\<le>) (\<lambda>f. b f x)) \<Longrightarrow> monotone R (\<le>) (\<lambda>f. whileLoop c (b f) i)"
  using whileLoop_mono unfolding monotone_def
  by (metis le_fun_def)

lemma monotone_whileLoop_ge[partial_function_mono]:
  "(\<And>x. monotone R (\<ge>) (\<lambda>f. b f x)) \<Longrightarrow> monotone R (\<ge>) (\<lambda>f. whileLoop c (b f) i)"
  using whileLoop_mono unfolding monotone_def
  by (metis le_fun_def)

lemma monotone_whileLoop_finite_le[partial_function_mono]:
  "(\<And>x. monotone R (\<le>) (\<lambda>f. b f x)) \<Longrightarrow> monotone R (\<le>) (\<lambda>f. whileLoop_finite c (b f) i)"
  using whileLoop_finite_mono unfolding monotone_def
  by (metis le_fun_def)

lemma monotone_whileLoop_finite_ge[partial_function_mono]:
  "(\<And>x. monotone R (\<ge>) (\<lambda>f. b f x)) \<Longrightarrow> monotone R (\<ge>) (\<lambda>f. whileLoop_finite c (b f) i)"
  using whileLoop_finite_mono unfolding monotone_def
  by (metis le_fun_def)

lemma run_whileLoop_le_invariant_cong:
  assumes I: "I (Result i) s"
  assumes invariant: "\<And>r s. C r s \<Longrightarrow> I (Result r) s \<Longrightarrow> B r \<bullet> s ?\<lbrace>I\<rbrace>"
  assumes C: "\<And>r s. I (Result r) s \<Longrightarrow> C r s = C' r s"
  assumes B: "\<And>r s. C r s \<Longrightarrow> I (Result r) s \<Longrightarrow> run (B r) s = run (B' r) s"
  shows "run (whileLoop C B i) s \<le> run (whileLoop C' B' i) s"
  unfolding le_run_refines_iff
  apply (rule refines_mono[of "\<lambda>a b. a = b \<and> I (fst a) (snd a)"])
  apply simp
  apply (rule refines_whileLoop)
  subgoal using C by auto
  subgoal for x s y t using invariant[of x s] B[of x t]
    by (cases "run (B' y) t")
       (auto simp add: refines.rep_eq runs_to_partial_alt runs_to.rep_eq split_beta')
  subgoal by simp
  subgoal using I by simp
  done

lemma run_whileLoop_invariant_cong:
  assumes I: "I (Result i) s"
  assumes invariant: "\<And>r s. C r s \<Longrightarrow> I (Result r) s \<Longrightarrow> B r \<bullet> s ?\<lbrace>I\<rbrace>"
  assumes C: "\<And>r s. I (Result r) s \<Longrightarrow> C r s = C' r s"
  assumes B: "\<And>r s. C r s \<Longrightarrow> I (Result r) s \<Longrightarrow> run (B r) s = run (B' r) s"
  shows "run (whileLoop C B i) s = run (whileLoop C' B' i) s"
proof (rule antisym)
  from I invariant C B
  show "run (whileLoop C B i) s \<le> run (whileLoop C' B' i) s"
    by (rule run_whileLoop_le_invariant_cong)
next
  from B invariant have invariant_sym: "\<And>r s. C r s \<Longrightarrow> I (Result r) s \<Longrightarrow> B' r \<bullet> s ?\<lbrace>I\<rbrace>"
    by (simp add: runs_to_partial.rep_eq)
  show "run (whileLoop C' B' i) s \<le> run (whileLoop C B i) s"
    apply (rule run_whileLoop_le_invariant_cong
      [where I=I, OF I invariant_sym C[symmetric] B[symmetric]])
    apply (auto simp add: C)
    done
qed

lemma whileLoop_cong:
  assumes C: "\<And>r s. C r s = C' r s"
  assumes B: "\<And>r s. C r s \<Longrightarrow> run (B r) s = run (B' r) s"
  shows "whileLoop C B = whileLoop C' B'"
proof (rule ext)
  fix i
  show "whileLoop C B i = whileLoop C' B' i"
  proof (rule spec_monad_ext)
    fix s

    show "run (whileLoop C B i) s = run (whileLoop C' B' i) s"
      by (rule run_whileLoop_invariant_cong[where I = "\<lambda>_ _. True"])
         (simp_all add: C B)
  qed
qed

lemma refines_whileLoop':
  assumes C: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<longleftrightarrow> C' b t"
    and B:
      "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<Longrightarrow> C' b t \<Longrightarrow> refines (B a) (B' b) s t R"
    and I: "R (Result I, s) (Result I', s')"
    and R:
      "\<And>r s r' s'. R (r, s) (r', s') \<Longrightarrow> rel_exception_or_result (\<lambda>_ _ . True) (\<lambda>_ _ . True) r r'"
  shows "refines (whileLoop C B I) (whileLoop C' B' I') s s'
    (\<lambda>(r, s) (r', s'). (\<forall>v. r = Result v \<longrightarrow> (\<exists>v'. r' = Result v' \<and> \<not> C v s \<and> \<not> C' v' s')) \<and>
     R (r, s) (r', s'))"
  apply (rule refines_whileLoop_strong)
  subgoal using C by simp
  subgoal using B by simp
  subgoal for v s v' s' using R[of v s v' s'] by (auto elim!: rel_exception_or_result.cases)
  subgoal using I by simp
  done

lemma rel_spec_whileLoop':
  assumes C: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<longleftrightarrow> C' b t"
    and B: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<Longrightarrow> C' b t \<Longrightarrow> rel_spec (B a) (B' b) s t R"
    and I: "R (Result I, s) (Result I', s')"
    and R: "\<And>r s r' s'. R (r, s) (r', s') \<Longrightarrow> rel_exception_or_result (\<lambda>_ _ . True) (\<lambda>_ _ . True) r r'"
  shows "rel_spec (whileLoop C B I) (whileLoop C' B' I') s s'
    (\<lambda>(r, s) (r', s'). (\<forall>v. r = Result v \<longrightarrow> (\<exists>v'. r' = Result v' \<and> \<not> C v s \<and> \<not> C' v' s')) \<and>
     R (r, s) (r', s'))"
  using C B I R
  unfolding rel_spec_iff_refines
  apply (intro conjI)
  subgoal
    by (intro refines_whileLoop') auto
  subgoal
    apply (intro refines_mono[OF _ refines_whileLoop'[where R="R\<inverse>\<inverse>"]])
    subgoal by simp (smt (verit) Exception_eq_Result rel_exception_or_result.cases)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by simp (smt (verit, best) rel_exception_or_result.simps)
    done
  done

lemma rel_spec_whileLoop:
  assumes C: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<longleftrightarrow> C' b t"
    and B: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<Longrightarrow> C' b t \<Longrightarrow> rel_spec (B a) (B' b) s t R"
    and I: "R (Result I, s) (Result I', s')"
    and R: "\<And>r s r' s'. R (r, s) (r', s') \<Longrightarrow> rel_exception_or_result (\<lambda>_ _ . True) (\<lambda>_ _ . True) r r'"
  shows "rel_spec (whileLoop C B I) (whileLoop C' B' I') s s' R"
  by (rule rel_spec_mono[OF _ rel_spec_whileLoop'[OF assms]]) auto

lemma do_whileLoop_combine:
  "do { x1 \<leftarrow> body x0; whileLoop P body x1 } =
    do {
      (b, y) \<leftarrow> whileLoop (\<lambda>(b, x) s. b \<longrightarrow> P x s) (\<lambda>(b, x). do { y \<leftarrow> body x; return (True, y) })
        (False, x0);
      return y
    }"
  apply (subst (2) whileLoop_unroll)
  apply (simp add: bind_assoc)
  apply (rule arg_cong[where f="bind _", OF ext])
  apply (subst bind_return[symmetric])
  apply (rule rel_spec_eqD)
  apply (rule rel_spec_bind_bind[where
    Q="rel_prod (rel_exception_or_result (=) (\<lambda>x (b, y). b = True \<and> x = y)) (=)"])
  subgoal for x s
    apply (rule rel_spec_whileLoop)
    subgoal by auto
    subgoal 
      apply (simp split: prod.splits) [1]
      apply (subst bind_return[symmetric])
      apply clarify
      apply (rule rel_spec_bind_bind[where Q="(=)"])
          apply (simp_all add: rel_spec_refl)
      done
    by (auto simp: rel_exception_or_result.simps split: prod.splits)
     apply (simp_all split: prod.splits)
  done

lemma rel_spec_whileLoop_res:
  assumes C: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<longleftrightarrow> C' b t"
    and B: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<Longrightarrow> C' b t \<Longrightarrow> rel_spec (B a) (B' b) s t R"
    and I: "R (Result I, s) (Result I', s')"
  shows "rel_spec ((whileLoop C B I)::('a, 's) res_monad) ((whileLoop C' B' I')::('b, 't) res_monad) s s' R"
  by (rule rel_spec_whileLoop[OF C B I]) auto

lemma rel_spec_monad_whileLoop:
  assumes init: "R I I'"
  assumes cond: "\<And>x y. R x y \<Longrightarrow> (rel_fun S (=)) (C x) (C' y)"
  assumes body: "\<And>x y. R x y \<Longrightarrow> rel_spec_monad S (rel_exception_or_result E R) (B x) (B' y)"
  shows "rel_spec_monad S (rel_exception_or_result E R) (whileLoop C B I) (whileLoop C' B' I')"
  apply (clarsimp simp add: rel_spec_monad_iff_rel_spec)
  apply (rule rel_spec_whileLoop)
  subgoal for s t x s' y t' using cond by (simp add: rel_fun_def)
  subgoal for s t x s' y t' using body[of x y] by (simp add: rel_spec_monad_iff_rel_spec)
  subgoal using init by simp
  subgoal by (auto elim!: rel_exception_or_result.cases)
  done

lemma rel_spec_monad_whileLoop_res':
  assumes init: "R I I'"
  assumes cond: "\<And>x y. R x y \<Longrightarrow> (rel_fun S (=)) (C x) (C' y)"
  assumes body: "\<And>x y. R x y \<Longrightarrow> rel_spec_monad S (\<lambda>Res x Res y. R x y) (B x) (B' y)"
  shows "rel_spec_monad S (\<lambda>Res x Res y. R x y)
            ((whileLoop C B I)::('a, 's) res_monad)
            ((whileLoop C' B' I')::('b, 't) res_monad)"
  using assms
  by (auto intro: rel_spec_monad_whileLoop simp add: rel_exception_or_result_Res_val)

lemma rel_spec_monad_whileLoop_res:
  assumes init: "R I I'"
  assumes cond: "rel_fun R (rel_fun S (=)) C C'"
  assumes body: "rel_fun R (rel_spec_monad S (\<lambda>Res x Res y. R x y)) B B'"
  shows "rel_spec_monad S (\<lambda>Res x Res y. R x y)
            ((whileLoop C B I)::('a, 's) res_monad)
            ((whileLoop C' B' I')::('b, 't) res_monad)"
  using assms
  by (auto intro: rel_spec_monad_whileLoop_res' simp add: rel_fun_def)

lemma runs_to_whileLoop_finite_exn:
  assumes B: "\<And>r s. I (Result r) s \<Longrightarrow> C r s \<Longrightarrow> (B r) \<bullet> s \<lbrace> I \<rbrace>"
  assumes Qr: "\<And>r s. I (Result r) s \<Longrightarrow> \<not> C r s \<Longrightarrow> Q (Result r) s"
  assumes Ql: "\<And>e s. I (Exn e) s \<Longrightarrow> Q (Exn e) s"
  assumes I: "I (Result r) s"
  shows "(whileLoop_finite C B r) \<bullet> s \<lbrace> Q \<rbrace>"
  using assms by (intro runs_to_whileLoop_finite[of I]) (auto simp: Exn_def default_option_def)

lemma runs_to_whileLoop_finite_res:
  assumes B: "\<And>r s. I r s \<Longrightarrow> C r s \<Longrightarrow> (B r) \<bullet> s \<lbrace>\<lambda>Res r. I r \<rbrace>"
  assumes Q: "\<And>r s. I r s \<Longrightarrow> \<not> C r s \<Longrightarrow> Q r s"
  assumes I: "I r s"
  shows "((whileLoop_finite C B r)::('a, 's) res_monad) \<bullet> s \<lbrace>\<lambda>Res r. Q r \<rbrace>"
  using assms by (intro runs_to_whileLoop_finite[of "\<lambda>Res r. I r"]) simp_all

lemma runs_to_whileLoop_eq_whileLoop_finite:
  "run (whileLoop C B r) s \<noteq> \<top> \<Longrightarrow>
    (whileLoop C B r) \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (whileLoop_finite C B r) \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: whileLoop_finite_eq_whileLoop runs_to.rep_eq)

lemma whileLoop_finite_cond_fail:
    "\<not> C r s \<Longrightarrow> (run (whileLoop_finite C B r) s) = (run (return r) s)"
  apply (subst whileLoop_finite_unfold)
  apply simp
  done

lemma runs_to_whileLoop_finite_cond_fail:
  "\<not> C r s \<Longrightarrow> (whileLoop_finite C B r) \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (return r) \<bullet> s \<lbrace> Q \<rbrace>"
  apply (subst whileLoop_finite_unfold)
  apply (simp add: runs_to.rep_eq)
  done

lemma runs_to_whileLoop_cond_fail:
  "\<not> C r s \<Longrightarrow> (whileLoop C B r) \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> (return r) \<bullet> s \<lbrace> Q \<rbrace>"
  apply (subst whileLoop_unroll)
  apply (simp add: runs_to.rep_eq)
  done

lemma whileLoop_finite_unfold':
  "(whileLoop_finite C B r) =
     ((condition (C r) (B r) (return r)) >>= (whileLoop_finite C B))"
  apply (rule spec_monad_ext)
  apply (subst (1) whileLoop_finite_unfold)
  subgoal for s
    apply (cases "C r s")
    subgoal by (simp add: run_bind)
    subgoal by (simp add: whileLoop_finite_cond_fail run_bind)
    done
  done

lemma runs_to_whileLoop_unroll:
  assumes "\<not> C r s \<Longrightarrow> P r s"
  assumes [runs_to_vcg]: "C r s \<Longrightarrow> (B r) \<bullet> s \<lbrace> \<lambda>Res r t. ((whileLoop C B r) \<bullet> t \<lbrace>\<lambda>Res r. P r \<rbrace>) \<rbrace>"
  shows "(whileLoop C B r) \<bullet> s \<lbrace>\<lambda>Res r. P r \<rbrace>"
  using assms(1)
  by (subst whileLoop_unroll) runs_to_vcg

lemma runs_to_partial_whileLoop_unroll:
  assumes "\<not> C r s \<Longrightarrow> P r s"
  assumes "C r s \<Longrightarrow> (B r) \<bullet> s ?\<lbrace> \<lambda>Res r t. ((whileLoop C B r) \<bullet> t ?\<lbrace>\<lambda>Res r. P r \<rbrace>) \<rbrace>"
  shows "(whileLoop C B r) \<bullet> s ?\<lbrace>\<lambda>Res r. P r \<rbrace>"
  using assms
  by (subst whileLoop_unroll) runs_to_vcg


lemma runs_to_whileLoop_unroll_exn:
  assumes "\<not> C r s \<Longrightarrow> P (Result r) s"
  assumes [runs_to_vcg]: "C r s \<Longrightarrow> (B r) \<bullet> s \<lbrace> \<lambda>r t.
    (\<forall>a. r = Result a \<longrightarrow> ((whileLoop C B a) \<bullet> t \<lbrace> P \<rbrace>)) \<and>
    (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t) \<rbrace>"
  shows "(whileLoop C B r) \<bullet> s \<lbrace>\<lambda>r s'. P r s' \<rbrace>"
  using assms(1)
  by (subst whileLoop_unroll) (runs_to_vcg, auto simp: Exn_def default_option_def)


lemma runs_to_partial_whileLoop_unroll_exn:
  assumes "\<not> C r s \<Longrightarrow> P (Result r) s"
  assumes "C r s \<Longrightarrow> (B r) \<bullet> s ?\<lbrace> \<lambda>r t.
    (\<forall>a. r = Result a \<longrightarrow> ((whileLoop C B a) \<bullet> t ?\<lbrace> P \<rbrace>)) \<and>
    (\<forall>e. r = Exn e \<longrightarrow> P (Exn e) t) \<rbrace>"
  shows "(whileLoop C B r) \<bullet> s ?\<lbrace>\<lambda>r s'. P r s' \<rbrace>"
  using assms
  by (subst whileLoop_unroll) runs_to_vcg

lemma refines_whileLoop_exn:
  assumes C: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<longleftrightarrow> C' b t"
    and B: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<Longrightarrow> C' b t \<Longrightarrow> refines (B a) (B' b) s t R"
    and I: "R (Result I, s) (Result I', s')"
    and R1: "\<And>a s b t. R (Exn a, s) (Result b, t) \<Longrightarrow> False"
    and R2: "\<And>a s b t. R (Result a, s) (Exn b, t) \<Longrightarrow> False"
  shows "refines (whileLoop C B I) (whileLoop C' B' I') s s' R"
proof -
  have ref: "refines (whileLoop C B I) (whileLoop C' B' I') s s'
         (\<lambda>(r, s) (r', s'). (\<forall>v. r = Result v \<longrightarrow> (\<exists>v'. r' = Result v' \<and> \<not> C v s \<and> \<not> C' v' s')) \<and> 
          R (r, s) (r', s'))"

    apply (rule refines_whileLoop' [OF C])
    subgoal by assumption
    subgoal by (rule B)
    subgoal by (rule I)
    subgoal using R1 R2
      by (auto simp add: rel_exception_or_result.simps Exn_def default_option_def)
        (metis default_option_def exception_or_result_cases not_None_eq)+
    done
  show ?thesis
    apply (rule refines_mono [OF _ ref])
    apply (auto)
    done
qed

lemma refines_whileLoop'':
  assumes C: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<longleftrightarrow> C' b t"
    and B: "\<And>a s b t. R (Result a, s) (Result b, t) \<Longrightarrow> C a s \<Longrightarrow> C' b t \<Longrightarrow> refines (B a) (B' b) s t R"
    and I: "R (Result I, s) (Result I', s')"
    and R: "\<And>r s r' s'. R (r, s) (r', s') \<Longrightarrow> rel_exception_or_result (\<lambda>_ _ . True) (\<lambda>_ _ . True) r r'"
  shows "refines (whileLoop C B I) (whileLoop C' B' I') s s' R"
proof -
  have "refines (whileLoop C B I) (whileLoop C' B' I') s s'
    (\<lambda>(r, s) (r', s'). (\<forall>v. r = Result v \<longrightarrow> (\<exists>v'. r' = Result v' \<and> \<not> C v s \<and> \<not> C' v' s')) \<and> 
     R (r, s) (r', s'))"
    by (rule refines_whileLoop' [OF C B I R])
  then show ?thesis
    apply (rule refines_weaken)
    apply auto
    done
qed

lemma rel_spec_monad_whileLoop_exn:
  assumes init: "R I I'"
  assumes cond: "\<And>x y. R x y \<Longrightarrow> (rel_fun S (=)) (C x) (C' y)"
  assumes body: "\<And>x y. R x y \<Longrightarrow> rel_spec_monad S (rel_xval E R) (B x) (B' y)"
  shows "rel_spec_monad S (rel_xval E R) (whileLoop C B I) (whileLoop C' B' I')"
  unfolding rel_xval_rel_exception_or_result_conv
  by (rule rel_spec_monad_whileLoop [OF init cond body [simplified rel_xval_rel_exception_or_result_conv]])

lemma refines_whileLoop_guard_right: 
  assumes "\<And>x s x' s'. R (Result x, s) (Result x', s') \<Longrightarrow> G' x' s' \<Longrightarrow> C x s = C' x' s'"
  assumes "\<And>x s x' s'. R (Result x, s) (Result x', s') \<Longrightarrow> C x s \<Longrightarrow> C' x' s' \<Longrightarrow> G' x' s' \<Longrightarrow> refines (B x) (B' x') s s' R" 
  assumes "\<And>v s v' s'. R (v, s) (v', s') \<Longrightarrow> (\<exists>x. v = Result x) = (\<exists>x'. v' = Result x')"
  assumes "R (Result x, s) (Result x', s')"
  assumes "G s' = G' x' s'"
  shows "refines (whileLoop C B x) (guard G \<bind> (\<lambda>_. whileLoop C' (\<lambda>r. do {res <- B' r; guard (G' res); return res}) x')) s s' R"
  apply (rule refines_bind_guard_right)
  apply (rule refines_mono [where R="\<lambda>(r, s) (q, t). R (r, s) (q, t) \<and> 
                (case q of Exception e \<Rightarrow> True | Result v \<Rightarrow> G' v t)"])
  subgoal by simp
  subgoal
    apply (rule refines_whileLoop)
    subgoal using assms(1) by auto
    subgoal apply (rule  refines_bind_guard_right_end')
      using assms(2)
      by auto
    subgoal using assms(3) by (auto split: exception_or_result_splits)
    subgoal using assms(4,5) by auto
    done
  done

subsection \<open>\<^const>\<open>map_value\<close>\<close>

lemma map_value_lift_state: "map_value f (lift_state R g) = lift_state R (map_value f g)"
  apply transfer
  apply (simp add: map_post_state_eq_lift_post_state lift_post_state_comp
      lift_post_state_Sup image_image OO_def prod_eq_iff rel_prod.simps)
  apply (simp add: ac_simps)
  done

lemma run_map_value[run_spec_monad]: "run (map_value f g) s =
  map_post_state (\<lambda>(v, s). (f v, s)) (run g s)"
  by transfer (auto simp add: apfst_def map_prod_def map_post_state_def
      split: post_state.splits prod.splits)

lemma always_progress_map_value[always_progress_intros]:
  "always_progress g \<Longrightarrow> always_progress (map_value f g)"
  by (simp add: always_progress_def run_map_value)

lemma runs_to_map_value_iff[runs_to_iff]: "map_value f g \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> g \<bullet> s \<lbrace>\<lambda>r t. Q (f r) t\<rbrace>"
  by (auto simp add: runs_to.rep_eq run_map_value split_beta')

lemma runs_to_partial_map_value_iff[runs_to_iff]:
  "map_value f g \<bullet> s ?\<lbrace> Q \<rbrace> \<longleftrightarrow> g \<bullet> s ?\<lbrace>\<lambda>r t. Q (f r) t\<rbrace>"
  by (auto simp add: runs_to_partial.rep_eq run_map_value split_beta')

lemma runs_to_map_value[runs_to_vcg]: "g \<bullet> s \<lbrace>\<lambda>r t. Q (f r) t\<rbrace> \<Longrightarrow> map_value f g \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_map_value_iff)

lemma runs_to_partial_map_value[runs_to_vcg]:
  "g \<bullet> s ?\<lbrace>\<lambda>r t. Q (f r) t\<rbrace> \<Longrightarrow> map_value f g \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (auto simp add: runs_to_partial.rep_eq run_map_value split_beta')

lemma mono_map_value: "g \<le> g' \<Longrightarrow> map_value f g \<le> map_value f g'"
  by transfer (simp add: le_fun_def mono_map_post_state)

lemma monotone_map_value_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. g f') \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. map_value f (g f'))"
  by (auto simp: monotone_def mono_map_value)

lemma monotone_map_value_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. g f') \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. map_value f (g f'))"
  by (auto simp: monotone_def mono_map_value)

lemma map_value_fail[simp]: "map_value f fail = fail"
  by transfer simp

lemma map_value_map_exn_gets[simp]: "map_value (map_exn emb) (gets x) = gets x"
  by (simp add: spec_monad_ext_iff run_map_value)

lemma refines_map_value_right_iff:
  "refines f (map_value m g) s t R \<longleftrightarrow> refines f g s t (\<lambda>(x, s) (y, t). R (x, s) (m y, t))"
  by transfer (simp add: sim_post_state_map_post_state2 split_beta' apfst_def map_prod_def)

lemma refines_map_value_left_iff:
  "refines (map_value m f) g s t R \<longleftrightarrow> refines f g s t (\<lambda>(x, s) (y, t). R (m x, s) (y, t))"
  by transfer (simp add: sim_post_state_map_post_state1 split_beta' apfst_def map_prod_def)

lemma rel_spec_map_value_right_iff:
  "rel_spec f (map_value m g) s t R \<longleftrightarrow> rel_spec f g s t (\<lambda>(x, s) (y, t). R (x, s) (m y, t))"
  by (simp add: rel_spec_iff_refines refines_map_value_right_iff refines_map_value_left_iff
                conversep.simps[abs_def] split_beta')

lemma rel_spec_map_value_left_iff:
  "rel_spec (map_value m f) g s t R \<longleftrightarrow> rel_spec f g s t (\<lambda>(x, s) (y, t). R (m x, s) (y, t))"
  by (simp add: rel_spec_iff_refines refines_map_value_right_iff refines_map_value_left_iff
                conversep.simps[abs_def] split_beta')

lemma refines_map_value_right:
  "refines f (map_value m f) s s (\<lambda>(x, s) (y, t). y = m x \<and> s = t)"
  by (simp add: refines_map_value_right_iff refines_refl)

lemma refines_map_value: 
  assumes "refines f f' s t Q"
  assumes "\<And>r s' w t'. Q (r, s') (w, t') \<Longrightarrow> R (g r, s') (g' w, t')"
  shows "refines (map_value g f) (map_value g' f') s t R"
  apply (simp add: refines_map_value_left_iff refines_map_value_right_iff)
  apply (rule refines_weaken [OF assms(1)])
  using assms(2) by auto

lemma map_value_id[simp]: "map_value (\<lambda>x. x) = (\<lambda>x. x)"
  apply (simp add: fun_eq_iff, intro allI iffI)
  apply (rule spec_monad_eqI)
  apply (rule runs_to_iff)
  done

subsection \<open>\<^const>\<open>liftE\<close>\<close>

lemma run_liftE[run_spec_monad]:
  "run (liftE f) s =
    map_post_state (\<lambda>(v, s). (map_exception_or_result (\<lambda>x. undefined) id v, s)) (run f s)"
  by (simp add: run_map_value liftE_def)

lemma always_progress_liftE[always_progress_intros]:
  "always_progress f \<Longrightarrow> always_progress (liftE f)"
  by (simp add: liftE_def always_progress_intros)

lemma runs_to_liftE_iff:
  "liftE f \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace>\<lambda>r t. Q (map_exception_or_result (\<lambda>x. undefined) id r) t\<rbrace>"
  by (simp add: liftE_def runs_to_map_value_iff)

lemma runs_to_liftE_iff_Res[runs_to_iff]:
  "liftE f \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace> \<lambda>Res r. Q (Result r)\<rbrace>"
  by (auto intro!: runs_to_cong_pred_only simp: runs_to_liftE_iff)

lemma runs_to_liftE':
  "f \<bullet> s \<lbrace>\<lambda>r t. Q (map_exception_or_result (\<lambda>x. undefined) id r) t\<rbrace> \<Longrightarrow> liftE f \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_liftE_iff)

lemma runs_to_liftE[runs_to_vcg]: "f \<bullet> s \<lbrace> \<lambda>Res r. Q (Result r)\<rbrace>  \<Longrightarrow> liftE f \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_liftE_iff_Res)

lemma refines_liftE_left_iff:
  "refines (liftE f) g s t R \<longleftrightarrow>
    refines f g s t (\<lambda>(x, s') (y, t'). \<forall>v. x = Result v \<longrightarrow> R (Result v, s') (y, t'))"
  by (auto simp add: liftE_def refines_map_value_left_iff intro!: refines_cong_cases del: iffI)

lemma refines_liftE_right_iff:
  "refines f (liftE g) s t R \<longleftrightarrow>
    refines f g s t (\<lambda>(x, s') (y, t'). \<forall>v. y = Result v \<longrightarrow> R (x, s') (Result v, t'))"
  by (auto simp add: liftE_def refines_map_value_right_iff intro!: refines_cong_cases del: iffI)

lemma rel_spec_liftE:
  "rel_spec (liftE f) g s t R \<longleftrightarrow>
    rel_spec f g s t (\<lambda>(x, s') (y, t'). \<forall>v. x = Result v \<longrightarrow> R (Result v, s') (y, t'))"
  by (simp add: rel_spec_iff_refines refines_liftE_right_iff refines_liftE_left_iff
                conversep.simps[abs_def] split_beta')

lemma rel_spec_monad_bind_liftE:
  "rel_spec_monad R (\<lambda>Res v1 Res v2. P v1 v2) m n \<Longrightarrow> rel_fun P (rel_spec_monad R Q) f g \<Longrightarrow>
    rel_spec_monad R Q ((liftE m) >>= f) ((liftE n) >>= g)"
  apply (auto intro!: rel_bind_post_state' rel_post_state_refl
    simp: rel_spec_monad_def run_bind run_liftE bind_post_state_map_post_state rel_fun_def)[1]
  subgoal premises prems for s t
    by (rule rel_post_state_weaken[OF prems(1)[rule_format, OF prems(3)]])
       (auto simp add: rel_prod.simps prems(2))
  done

lemma rel_spec_monad_bind_liftE':
  "(\<And>x. rel_spec_monad (=) Q (f x) (g x)) \<Longrightarrow> rel_spec_monad (=) Q (liftE m >>= f) (liftE m >>= g)"
  by (auto simp add: rel_spec_monad_def run_bind run_liftE bind_post_state_map_post_state
           intro!: rel_bind_post_state' rel_post_state_refl)

lemma runs_to_partial_liftE':
  "f \<bullet> s ?\<lbrace>\<lambda>r t. Q (map_exception_or_result (\<lambda>x. undefined) id r) t\<rbrace> \<Longrightarrow> liftE f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: runs_to_partial.rep_eq run_liftE split_beta')

lemma runs_to_partial_liftE[runs_to_vcg]:
  assumes [runs_to_vcg]: "f \<bullet> s ?\<lbrace> \<lambda>Res r. Q (Result r)\<rbrace>" shows "liftE f \<bullet> s ?\<lbrace> Q \<rbrace>"
  supply runs_to_partial_liftE'[runs_to_vcg] by runs_to_vcg

lemma mono_lifE: "f \<le> f' \<Longrightarrow> liftE f  \<le> liftE f'"
  unfolding liftE_def by (rule mono_map_value)

lemma monotone_liftE_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. liftE (f f'))"
  unfolding liftE_def by (rule monotone_map_value_le)

lemma monotone_liftE_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. liftE (f f'))"
  unfolding liftE_def by (rule monotone_map_value_ge)

lemma bind_handle_liftE: "bind_handle (liftE f) g h = bind f g"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma liftE_top[simp]: "liftE \<top> = \<top>"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_bot[simp]: "liftE bot = bot"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_fail[simp]: "liftE fail = fail"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_return[simp]: "liftE (return x) = return x"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_yield_Exception[simp]:
  "liftE (yield (Exception x)) = skip"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_throw_exception_or_result[simp]:
  "liftE (throw_exception_or_result x) = return undefined"
  by (rule spec_monad_ext) (simp add: run_liftE map_exception_or_result_def)

lemma liftE_get_state[simp]: "liftE (get_state) = get_state"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_set_state[simp]: "liftE (set_state s) = set_state s"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_select[simp]: "liftE (select S) = select S"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_unknown[simp]: "liftE (unknown) = unknown"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_lift_state: "liftE (lift_state R f) = lift_state R (liftE f)"
  unfolding liftE_def by (rule map_value_lift_state)

lemma liftE_exec_concrete: "liftE (exec_concrete st f) = exec_concrete st (liftE f)"
  unfolding exec_concrete_def by (rule liftE_lift_state)

lemma liftE_exec_abstract: "liftE (exec_abstract st f) = exec_abstract st (liftE f)"
  unfolding exec_abstract_def by (rule liftE_lift_state)

lemma liftE_assert[simp]: "liftE (assert P) = assert P"
  by (rule spec_monad_ext) (simp add: run_liftE run_assert)

lemma liftE_assume[simp]: "liftE (assume P) = assume P"
  by (rule spec_monad_ext) (simp add: run_liftE run_assume)

lemma liftE_gets[simp]: "liftE (gets f) = gets f"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_guard[simp]: "liftE (guard P) = guard P"
  by (rule spec_monad_ext) (simp add: run_liftE run_guard)

lemma liftE_assert_opt[simp]: "liftE (assert_opt v) = assert_opt v"
  by (rule spec_monad_ext) (auto simp add: run_liftE split: option.splits)

lemma liftE_gets_the[simp]: "liftE (gets_the f) = gets_the f"
  by (rule spec_monad_ext) (auto simp add: run_liftE split: option.splits)

lemma liftE_modify[simp]: "liftE (modify f) = modify f"
  by (rule spec_monad_ext) (simp add: run_liftE)

lemma liftE_bind: "liftE x >>= (\<lambda>a. liftE (y a)) = liftE (x >>= y)"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma bindE_liftE_skip: "liftE (f \<bind> (\<lambda>y. skip)) \<bind> g = liftE f \<bind> (\<lambda>_. g ())"
  by (auto simp add: spec_monad_eq_iff runs_to_iff intro!: arg_cong[where f="runs_to f _"])

lemma liftE_state_select[simp]: "liftE (state_select f) = state_select f"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma liftE_assume_result_and_state[simp]:
  "liftE (assume_result_and_state f) = assume_result_and_state f"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma map_value_map_exn_liftE [simp]:
  "map_value (map_exn emb) (liftE f) = liftE f"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma liftE_condition: "liftE (condition c f g) = condition c (liftE f) (liftE g)"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma liftE_whileLoop: "liftE (whileLoop C B I) = whileLoop C (\<lambda>r. liftE (B r)) I"
  apply (rule rel_spec_eqD)
  apply (subst rel_spec_liftE)
  apply (rule rel_spec_whileLoop)
  subgoal by simp
  apply (subst rel_spec_symm)
  apply (subst rel_spec_liftE)
  apply (simp add: rel_spec_refl)
  apply auto
  done

subsection \<open>\<^const>\<open>try\<close>\<close>

lemma run_try[run_spec_monad]:
  "run (try f) s = map_post_state (\<lambda>(v, s). (unnest_exn v, s)) (run f s)"
  by (simp add: try_def run_map_value)

lemma always_progress_try[always_progress_intros]: "always_progress f \<Longrightarrow> always_progress (try f)"
  by (simp add: try_def always_progress_intros)

lemma runs_to_try[runs_to_vcg]: "f \<bullet> s \<lbrace>\<lambda>r t. Q (unnest_exn r) t\<rbrace> \<Longrightarrow> try f \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: try_def runs_to_map_value)

lemma runs_to_try_iff[runs_to_iff]: "try f \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace>\<lambda>r t. Q (unnest_exn r) t\<rbrace>"
  by (auto simp add: try_def runs_to_iff)

lemma runs_to_partial_try[runs_to_vcg]: "f \<bullet> s ?\<lbrace>\<lambda>r t. Q (unnest_exn r) t\<rbrace> \<Longrightarrow> try f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: try_def runs_to_partial_map_value)

lemma mono_try: "f \<le> f' \<Longrightarrow> try f \<le> try f'"
  unfolding try_def
  by (rule mono_map_value)

lemma monotone_try_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. try (f f'))"
  unfolding try_def by (rule monotone_map_value_le)

lemma monotone_try_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. try (f f'))"
  unfolding try_def by (rule monotone_map_value_ge)

lemma refines_try_right:
  "refines f (try f) s s (\<lambda>(x, s) (y, t). y = unnest_exn x \<and> s = t)"
  by (auto simp add: try_def refines_map_value_right)

subsection \<open>\<^const>\<open>finally\<close>\<close>

lemma run_finally[run_spec_monad]:
  "run (finally f) s = map_post_state (\<lambda>(v, s). (unite v, s)) (run f s)"
  by (simp add: finally_def run_map_value)

lemma always_progress_finally[always_progress_intros]:
  "always_progress f \<Longrightarrow> always_progress (finally f)"
  by (simp add: finally_def always_progress_intros)

lemma runs_to_finally_iff[runs_to_iff]:
  "finally f \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow>
    f \<bullet> s \<lbrace>\<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> Q (Result v) t) \<and> (\<forall>v. r = Exn v \<longrightarrow> Q (Result v) t)\<rbrace>"
  by (auto simp: finally_def runs_to_map_value_iff unite_def
           intro!: arg_cong[where f="runs_to _ _"] split: xval_splits)

lemma runs_to_finally': "f \<bullet> s \<lbrace>\<lambda>r t. Q (unite r) t\<rbrace> \<Longrightarrow> finally f \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: finally_def runs_to_map_value)

lemma runs_to_finally[runs_to_vcg]:
  "f \<bullet> s \<lbrace>\<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> Q (Result v) t) \<and> (\<forall>v. r = Exn v \<longrightarrow> Q (Result v) t)\<rbrace> \<Longrightarrow>
  finally f \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_finally_iff)

lemma runs_to_partial_finally': "f \<bullet> s ?\<lbrace>\<lambda>r t. Q (unite r) t\<rbrace> \<Longrightarrow> finally f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: finally_def runs_to_partial_map_value)

lemma runs_to_partial_finally_iff:
  "finally f \<bullet> s ?\<lbrace> Q \<rbrace> \<longleftrightarrow>
    f \<bullet> s ?\<lbrace>\<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> Q (Result v) t) \<and> (\<forall>v. r = Exn v \<longrightarrow> Q (Result v) t)\<rbrace>"
  by (auto simp: finally_def runs_to_partial_map_value_iff unite_def
           intro!: arg_cong[where f="runs_to_partial _ _"] split: xval_splits)

lemma runs_to_partial_finally[runs_to_vcg]:
  "f \<bullet> s ?\<lbrace>\<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> Q (Result v) t) \<and> (\<forall>v. r = Exn v \<longrightarrow> Q (Result v) t)\<rbrace> \<Longrightarrow>
  finally f \<bullet> s ?\<lbrace> Q \<rbrace>"
  by (simp add: runs_to_partial_finally_iff)

lemma mono_finally: "f \<le> f' \<Longrightarrow> finally f \<le> finally f'"
  unfolding finally_def
  by (rule mono_map_value)

lemma monotone_finally_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. finally (f f'))"
  unfolding finally_def by (rule monotone_map_value_le)

lemma monotone_finally_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. finally (f f'))"
  unfolding finally_def by (rule monotone_map_value_ge)

subsection \<open>\<^const>\<open>catch\<close>\<close>

lemma run_catch[run_spec_monad]:
  "run (f <catch> h) s =
    bind_post_state (run f s)
      (\<lambda>(r, t). case r of Exn e \<Rightarrow> run (h e) t | Result v \<Rightarrow> run (return v) t)"
  apply (simp add: catch_def run_bind_handle)
  apply (rule arg_cong[where f="bind_post_state _", OF ext])
  apply (auto simp add: Exn_def default_option_def split: exception_or_result_splits xval_splits)
  done

lemma always_progress_catch[always_progress_intros]:
  "always_progress f \<Longrightarrow> (\<And>e. always_progress (h e)) \<Longrightarrow> always_progress (f <catch> h)"
  unfolding catch_def
  by (auto intro: always_progress_intros)

lemma runs_to_catch_iff[runs_to_iff]:
  "(f <catch> h) \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow>
    f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow> Q (Result v) t) \<and> (\<forall>e. r = Exn e \<longrightarrow> h e \<bullet> t \<lbrace> Q \<rbrace>)\<rbrace>"
  by (simp add: runs_to.rep_eq run_catch split_beta' ac_simps split: xval_splits prod.splits)

lemma runs_to_catch[runs_to_vcg]:
  "f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow>  Q (Result v) t) \<and>
                 (\<forall>e. r = Exn e \<longrightarrow> h e \<bullet> t \<lbrace> Q \<rbrace>)\<rbrace> \<Longrightarrow>
      (f <catch> h) \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_catch_iff)

lemma runs_to_partial_catch[runs_to_vcg]:
  "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow>  Q (Result v) t) \<and>
                 (\<forall>e. r = Exn e \<longrightarrow> h e \<bullet> t ?\<lbrace> Q \<rbrace>)\<rbrace> \<Longrightarrow>
      (f <catch> h) \<bullet> s ?\<lbrace> Q \<rbrace>"
  unfolding runs_to_partial.rep_eq run_catch
  by (rule holds_partial_bind_post_state)
     (simp add: split_beta' ac_simps split: xval_splits prod.splits)

lemma mono_catch: "f \<le> f' \<Longrightarrow> h \<le> h' \<Longrightarrow> catch f h \<le> catch f' h'"
  unfolding catch_def
  apply (rule mono_bind_handle)
  by (simp_all add: le_fun_def)

lemma monotone_catch_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>e. monotone R (\<le>) (\<lambda>f'. h f' e))
  \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. catch (f f') (h f'))"
  unfolding catch_def
  apply (rule monotone_bind_handle_le)
  by auto

lemma monotone_catch_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>e. monotone R (\<ge>) (\<lambda>f'. h f' e))
  \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. catch (f f') (h f'))"
  unfolding catch_def
  apply (rule monotone_bind_handle_ge)
  by auto

lemma catch_liftE: "catch (liftE g) h = g"
  by (simp add: catch_def bind_handle_liftE)

lemma refines_catch:
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'. Q (Exn e, t) (Exn e', t') \<Longrightarrow>
    refines (h e) (h' e') t t' R"
  assumes lr: "\<And>e v' t t'. Q (Exn e, t) (Result v', t') \<Longrightarrow>
    refines (h e) (return v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exn e', t') \<Longrightarrow>
    refines (return v) (h' e') t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    R (Result v, t) (Result v', t')"
  shows "refines (catch f h) (catch f' h') s s' R"
  unfolding catch_def
  apply (rule refines_bind_handle_bind_handle_exn[OF f])
  subgoal using ll by auto
  subgoal using lr by auto
  subgoal using rl by auto
  subgoal using rr by (auto simp add: refines_yield)
  done

lemma rel_spec_catch:
  assumes f: "rel_spec f f' s s' Q"
  assumes ll: "\<And>e e' t t'. Q (Exn e, t) (Exn e', t') \<Longrightarrow>
    rel_spec (h e) (h' e') t t' R"
  assumes lr: "\<And>e v' t t'. Q (Exn e, t) (Result v', t') \<Longrightarrow>
    rel_spec (h e) (return v') t t' R"
  assumes rl: "\<And>v e' t t'. Q (Result v, t) (Exn e', t') \<Longrightarrow>
    rel_spec (return v) (h' e') t t' R"
  assumes rr: "\<And>v v' t t'. Q (Result v, t) (Result v', t') \<Longrightarrow>
    R (Result v, t) (Result v', t')"
  shows "rel_spec (catch f h) (catch f' h') s s' R"
  using assms by (auto simp: rel_spec_iff_refines intro!: refines_catch)

subsection \<open>\<^const>\<open>check\<close>\<close>

lemma run_check[run_spec_monad]: "run (check e p) s =
  (if (\<exists>x. p s x) then Success ((\<lambda>x. (x, s)) ` (Result ` {x. p s x})) else
    pure_post_state (Exn e, s))"
  by (auto simp add: check_def run_bind)

lemma always_progress_check[always_progress_intros, simp]: "always_progress (check e p)"
  by (auto simp add: always_progress_def run_check)

lemma runs_to_check_iff[runs_to_iff]:
  "(check e p) \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> (if (\<exists>x. p s x) then (\<forall>x. p s x \<longrightarrow> Q (Result x) s) else Q (Exn e) s)"
  by (auto simp add: runs_to.rep_eq run_check)

lemma runs_to_check[runs_to_vcg]:
  "(\<exists>x. p s x \<Longrightarrow> (\<forall>x. p s x \<longrightarrow> Q (Result x) s)) \<Longrightarrow> (\<forall>x. \<not> p s x) \<Longrightarrow> Q (Exn e) s \<Longrightarrow>
    check e p \<bullet> s \<lbrace>Q\<rbrace>"
  by (simp add: runs_to_check_iff)

lemma runs_to_partial_check[runs_to_vcg]:
  "(\<exists>x. p s x \<Longrightarrow> (\<forall>x. p s x \<longrightarrow> Q (Result x) s)) \<Longrightarrow> (\<forall>x. \<not> p s x) \<Longrightarrow> Q (Exn e) s \<Longrightarrow>
    check e p \<bullet> s ?\<lbrace>Q\<rbrace>"
  by (simp add: runs_to_partial.rep_eq run_check)

lemma refines_check_right_ok:
  "Q t a \<Longrightarrow> refines f (g a) s t R \<Longrightarrow> refines f (check q Q >>= g) s t R"
  by (rule refines_bind_right_single[of a t])
     (auto simp add: run_check)

lemma refines_check_right_fail:
  "(\<forall>a. \<not> Q t a) \<Longrightarrow> f \<bullet> s \<lbrace> \<lambda>r s'. R (r, s') (Exn q, t) \<rbrace> \<Longrightarrow> refines f (check q Q >>= g) s t R"
  apply (rule refines_bind_right_runs_to_partialI[OF runs_to_partial_of_runs_to])
  apply (auto simp: runs_to_check_iff Exn_def refines_yield_right_iff)
  done

lemma refines_throwError_check:
  "(\<forall>a. \<not> P t a) \<Longrightarrow> R (Exn r, s) (Exn q, t) \<Longrightarrow>
    refines (throw r) (check q P >>= f) s t R"
  by (intro refines_check_right_fail) auto

lemma refines_condition_neg_check:
  "P s \<longleftrightarrow> (\<forall>a. \<not> Q t a) \<Longrightarrow>
    (P s \<Longrightarrow> \<forall>a. \<not> Q t a \<Longrightarrow> R (Result r, s) (Exn q, t)) \<Longrightarrow>
    (\<And>a. \<not> P s \<Longrightarrow> Q t a \<Longrightarrow> refines f (g a) s t R) \<Longrightarrow>
    refines (condition P (return r) f) (check q Q >>= g) s t R"
 by (intro refines_condition_left)
    (auto intro: refines_check_right_ok refines_check_right_fail)

subsection \<open>\<^const>\<open>ignoreE\<close>\<close>

named_theorems ignoreE_simps \<open>Rewrite rules to push \<^const>\<open>ignoreE\<close> inside.\<close>

lemma ignoreE_eq: "ignoreE f = vmap_value (map_exception_or_result (\<lambda>x. undefined) id) f"
  unfolding ignoreE_def catch_def
  by transfer
     (simp add: fun_eq_iff post_state_eq_iff eq_commute all_comm[where 'a='a]
           split: prod.splits exception_or_result_splits)

lemma run_ignoreE: "run (ignoreE f) s =
  bind_post_state (run f s)
    (\<lambda>(r, t). case r of Exn e \<Rightarrow> \<bottom> | Result v \<Rightarrow> pure_post_state (Result v, t))"
  unfolding ignoreE_def by (simp add: run_catch)

lemma runs_to_ignoreE_iff[runs_to_iff]:
  "(ignoreE f) \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow> f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow>  Q (Result v) t)\<rbrace>"
  unfolding ignoreE_eq runs_to.rep_eq
  by transfer
     (simp add: split_beta' eq_commute prod_eq_iff split: prod.splits exception_or_result_splits)

lemma runs_to_ignoreE[runs_to_vcg]:
  "f \<bullet> s \<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow>  Q (Result v) t)\<rbrace> \<Longrightarrow> (ignoreE f) \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_ignoreE_iff)

lemma liftE_le_iff_le_ignoreE: "liftE f \<le> g \<longleftrightarrow> f \<le> ignoreE g"
  unfolding liftE_def ignoreE_eq[abs_def]
  by transfer (simp add: le_fun_def vmap_post_state_le_iff_le_map_post_state id_def)

lemma runs_to_partial_ignoreE[runs_to_vcg]:
  "f \<bullet> s ?\<lbrace> \<lambda>r t. (\<forall>v. r = Result v \<longrightarrow>  Q (Result v) t)\<rbrace> \<Longrightarrow>
      (ignoreE f) \<bullet> s ?\<lbrace> Q \<rbrace>"
  unfolding ignoreE_def
  apply (runs_to_vcg)
  apply (fastforce simp add: runs_to_partial.rep_eq)
  done

lemma mono_ignoreE: "f \<le> f' \<Longrightarrow> ignoreE f \<le> ignoreE f'"
  unfolding ignoreE_def
  apply (rule mono_catch)
  by simp_all

lemma monotone_ignoreE_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f')
  \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. ignoreE (f f'))"
  unfolding ignoreE_def
  apply (rule monotone_catch_le)
  by simp_all

lemma monotone_ignoreE_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f')
  \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. ignoreE (f f'))"
  unfolding ignoreE_def
  apply (rule monotone_catch_ge)
  by simp_all

lemma ignoreE_liftE [simp]: "ignoreE (liftE f) = f"
  by (simp add: catch_liftE ignoreE_def)

lemma ignoreE_top[simp]: "ignoreE \<top> = \<top>"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_bot[simp]: "ignoreE bot = bot"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_fail[simp]: "ignoreE fail = fail"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_return[simp]: "ignoreE (return x) = return x"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_throw[simp]: "ignoreE (throw x) = bot"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_yield_Exception[simp]: "e \<noteq> default \<Longrightarrow> ignoreE (yield (Exception e)) = bot"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_guard[simp]: "ignoreE (guard P) = guard P"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_get_state[simp]: "ignoreE (get_state) = get_state"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_set_state[simp]: "ignoreE (set_state s) = set_state s"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_select[simp]: "ignoreE (select S) = select S"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_unknown[simp]: "ignoreE (unknown) = unknown"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_exec_concrete[simp]: "ignoreE (exec_concrete st f) = exec_concrete st (ignoreE f)"
  by (rule spec_monad_eqI) (auto simp add: runs_to_iff)

lemma ignoreE_assert[simp]: "ignoreE (assert P) = assert P"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_assume[simp]: "ignoreE (assume P) = assume P"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_gets[simp]: "ignoreE (gets f) = gets f"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_assert_opt[simp]: "ignoreE (assert_opt v) = assert_opt v"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_gets_the[simp]: "ignoreE (gets_the f) = gets_the f"
  by (rule spec_monad_eqI) (auto simp add: runs_to_iff)

lemma ignoreE_modify[simp]: "ignoreE (modify f) = modify f"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_condition[ignoreE_simps]:
  "ignoreE (condition c f g) = condition c (ignoreE f) (ignoreE g)"
  by (rule spec_monad_eqI) (simp add: runs_to_iff)

lemma ignoreE_when[simp]: "ignoreE (when P f) = when P (ignoreE f)"
  by (simp add: when_def ignoreE_condition)

lemma ignoreE_bind[ignoreE_simps]:
  "ignoreE (bind f g) = bind (ignoreE f) (\<lambda>v. (ignoreE (g v)))"
  by (simp add: spec_monad_eq_iff runs_to_ignoreE_iff runs_to_bind_iff)

lemma ignoreE_map_exn[simp]: "ignoreE (map_value (map_exn f) g) = ignoreE g"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma ignoreE_whileLoop[ignoreE_simps]:
  "ignoreE (whileLoop C B I) = whileLoop C (\<lambda>x. ignoreE (B x)) I"
proof -
  have "(\<lambda>I. ignoreE (whileLoop C B I)) = whileLoop C (\<lambda>x. ignoreE (B x))"
    unfolding whileLoop_def
    apply (rule gfp_fusion[OF _ mono_whileLoop_functional mono_whileLoop_functional,
      where g="\<lambda>x a. liftE (x a)"])
    subgoal by (simp add: le_fun_def liftE_le_iff_le_ignoreE)
    subgoal by (simp add: ignoreE_bind ignoreE_condition)
    done
  then show ?thesis by (simp add: fun_eq_iff)
qed

subsection \<open>\<^const>\<open>on_exit'\<close>\<close>

lemmas bind_finally_def = bind_exception_or_result_def

lemma bind_exception_or_result_liftE_assoc:
  "bind_exception_or_result (bind (liftE f) g) h = bind f (\<lambda>v. bind_exception_or_result (g v) h)"
  by (rule spec_monad_eqI) (auto simp add: runs_to_iff)

lemma bind_exception_or_result_bind_guard_assoc:
  "bind_exception_or_result (bind (guard P) g) h =
    bind (guard P) (\<lambda>v. bind_exception_or_result (g v) h)"
  by (rule spec_monad_eqI) (auto simp add: runs_to_iff)

lemma on_exit_bind_exception_or_result_conv: 
  "on_exit f cleanup = bind_exception_or_result f (\<lambda>x. do {state_select cleanup; yield x})"
  by (simp add: on_exit_def on_exit'_def)

lemma guard_on_exit_bind_exception_or_result_conv: 
  "guard_on_exit f P cleanup =
    bind_exception_or_result f (\<lambda>x. do {guard P; state_select cleanup; yield x})"
  by (simp add: on_exit'_def bind_assoc)

lemma assume_result_and_state_check_only_state:
  "assume_result_and_state (\<lambda>s. {((), s'). s' = s \<and> P s}) = assuming P"
  by (simp add: spec_monad_eq_iff runs_to_iff)

lemma assume_on_exit_bind_exception_or_result_conv: 
  "assume_on_exit f P cleanup = bind_exception_or_result f
    (\<lambda>x. do {assume_result_and_state (\<lambda>s. {((), s'). s' = s \<and> P s}); state_select cleanup; yield x})"
  by (simp add: on_exit'_def bind_assoc assume_result_and_state_check_only_state)

lemma monotone_on_exit'_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. g f') \<Longrightarrow>
    monotone R (\<le>) (\<lambda>f'. on_exit' (f f') (g f'))"
  unfolding on_exit'_def by (intro partial_function_mono)

lemma monotone_on_exit'_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. g f') \<Longrightarrow>
    monotone R (\<ge>) (\<lambda>f'. on_exit' (f f') (g f'))"
  unfolding on_exit'_def by (intro partial_function_mono)

lemma runs_to_on_exit'_iff[runs_to_iff]:
  "on_exit' f c \<bullet> s \<lbrace> Q \<rbrace> \<longleftrightarrow>
    f \<bullet> s \<lbrace> \<lambda>r t. c \<bullet> t \<lbrace> \<lambda>q t. Q (case q of Exception e \<Rightarrow> Exception e | Result _ \<Rightarrow> r) t \<rbrace> \<rbrace>"
  by (auto simp add: on_exit'_def runs_to_iff fun_eq_iff split: exception_or_result_split
           intro!: arg_cong[where f="runs_to _ _"])

lemma runs_to_on_exit'[runs_to_vcg]:
  "f \<bullet> s \<lbrace> \<lambda>r t. c \<bullet> t \<lbrace> \<lambda>q t. Q (case q of Exception e \<Rightarrow> Exception e | Result _ \<Rightarrow> r) t \<rbrace> \<rbrace> \<Longrightarrow> on_exit' f c \<bullet> s \<lbrace> Q \<rbrace>"
  by (simp add: runs_to_on_exit'_iff)

lemma runs_to_partial_on_exit'[runs_to_vcg]:
  "f \<bullet> s ?\<lbrace> \<lambda>r t. c \<bullet> t ?\<lbrace> \<lambda>q t. Q (case q of Exception e \<Rightarrow> Exception e | Result _ \<Rightarrow> r) t \<rbrace> \<rbrace> \<Longrightarrow> on_exit' f c \<bullet> s ?\<lbrace> Q \<rbrace>"
  unfolding on_exit'_def
  apply (rule runs_to_partial_bind_exception_or_result)
  apply (rule runs_to_partial_weaken, assumption)
  apply (rule runs_to_partial_bind)
  apply (rule runs_to_partial_weaken, assumption)
  apply auto
  done

lemma refines_on_exit':
  assumes f: "refines f f' s s'
    (\<lambda>(r, t) (r', t'). refines c c' t t' (\<lambda>(q, t) (q', t'). R
      (case q of Exception e \<Rightarrow> Exception e | Result _ \<Rightarrow> r, t) 
      (case q' of Exception e' \<Rightarrow> Exception e' | Result _ \<Rightarrow> r', t')))"
  shows "refines (on_exit' f c) (on_exit' f' c') s s' R"
  unfolding on_exit'_def
  apply (rule refines_bind_exception_or_result[OF f[THEN refines_weaken]])
  apply (clarsimp intro!: refines_bind')
  apply (rule refines_weaken, assumption)
  apply auto
  done

lemma on_exit'_skip: "on_exit' f skip = f"
  by (simp add: spec_monad_eq_iff runs_to_iff)

subsection \<open>\<^const>\<open>run_bind\<close>\<close>

lemma run_run_bind: "run (run_bind f t g) s = bind_post_state (run f t) (\<lambda>(r, t). run (g r t) s)"
  by (transfer) simp

lemma runs_to_run_bind_iff[runs_to_iff]:
  "(run_bind f t g) \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> f \<bullet> t \<lbrace>\<lambda>r t. (g r t) \<bullet> s \<lbrace>Q\<rbrace> \<rbrace>"
  by (simp add: runs_to.rep_eq run_run_bind split_beta')

lemma runs_to_run_bind[runs_to_vcg]:
  "f \<bullet> t \<lbrace>\<lambda>r t. (g r t) \<bullet> s \<lbrace>Q\<rbrace> \<rbrace> \<Longrightarrow> (run_bind f t g) \<bullet> s \<lbrace>Q\<rbrace>"
  by (simp add: runs_to_run_bind_iff)

lemma runs_to_partial_run_bind[runs_to_vcg]:
  "f \<bullet> t ?\<lbrace>\<lambda>r t. (g r t) \<bullet> s ?\<lbrace>Q\<rbrace> \<rbrace> \<Longrightarrow> (run_bind f t g) \<bullet> s ?\<lbrace>Q\<rbrace>"
  by (auto simp: runs_to_partial.rep_eq run_run_bind split_beta'
           intro!: holds_partial_bind_post_state)

lemma mono_run_bind: "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> run_bind f t g \<le> run_bind f' t g' "
  apply (rule le_spec_monad_runI)
  apply (simp add: run_run_bind)
  apply (rule mono_bind_post_state)
   apply (auto simp add: le_fun_def less_eq_spec_monad.rep_eq split: exception_or_result_splits)
  done

lemma monotone_run_bind_le[partial_function_mono]:
  "monotone R (\<le>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>r t. monotone R (\<le>) (\<lambda>f'. g f' r t))
  \<Longrightarrow> monotone R (\<le>) (\<lambda>f'. run_bind (f f') t (g f'))"
  apply (simp add: monotone_def)
  using mono_run_bind
  by (metis le_fun_def)

lemma monotone_run_bind_ge[partial_function_mono]:
  "monotone R (\<ge>) (\<lambda>f'. f f') \<Longrightarrow> (\<And>r t. monotone R (\<ge>) (\<lambda>f'. g f' r t))
  \<Longrightarrow> monotone R (\<ge>) (\<lambda>f'. run_bind (f f') t (g f'))"
  apply (simp add: monotone_def)
  using mono_run_bind
  by (metis le_fun_def)

lemma liftE_run_bind: "liftE (run_bind f t g) = run_bind f t (\<lambda>r t. liftE (g r t))"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma exec_concrete_run_bind: "exec_concrete st f =
  do {
   s \<leftarrow> get_state;
   t \<leftarrow> select {t. st t = s};
   run_bind f t (\<lambda>r' t'. do {set_state (st t'); yield r' })
  }"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma exec_abstract_run_bind: "exec_abstract st f =
  do {
   s \<leftarrow> get_state;
   run_bind f (st s) (\<lambda>r' t'. do {s' \<leftarrow> select {s'. t' = st s'}; set_state s'; yield r' })
  }"
  apply (rule spec_monad_eqI)
  apply (auto simp add: runs_to_iff)
  done

lemma refines_run_bind:
  "refines f f' x y (\<lambda>(r,x') (r', y'). refines (g r x') (g' r' y') s t R) \<Longrightarrow>
    refines (run_bind f x g) (run_bind f' y g') s t R"
  apply transfer
  apply (rule sim_bind_post_state, assumption)
  apply auto
  done


subsection \<open>Iteration of monadic actions\<close>

fun iter_spec_monad where
  "iter_spec_monad f 0       = skip" |
  "iter_spec_monad f (Suc n) = do {iter_spec_monad f n; f n }"

lemma iter_spec_monad_unfold:
  "0 < n \<Longrightarrow> iter_spec_monad f n = do {iter_spec_monad f (n-1); f (n-1) }"
  by (metis Suc_pred' iter_spec_monad.simps(2))

lemma iter_spec_monad_cong:
  "(\<And>j. j < i \<Longrightarrow> f j = g j) \<Longrightarrow> iter_spec_monad f i = iter_spec_monad g i"
  by (induction i) auto

subsection \<open>\<open>forLoop\<close>\<close>

definition forLoop:: "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> ('a, 's) res_monad) \<Rightarrow> (int, 's) res_monad" where
  "forLoop z (m::int) B = whileLoop (\<lambda>i s. i < m) (\<lambda>i. do {B i; return (i + 1) }) z"

lemma runs_to_forLoop:
  assumes "z \<le> m"
  assumes I: "\<And>r s. I r s \<Longrightarrow> z \<le> r \<Longrightarrow> r < m \<Longrightarrow> (B r) \<bullet> s \<lbrace> \<lambda>_ t. I (r + 1) t \<rbrace>"
  assumes Q: "\<And>s. I m s \<Longrightarrow> Q m s"
  shows "I z s \<Longrightarrow> (forLoop z m B) \<bullet> s \<lbrace>\<lambda>Res r. Q r\<rbrace>"
  unfolding forLoop_def
  using \<open>z \<le> m\<close> Q I
  by (intro runs_to_whileLoop_res[where I="\<lambda>q t. I q t \<and> z \<le> q \<and> q \<le> m"
        and P=Q
        and R="measure (\<lambda>(i, _). nat (m - i))"])
    (auto intro!: runs_to_bind)

lemma whileLoop_cong_inv:
  "run ((whileLoop C f z)::('a, 's) res_monad) s = run (whileLoop D g z) s"
  if I: "\<And>i s. I i s \<Longrightarrow> C i s \<Longrightarrow> f i \<bullet> s ?\<lbrace> \<lambda>v' s'. \<forall>i'. v' = Result i' \<longrightarrow> I i' s'\<rbrace>"
    and I_eq: "\<And>i s. I i s \<Longrightarrow> C i s \<Longrightarrow> run (f i) s = run (g i) s"
    and C_eq: "\<And>i s. I i s \<Longrightarrow> C i s \<longleftrightarrow> D i s"
    and "I z s"
  for s::'s and z::'a and R::"('a \<times> 's) rel"
proof -
  have "rel_spec (whileLoop C f z) (whileLoop D g z) s s
    (\<lambda>(Res i, s) (Res i', s'). i = i' \<and> s = s' \<and> I i s)"
    apply (intro rel_spec_whileLoop_res)
    subgoal for i s j t using C_eq[of i s] by auto
    subgoal premises prems for i s j t
      using prems I[of i s]
      apply (clarsimp simp: rel_spec.rep_eq runs_to_partial.rep_eq I_eq
                      intro!: rel_post_state_refl')
      apply (auto intro: holds_partial_post_state_weaken)
      done
    subgoal using \<open>I z s\<close> by simp
    done
  from rel_spec_mono[OF _ this, of "(=)"]
  show ?thesis
    by (auto simp: le_fun_def rel_spec_eq)
qed

lemma forLoop_skip: "forLoop z m f = return z" if "z \<ge> m"
  using that unfolding forLoop_def
  by (subst whileLoop_unroll) simp

lemma forLoop_eq_whileLoop: "forLoop z m f = whileLoop C g z"
  if "\<And>i. z \<le> i \<Longrightarrow> i < m \<Longrightarrow> g i = do { y \<leftarrow> f i; return (i + 1) }"
    "\<And>i s. z \<le> i \<Longrightarrow> i \<le> m \<Longrightarrow> C i s \<longleftrightarrow> i < m"
    "\<And>s. z > m \<Longrightarrow> \<not> C z s"
proof cases
  assume "z \<le> m"
  then show ?thesis
    unfolding forLoop_def
    apply (intro spec_monad_ext ext whileLoop_cong_inv[where I="\<lambda>i s. z \<le> i \<and> i \<le> m"])
    apply (auto simp: that intro!: runs_to_partial_bind)
    done
next
  assume "\<not> z \<le> m"
  then show ?thesis
    apply (subst whileLoop_unroll)
    apply (simp add: forLoop_skip)
    apply (rule spec_monad_ext)
    apply (simp add: that)
    done
qed

lemma runs_to_partial_forLoopE: "forLoop z m f \<bullet> s ?\<lbrace> \<lambda>x s'. \<forall>v. x = Result v \<longrightarrow> v = m \<rbrace>"
  if "z \<le> m"
proof -
  have *: "forLoop z m f = whileLoop (\<lambda>i _. i \<noteq> m) (\<lambda>i. do {f i; return (i + 1) }) z"
    using \<open>z \<le> m\<close>
    by (auto intro!: forLoop_eq_whileLoop)
  show ?thesis unfolding *
    by (rule runs_to_partial_whileLoop_cond_false[THEN runs_to_partial_weaken]) simp
qed

subsection \<open>\<open>whileLoop_unroll_reachable\<close>\<close>

context fixes C :: "'a \<Rightarrow> 's \<Rightarrow> bool" and B :: "'a \<Rightarrow> ('e::default, 'a, 's) spec_monad"
begin

inductive whileLoop_unroll_reachable :: "'a \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" for a s where
  initial[intro, simp]: "whileLoop_unroll_reachable a s a s"
| step: "\<And>b t X c u.
    whileLoop_unroll_reachable a s b t \<Longrightarrow> C b t \<Longrightarrow>
    run (B b) t = Success X \<Longrightarrow> (Result c, u) \<in> X \<Longrightarrow>
    whileLoop_unroll_reachable a s c u"

lemma whileLoop_unroll_reachable_trans:
  assumes a_b: "whileLoop_unroll_reachable a s b t" and b_c: "whileLoop_unroll_reachable b t c u"
  shows "whileLoop_unroll_reachable a s c u"
proof (use b_c in \<open>induction arbitrary: \<close>)
  case (step c u X d v)
  show ?case
    by (rule whileLoop_unroll_reachable.step[OF step(5,2,3,4)])
qed (simp add: a_b)

end

lemma run_whileLoop_unroll_reachable_cong:
  assumes eq:
    "\<And>b t. whileLoop_unroll_reachable C B a s b t \<Longrightarrow> C b t \<longleftrightarrow> C' b t"
    "\<And>b t. whileLoop_unroll_reachable C B a s b t \<Longrightarrow> C b t \<Longrightarrow> run (B b) t = run (B' b) t"
  shows "run (whileLoop C B a) s  = run (whileLoop C' B' a) s"
proof -
  have "rel_spec (whileLoop C B a) (whileLoop C' B' a) s s
    (\<lambda>(x', s') (y, t). y = x' \<and> t = s'\<and>
      (\<forall>a'. x' = Result a' \<longrightarrow> whileLoop_unroll_reachable C B a s a' s'))"
    apply (rule rel_spec_whileLoop)
    subgoal by (simp add: eq)
    subgoal for a' s'
      using whileLoop_unroll_reachable.step[of C B a s a' s']
      by (cases "run (B' a') s'") (auto simp add: rel_spec_def eq intro!: rel_set_refl)
    subgoal by simp
    subgoal for a' s' b' t' by (cases a') (auto simp add: rel_exception_or_result.simps)
    done
  then have "rel_spec (whileLoop C B a) (whileLoop C' B' a) s s (=)"
    by (rule rel_spec_mono[rotated]) auto
  then show ?thesis
    by (simp add: rel_spec_eq)
qed

subsection \<open>\<open>on_exit\<close>\<close>

lemma refines_rel_prod_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (rel_prod R S')"
  assumes cleanup: "\<And>s\<^sub>c s\<^sub>a t\<^sub>c. S' s\<^sub>c s\<^sub>a \<Longrightarrow> (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> \<exists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a \<and> S t\<^sub>c t\<^sub>a"
  assumes emp: "\<And>s\<^sub>c s\<^sub>a. S' s\<^sub>c s\<^sub>a \<Longrightarrow> \<nexists>t\<^sub>c. (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> \<nexists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a"
  shows "refines (on_exit f\<^sub>c cleanup\<^sub>c) (on_exit f\<^sub>a cleanup\<^sub>a) s\<^sub>c s\<^sub>a (rel_prod R S)"
  unfolding on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result) 
  apply (rule refines_mono [OF _ f])
  apply (clarsimp) 
  apply (rule refines_bind')
  apply (rule refines_state_select)
  using cleanup emp
   apply auto
  done

lemma refines_runs_to_partial_rel_prod_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (rel_prod R S')"
  assumes runs_to: "f\<^sub>c \<bullet> s\<^sub>c ?\<lbrace>\<lambda>r t. P t\<rbrace>"
  assumes cleanup: "\<And>s\<^sub>c s\<^sub>a t\<^sub>c. S' s\<^sub>c s\<^sub>a \<Longrightarrow> (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> P s\<^sub>c \<Longrightarrow> \<exists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a \<and> S t\<^sub>c t\<^sub>a"
  assumes emp: "\<And>s\<^sub>c s\<^sub>a. S' s\<^sub>c s\<^sub>a \<Longrightarrow> P s\<^sub>c \<Longrightarrow> \<nexists>t\<^sub>c. (s\<^sub>c, t\<^sub>c) \<in> cleanup\<^sub>c \<Longrightarrow> \<nexists>t\<^sub>a. (s\<^sub>a, t\<^sub>a) \<in> cleanup\<^sub>a"
  shows "refines (on_exit f\<^sub>c cleanup\<^sub>c) (on_exit f\<^sub>a cleanup\<^sub>a) s\<^sub>c s\<^sub>a (rel_prod R S)"
proof -
  from refines_runs_to_partial_fuse [OF f runs_to]
  have "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (\<lambda>(r, t) (r', t'). rel_prod R S' (r, t) (r', t') \<and> P t)" .
  moreover have "(\<lambda>(r, t) (r', t'). rel_prod R S' (r, t) (r', t') \<and> P t) = rel_prod R (\<lambda>t t'. S' t t' \<and> P t)"
    by (auto simp add: rel_prod_conv)
  ultimately have "refines f\<^sub>c f\<^sub>a s\<^sub>c s\<^sub>a (rel_prod R (\<lambda>t t'. S' t t' \<and> P t))" by simp
  then show ?thesis
    apply (rule refines_rel_prod_on_exit) 
    subgoal using cleanup by blast
    subgoal using emp by blast
    done
qed


lemma rel_spec_monad_mono:
  assumes Q: "rel_spec_monad R Q f g" and QQ': "\<And>x y. Q x y \<Longrightarrow> Q' x y"
  shows "rel_spec_monad R Q' f g"
proof -
  have "rel_spec_monad R Q \<le> rel_spec_monad R Q'"
    unfolding rel_spec_monad_def using QQ' 
    by (auto simp add: rel_post_state.simps rel_set_def)
      (metis rel_prod_sel)+
  with Q show ?thesis by auto
qed

lemma gets_return: "gets (\<lambda>_. x) = return x"
  by (rule spec_monad_eqI) (auto simp add: runs_to_iff)

lemma bind_handle_bind_exception_or_result_conv: 
  "bind_handle f g h = 
         bind_exception_or_result f 
          (\<lambda>Exception e \<Rightarrow> h e | Result v \<Rightarrow> g v)"
  apply (rule spec_monad_eqI)
  by (auto simp add: runs_to_iff)
    (auto elim!: runs_to_weaken split: exception_or_result_splits)

lemma bind_handle_bind_exception_or_result_conv_exn: "bind_handle f g (\<lambda>Some e \<Rightarrow> h e) = 
         bind_exception_or_result f 
          (\<lambda>Exn e \<Rightarrow> h e | Result v \<Rightarrow> g v)"
  by (simp add: bind_handle_bind_exception_or_result_conv case_xval_def)

lemma try_nested_bind_exception_or_result_conv: 
  shows "try (f >>= g) = 
    (bind_exception_or_result f 
      (\<lambda>Exn e \<Rightarrow> (case e of Inl l \<Rightarrow> throw l | Inr r \<Rightarrow> return r )
      | Result v \<Rightarrow> try (g v)))"
  apply (rule spec_monad_eqI)
  by (auto simp add: runs_to_iff )
    (auto elim!: runs_to_weaken simp add: runs_to_iff  unnest_exn_def 
      split: xval_splits sum.splits)

lemma try_nested_bind_handle_conv:
  shows "try (f >>= g) = 
    (bind_handle f (\<lambda>v. try (g v))
      (\<lambda>Some e \<Rightarrow> (case e of Inl l \<Rightarrow> throw l | Inr r \<Rightarrow> return r )))"
  by (simp add: bind_handle_bind_exception_or_result_conv_exn try_nested_bind_exception_or_result_conv)

definition no_fail:: "('s \<Rightarrow> bool) \<Rightarrow> ('e::default, 'a, 's) spec_monad \<Rightarrow> bool" where
 "no_fail P f \<equiv> \<forall>s. P s \<longrightarrow> run f s \<noteq> \<top>"

definition no_throw:: "('s \<Rightarrow> bool) \<Rightarrow> ('e::default, 'a, 's) spec_monad \<Rightarrow> bool" where
 "no_throw P f \<equiv> \<forall>s. P s \<longrightarrow> f \<bullet> s ?\<lbrace> \<lambda>r t. \<exists>v. r = Result v\<rbrace>"

definition no_return:: "('s \<Rightarrow> bool) \<Rightarrow> ('e::default, 'a, 's) spec_monad \<Rightarrow> bool" where
 "no_return P f \<equiv> \<forall>s. P s \<longrightarrow> f \<bullet> s ?\<lbrace> \<lambda>r t. \<exists>e. r = Exception e \<and> e \<noteq> default\<rbrace>"

lemma no_return_exn_def: "no_return P f \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> f \<bullet> s ?\<lbrace> \<lambda>r t. \<exists>e. r = Exn e\<rbrace>)"
  by (auto simp add: no_return_def Exn_def default_option_def elim!: runs_to_partial_weaken ) 

lemma no_throw_gets[simp]: "no_throw P (gets f)"
  by (auto simp add: no_throw_def runs_to_partial_def)

lemma no_throw_modify[simp]: "no_throw P (modify f)"
  by (auto simp add: no_throw_def runs_to_partial_def)

lemma no_throw_select[simp]: "no_throw P (select f)"
  by (auto simp add: no_throw_def runs_to_partial_def)

lemma always_progress_select_UNIV[simp]: "always_progress (select UNIV)"
  by (auto simp add: always_progress_def bot_post_state_def)

lemma rel_spec_monad_rel_xval_catch:
  assumes fh: "rel_spec_monad R (rel_xval E Q) f h"
  assumes gi: "rel_fun E (rel_spec_monad R (rel_xval E2 Q)) g i"
  shows "rel_spec_monad R (rel_xval E2 Q) (f <catch> g) (h <catch> i)"
  using assms unfolding rel_spec_monad_iff_rel_spec
  by (auto intro!: rel_spec_catch simp: rel_fun_def)

section \<open>Setup for Tagging\<close>

lemma runs_to_tag:
  "(\<paragraph> tag \<Longrightarrow> f \<bullet> s \<lbrace> P \<rbrace>) \<Longrightarrow> (tag \<bar> f) \<bullet> s \<lbrace> P \<rbrace>"
  unfolding TAG_def ASM_TAG_def by auto

lemma runs_to_tag_guard:
  fixes g :: "'a \<Rightarrow> bool"
    and s :: "'a"
  assumes "tag \<bar> g s"
  assumes "P (Result ()) s"
  shows "(tag \<bar> guard g) \<bullet> s \<lbrace> P \<rbrace>"
  using assms unfolding TAG_def by - (rule runs_to_weaken, rule runs_to_guard; simp)

bundle runs_to_vcg_tagging_setup
begin

unbundle basic_vcg_tagging_setup

lemmas [runs_to_vcg] = runs_to_tag runs_to_tag_guard

end

end