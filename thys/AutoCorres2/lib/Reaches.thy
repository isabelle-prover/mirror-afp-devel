(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Reaches
  imports Spec_Monad
begin


text \<open>The core notions on spec monads are
\<^item> Properties of a monad: \<^const>\<open>runs_to\<close>, \<^const>\<open>runs_to_partial\<close>
\<^item> Refinement / Simulation of monads: \<^const>\<open>refines\<close>, \<^const>\<open>rel_spec\<close> and \<^const>\<open>rel_spec_monad\<close>.

It is considered good style to use these more abstract concepts as much as possible.

Next we introduce some notions that are more in a 'pointwise' spirit in the sense that they talk about a 
particular outcome of a monadic computation, e.g. that a particular state is a reachable outcome
of a monadic computation.

There is nothing \<^emph>\<open>wrong\<close> with these notions but we consider them as less elegant and more
'brute force'. So we encourage to think twice before using them and prefer the more abstract
notions.
\<close>

primrec outcomes :: "'a post_state \<Rightarrow> 'a set" where
  "outcomes Failure = {}"
| "outcomes (Success X) = X"

lemma le_post_state_iff:
  "p \<le> q \<longleftrightarrow> (q \<noteq> Failure \<longrightarrow> (p \<noteq> Failure \<and> outcomes p \<subseteq> outcomes q))"
  by (cases q; cases p) simp_all

lemma outcomes_map[simp]: "outcomes (map_post_state f x) = f ` outcomes x"
  by (cases x) simp_all

lemma map_post_state_eq_Failure[simp]:
  "map_post_state f x = Failure \<longleftrightarrow> x = Failure"
  by (cases x; simp)

lemma outcomes_Sup[simp]: "Failure \<notin> F \<Longrightarrow> outcomes (Sup F) = (\<Union>f\<in>F. outcomes f)"
  by (auto simp: Sup_post_state_def)
    (metis outcomes.simps(2) post_state.exhaust vimage_eq)


(* TODO: remove: *)
lemmas runs_to_holds_def = runs_to.rep_eq
lemmas runs_to_partial_holds_partial_def = runs_to_partial.rep_eq
(* END TODO *)

section \<open>\<open>succeeds\<close> and \<open>reaches\<close>\<close>

definition succeeds :: "('e::default, 'a, 's) spec_monad \<Rightarrow> 's \<Rightarrow> bool" where
  "succeeds f s \<longleftrightarrow> run f s \<noteq> \<top>"

definition reaches :: "('e::default, 'a, 's) spec_monad \<Rightarrow> 's \<Rightarrow> ('e, 'a) exception_or_result \<Rightarrow> 's \<Rightarrow> bool" where
  "reaches f s r' s' \<longleftrightarrow> (r', s') \<in> outcomes (run f s)"

text \<open>There seems to a similarity between what happens in HOL with the dualism of sets as type vs. the
characterisation as predicate as expressed in \<^const>\<open>Collect\<close>. Similar \<^typ>\<open>'a post_state\<close> has a
set in the \<^const>\<open>Success\<close> case. In particular with \<^const>\<open>holds_post_state\<close> we switch to the predicate view.
Which is then continued in \<^const>\<open>runs_to\<close> which is the predicate view and the set view with \<^const>\<open>reaches\<close>,
which is more the element wise set view similar to \<^term>\<open>x \<in> X\<close> and finally culminates in
 @{thm spec_monad_eq_iff}. The predicate view seems to be the one we finally
aim for. So maybe we could get completely rid of the set like things and start of with a
predicate already in \<^typ>\<open>'a post_state\<close>?\<close>

lemma runs_to_partial_def_old:
  "runs_to_partial f s Q \<longleftrightarrow> (succeeds f s \<longrightarrow> (\<forall>r t. reaches f s r t \<longrightarrow> Q r t))"
  unfolding succeeds_def reaches_def runs_to_partial.rep_eq
  by (cases "run f s") (auto simp: top_post_state_def)

lemma runs_to_def_old: "runs_to f s Q \<longleftrightarrow> succeeds f s \<and> (\<forall>r t. reaches f s r t \<longrightarrow> Q r t)"
  unfolding succeeds_def reaches_def runs_to.rep_eq
  by (cases "run f s") (auto simp: top_post_state_def)

lemma runs_to_succeeds_runsto_partial_conv:
  "runs_to f s Q \<longleftrightarrow> (succeeds f s \<and> runs_to_partial f s Q)"
  by (auto simp add: runs_to_def_old runs_to_partial_def_old)

lemma run_Success_succeeds: "run f s = Success x \<Longrightarrow> succeeds f s"
  by (auto simp add: succeeds_def top_post_state_def)

lemma runs_to_partial_le_outcomes_conv:
  "runs_to_partial f s Q \<longleftrightarrow> (outcomes (run f s)) \<le> {(r,t). Q r t}"
  apply (simp add: runs_to_partial_def_old succeeds_def outcomes_def reaches_def top_post_state_def)
  apply transfer
  apply standard
  subgoal
    by (auto split: post_state.splits)
  subgoal
    by blast
  done

lemma not_succeeds_empty_outcomes: "\<not> succeeds f s \<Longrightarrow> outcomes (run f s) = {}"
  by (simp add: succeeds_def top_post_state_def)

lemma reaches_succeeds: "reaches f s r t \<Longrightarrow> succeeds f s"
  apply (simp add: reaches_def succeeds_def top_post_state_def)
  apply transfer
  apply auto
  done

lemma always_progress_succeeds_reaches_conv:
  "always_progress f \<longleftrightarrow> (\<forall>s. succeeds f s \<longrightarrow> (\<exists>r t. reaches f s r t))"
  apply (simp add: always_progress_def succeeds_def reaches_def)
  apply transfer
  apply (clarsimp simp add: top_post_state_def bot_post_state_def, safe)
   apply (metis ex_in_conv outcomes.simps(2) post_state.exhaust surj_pair)
  by (metis empty_iff post_state.distinct(1) outcomes.simps(2))

lemma le_succeedsD: "g \<le> f \<Longrightarrow> succeeds f s \<Longrightarrow> succeeds g s"
  apply (simp add: succeeds_def)
  apply transfer
  by (auto simp add: le_fun_def less_eq_post_state.simps top_post_state_def)

lemma outcomes_succeeds_run_conv: "outcomes (run f s) = X \<Longrightarrow> succeeds f s \<Longrightarrow> run f s = Success X"
  by (cases "run f s") (auto simp add: succeeds_def top_post_state_def)

lemma succeeds_outcomes_run_eqI: "succeeds f s \<longleftrightarrow> succeeds g s \<Longrightarrow>
       (succeeds f s \<Longrightarrow> succeeds g s \<Longrightarrow> (outcomes (run f s) = outcomes (run g s))) \<Longrightarrow>
       run f s = run g s"
  by (cases "run f s"; cases "run g s") (auto simp add: succeeds_def top_post_state_def)

lemma succeeds_outcomes_spec_monad_eqI:
"(\<And>s. succeeds f s \<longleftrightarrow> succeeds g s) \<Longrightarrow>
 (\<And>s. succeeds f s \<Longrightarrow> succeeds g s \<Longrightarrow> (outcomes (run f s) = outcomes (run g s))) \<Longrightarrow>
 f = g"
  apply (rule spec_monad_ext)
  apply (auto intro: succeeds_outcomes_run_eqI)
  done

lemma succeeds_reaches_spec_monad_eqI:
"(\<And>s. succeeds f s \<longleftrightarrow> succeeds g s) \<Longrightarrow>
 (\<And>s r t. succeeds f s \<Longrightarrow> succeeds g s \<Longrightarrow> (reaches f s r t \<longleftrightarrow> reaches g s r t)) \<Longrightarrow>
 f = g"
  apply (rule succeeds_outcomes_spec_monad_eqI)
   apply simp
  apply (auto simp add: reaches_def)
  done

lemma succeeds_runs_to_iff: "succeeds f s \<longleftrightarrow> runs_to f s (\<lambda>_ _. True)"
  by (simp add: runs_to_def_old)

named_theorems outcomes_spec_monad "Simplification rules for outcomes of Spec monad"

subsection \<open>Relational rewriting for Monads\<close>

lemma refines_def_old:
  "refines f g s t R \<longleftrightarrow>
    (succeeds g t \<longrightarrow> succeeds f s \<and>
      (\<forall>r s'. reaches f s r s' \<longrightarrow> (\<exists>x t'. reaches g t x t' \<and> R (r, s') (x, t'))))"
  by (cases "run g t"; cases "run f s")
     (force simp: refines.rep_eq succeeds_def reaches_def top_post_state_def)+

lemma rel_specI:
  assumes "succeeds f s \<longleftrightarrow> succeeds g t"
  assumes "\<And>r s'. reaches f s r s' \<Longrightarrow> \<exists>q t'. reaches g t q t' \<and> R (r, s') (q, t')"
  assumes "\<And>q t'. reaches g t q t' \<Longrightarrow> \<exists>r s'. reaches f s r s' \<and> R (r, s') (q, t')"
  shows "rel_spec f g s t R"
  using assms
  by (cases "run f s"; cases "run g t";
      fastforce simp: rel_spec_def rel_prod.simps rel_set_def
      reaches_def succeeds_def top_post_state_def)

lemma rel_specD_succeeds:
  "rel_spec f g s t R \<Longrightarrow> succeeds f s \<longleftrightarrow> succeeds g t"
  by (cases "run f s"; cases "run g t";
      simp add: rel_post_state.simps rel_spec_def rel_prod.simps succeeds_def top_post_state_def)

lemma rel_specD_reaches1:
  "rel_spec f g s t R \<Longrightarrow> reaches f s r s' \<Longrightarrow> \<exists>q t'. reaches g t q t' \<and> R (r, s') (q, t')"
  by (cases "run f s"; cases "run g t";
      fastforce simp: rel_post_state.simps rel_spec_def rel_prod.simps rel_set_def
      reaches_def top_post_state_def)

lemma rel_specD_reaches2:
  "rel_spec f g s t R \<Longrightarrow> reaches g t q t' \<Longrightarrow> \<exists>r s'. reaches f s r s' \<and> R (r, s') (q, t')"
  by (cases "run f s"; cases "run g t";
      fastforce simp: rel_post_state.simps rel_spec_def rel_prod.simps rel_set_def
      reaches_def top_post_state_def)

lemma refines_iff:
  "refines f g s t R \<longleftrightarrow>
    ((succeeds g t \<longrightarrow> succeeds f s) \<and>
    (succeeds g t \<longrightarrow> succeeds f s \<longrightarrow>
       (\<forall>r s'. reaches f s r s' \<longrightarrow> (\<exists>q t'. reaches g t q t' \<and> R (r, s') (q, t')))))"
  by (simp add: refines_def_old) blast

lemma refinesI:
  assumes "succeeds g t \<Longrightarrow> succeeds f s"
  assumes "\<And>r s'. succeeds g t \<Longrightarrow> succeeds f s \<Longrightarrow> reaches f s r s' \<Longrightarrow>
    (\<exists>q t'. reaches g t q t' \<and> R (r, s') (q, t'))"
  shows "refines f g s t R"
  using assms
  by (auto simp add: refines_def_old)

lemma refinesD_succeeds:
  "refines f g s t R \<Longrightarrow> succeeds g t \<Longrightarrow> succeeds f s"
  by (auto simp: refines_def_old)

lemma refinesD_reaches:
  "refines f g s t R \<Longrightarrow> reaches f s r s' \<Longrightarrow> succeeds g t
    \<Longrightarrow> \<exists>q t'. reaches g t q t' \<and> R (r, s') (q, t')"
  by (fastforce simp: refines_def_old )

lemma refines_strengthen':
  assumes "refines f g s t R"
  assumes "\<And>r u q v. reaches f s r u \<Longrightarrow> reaches g t q v \<Longrightarrow> succeeds f s \<Longrightarrow> succeeds g t
   \<Longrightarrow> R (r, u) (q, v) \<Longrightarrow> Q (r, u) (q, v)"
  shows "refines f g s t Q"
  using assms by (fastforce simp: refines_def_old)

lemma always_progressD: "always_progress f \<Longrightarrow> succeeds f s \<Longrightarrow> \<exists>r t. reaches f s r t"
  by (auto simp:always_progress_succeeds_reaches_conv)

lemma Ex_reaches: "f \<bullet> s \<lbrace> P \<rbrace> \<Longrightarrow> always_progress f \<Longrightarrow> \<exists>r t. reaches f s r t"
  by (auto simp: runs_to_def_old always_progress_succeeds_reaches_conv)

lemma witness_outcomes_succeeds: "x \<in> outcomes (run f s) \<Longrightarrow> succeeds f s"
  using not_succeeds_empty_outcomes by fastforce

lemma runs_toD2: "f \<bullet> s \<lbrace> P \<rbrace> \<Longrightarrow> reaches f s r t \<Longrightarrow> P r t"
  by (simp add: runs_to_def_old)

lemma runs_toD2_res: fixes f:: "('a, 's) res_monad"
  shows "f \<bullet> s \<lbrace>\<lambda>Res r. P r \<rbrace> \<Longrightarrow> reaches f s (Result r) t \<Longrightarrow> P r t"
  by (simp add: runs_to_def_old)

lemma rel_post_state_runI:
  assumes "succeeds f s \<longleftrightarrow> succeeds g t"
  assumes "succeeds f s \<Longrightarrow> succeeds g t \<Longrightarrow> rel_set R (outcomes (run f s)) (outcomes (run g t))"
  shows "rel_post_state R (run f s) (run g t)"
  using assms
  by (cases "run f s"; cases "run g t") 
     (auto simp add: rel_post_state.simps succeeds_def top_post_state_def)

lemma rel_post_state_runI':
  assumes "succeeds f s \<longleftrightarrow> succeeds g t"
  assumes "succeeds f s \<Longrightarrow> succeeds g t \<Longrightarrow> rel_post_state R (run f s) (run g t)"
  shows "rel_post_state R (run f s) (run g t)"
  using assms
  by (auto simp add: rel_post_state.simps succeeds_def top_post_state_def)

lemma rel_post_state_runD:
  assumes "rel_post_state R (run f s) (run g t)"
  shows "(succeeds f s \<longleftrightarrow> succeeds g t) \<and>
         (succeeds f s \<longrightarrow> succeeds g t \<longrightarrow> rel_set R (outcomes (run f s)) (outcomes (run g t)))"
  using assms
  by (auto simp add: rel_post_state.simps succeeds_def top_post_state_def)

lemma rel_post_state_run_iff:
  "rel_post_state R (run f s) (run g t) \<longleftrightarrow>
    ((succeeds f s \<longleftrightarrow> succeeds g t) \<and>
     (succeeds f s \<longrightarrow> succeeds g t \<longrightarrow> rel_set R (outcomes (run f s)) (outcomes (run g t))))"
  using rel_post_state_runI rel_post_state_runD by metis

lemma rel_spec_monad_succeeds_iff: "rel_spec_monad R Q f g \<Longrightarrow> R s t \<Longrightarrow> succeeds f s \<longleftrightarrow> succeeds g t"
  by (meson rel_specD_succeeds rel_spec_monad_iff_rel_spec)

lemma outcomes_top_ps[simp]: "outcomes \<top> = {}" "outcomes (pure_post_state x) = {x}"
"outcomes \<bottom> = {}"
  by (auto simp: top_post_state_def pure_post_state_def bot_post_state_def)

subsection "\<^const>\<open>top\<close>"

lemma outcomes_top[outcomes_spec_monad]: "outcomes (run \<top> s) = {}"
  by transfer (simp add: top_spec_monad_def top_post_state_def)

lemma succeeds_top[simp]: "succeeds \<top> s \<longleftrightarrow> False"
  unfolding succeeds_def
  by transfer (simp add: top_spec_monad_def top_post_state_def)

lemma reaches_top[simp]: "reaches \<top> s r t \<longleftrightarrow> False"
  unfolding reaches_def
  by (simp add: outcomes_top top_post_state_def)

subsection \<open>\<^const>\<open>bot\<close>\<close>

lemma outcomes_bot[outcomes_spec_monad]: "outcomes (run \<bottom> s) = {}"
  by transfer (simp add: bot_spec_monad_def bot_post_state_def)

lemma succeeds_bot[simp]: "succeeds \<bottom> s \<longleftrightarrow> True"
  unfolding succeeds_def
  by transfer (simp add: bot_spec_monad_def bot_post_state_def top_post_state_def)

lemma reaches_bot[simp]: "reaches \<bottom> s r t \<longleftrightarrow> False"
  unfolding reaches_def
  by (simp add: outcomes_bot bot_post_state_def)

subsection "\<^const>\<open>fail\<close>"

lemma outcomes_fail[outcomes_spec_monad]: "outcomes (run fail s) = {}"
  by transfer simp

lemma succeeds_fail_iff[iff]: "\<not> (succeeds fail f)"
  by (simp add: succeeds_def)

lemma reaches_fail_iff[iff]: "\<not> reaches fail s r t"
  by (simp add: reaches_def outcomes_spec_monad top_post_state_def)


subsection "\<^const>\<open>yield\<close>"

lemma succeeds_yield[simp]: "succeeds (yield r) s"
  unfolding succeeds_def
  apply transfer
  apply (simp add: pure_post_state_def top_post_state_def)
  done

lemma outcomes_yield [outcomes_spec_monad]: "outcomes (run (yield r) s) = {(r, s)}"
  by (simp add: pure_post_state_def)

lemma reaches_yield[simp]: "reaches (yield v) s r t \<longleftrightarrow> (r = v \<and> (t = s))"
  by (simp add: reaches_def outcomes_spec_monad pure_post_state_def)


subsection "\<^const>\<open>return\<close>"

lemma outcomes_return [outcomes_spec_monad]:
  "outcomes (run (return v) s) = {(Result v, s)}"
  by transfer (simp add: pure_post_state_def)

lemma succeeds_return [iff]: "succeeds (return v) s"
  by (simp add: succeeds_def top_post_state_def)

lemma reaches_return[simp]: "reaches (return v) s r t \<longleftrightarrow> (r = Result v \<and> (t = s))"
  by (simp add: reaches_def outcomes_spec_monad pure_post_state_def)

lemma refines_yield_left:
  "refines (yield x) f s t R"
  if "succeeds f t \<Longrightarrow> reaches f t x' s' \<and> R (x, s) (x', s')"
  using that
  unfolding refines_def_old
  by (auto simp: succeeds_def top_post_state_def intro!: bexI[where x="(x', s')"])

subsection "\<^const>\<open>skip\<close>"

lemma outcomes_skip [outcomes_spec_monad]:
  "outcomes (run (skip) s) = {(Result (), s)}"
  by (simp add: outcomes_spec_monad pure_post_state_def)

lemma succeeds_skip: "succeeds skip s"
  by simp

lemma reaches_skip: "reaches (return v) s r t \<longleftrightarrow> (r = Result () \<and> (t = s))"
  by (simp add: reaches_def outcomes_spec_monad pure_post_state_def)

lemma runs_to_skip[runs_to_vcg]: "skip \<bullet> s \<lbrace> \<lambda>_ t. t = s \<rbrace>"
  by simp

lemma runs_to_partial_skip[runs_to_vcg]: "skip \<bullet> s ?\<lbrace> \<lambda>_ t. t = s \<rbrace>"
  by simp

lemma runs_to_skip_iff[runs_to_iff]: "skip \<bullet> s \<lbrace>Q\<rbrace> \<longleftrightarrow> Q (Result ()) s"
  by (simp add: runs_to_def_old)


subsection \<open>\<^const>\<open>throw_exception_or_result\<close>\<close>

lemma outcomes_throw_exception_or_result [outcomes_spec_monad]:
  "outcomes (run (throw_exception_or_result x) s) = {(Exception x, s)}"
  by transfer (simp add: pure_post_state_def)

lemma succeeds_throw_exception_or_result [iff]: "succeeds (throw_exception_or_result v) s"
  by (simp add: succeeds_def top_post_state_def)

lemma reaches_throw_exception_or_result[simp]:
  "reaches (throw_exception_or_result x) s r t \<longleftrightarrow> (r = Exception x \<and> (t = s))"
  by (simp add: reaches_def outcomes_spec_monad pure_post_state_def)

subsection \<open>\<^const>\<open>throw\<close>\<close>

lemma outcomes_throw [outcomes_spec_monad]:
  "outcomes (run (throw e) s) = {(Exn e, s)}"
  by (simp add: pure_post_state_def)

subsection \<open>\<^const>\<open>get_state\<close>\<close>

lemma outcomes_get_state [outcomes_spec_monad]:
  "outcomes (run get_state s) = {(Result s, s)}"
  by transfer (simp add: pure_post_state_def)

lemma succeeds_get_state [iff]: "succeeds get_state s"
  by (simp add: succeeds_def)

lemma reaches_get_state[simp]:
  "reaches get_state s r t \<longleftrightarrow> (r = Result s \<and> (t = s))"
  by (simp add: reaches_def outcomes_spec_monad pure_post_state_def)

subsection \<open>\<^const>\<open>set_state\<close>\<close>

lemma outcomes_set_state [outcomes_spec_monad]:
  "outcomes (run (set_state t) s) = {(Result (), t)}"
  by transfer (simp add: pure_post_state_def)

lemma succeeds_set_state [iff]: "succeeds (set_state t) s"
  by (simp add: succeeds_def)

lemma reaches_set_state[simp]: "reaches (set_state s') s r t \<longleftrightarrow> (r = Result () \<and> (t = s'))"
  by (simp add: reaches_def outcomes_spec_monad pure_post_state_def)

subsection \<open>\<^const>\<open>select\<close>\<close>

lemma succeeds_holds: "succeeds f s \<longleftrightarrow> holds_post_state (\<lambda>x. True) (run f s)"
  by (cases "run f s") (simp_all add: succeeds_def top_post_state_def)

lemma succeeds_select[simp]: "succeeds (select S) s"
  apply (simp add:  succeeds_holds select_def)
  apply transfer
  apply (auto simp add: pure_post_state_def)
  done

lemma select_outcomes[outcomes_spec_monad]: "outcomes (run (select S) s) = (\<lambda>v. (Result v, s)) ` S"
  apply (simp add: select_def)
  apply transfer
  apply (force simp add: pure_post_state_def outcomes_def Inf_set_def Sup_post_state_def
      split: post_state.splits prod.splits)
  done

lemma reaches_select [simp]: "reaches (select S) s r t \<longleftrightarrow> (r \<in> Result ` S \<and> t = s)"
  apply (auto simp add: reaches_def outcomes_spec_monad)
  done


subsection \<open>\<^const>\<open>unknown\<close>\<close>

lemma succeeds_unknown[simp]: "succeeds unknown s"
  unfolding unknown_def by simp

lemma unknown_outcomes[outcomes_spec_monad]: "outcomes (run unknown s) = (\<lambda>v. (Result v, s)) ` UNIV"
  by simp

lemma reaches_unknown [simp]: "reaches unknown s r t \<longleftrightarrow> (r \<in> Result ` UNIV \<and> t = s)"
  unfolding unknown_def by simp


subsection \<open>\<^const>\<open>lift_state\<close>\<close>

lemma succeeds_lift_state_iff: "succeeds (lift_state R f) s \<longleftrightarrow> (\<forall>s'. R s s' \<longrightarrow> succeeds f s')"
  by (simp add: succeeds_holds lift_state_def Spec_inverse)


subsection \<open>const\<open>exec_concrete\<close>\<close>

lemma succeeds_exec_concrete_iff: "succeeds (exec_concrete st f) s \<longleftrightarrow> (\<forall>t. s = st t \<longrightarrow> succeeds f t)"
  by (simp add: exec_concrete_def succeeds_lift_state_iff)

lemma reaches_exec_concrete:
  assumes succeeds: "succeeds (exec_concrete st f) s"
  shows "reaches (exec_concrete st f) s r s' \<longleftrightarrow> (\<exists>t t'. s = st t \<and> reaches f t r t' \<and> s' = st t')"
  apply (simp add: reaches_def run_exec_concrete)
  apply standard
  subgoal
    by (auto simp add: map_post_state_def Sup_post_state_def image_def vimage_def
        split: prod.splits post_state.splits if_split_asm)
      (metis outcomes.simps(2))
  subgoal
    using succeeds
    apply (simp add: succeeds_def run_exec_concrete)
    by (auto simp add: map_post_state_def Sup_post_state_def image_def vimage_def top_post_state_def
        split: prod.splits post_state.splits if_split_asm)
      (metis apsnd_conv outcomes.simps(2) post_state.exhaust)
  done


subsection \<open>const\<open>exec_abstract\<close>\<close>

lemma succeeds_exec_abstract_iff[simp]: "succeeds (exec_abstract st f) s \<longleftrightarrow> succeeds f (st s)"
  by (simp add: exec_abstract_def succeeds_lift_state_iff)

lemma reaches_exec_abstract:
  shows "reaches (exec_abstract st f) s r s' \<longleftrightarrow> (\<exists>t'. reaches f (st s) r t' \<and> t' = st s')"
  by (cases "run f (st s)") (simp_all add: reaches_def run_exec_abstract)

subsection \<open>\<^const>\<open>bind_handle\<close>\<close>


lemma succeeds_bind_handle:
  "succeeds (bind_handle f g h) s \<longleftrightarrow>
     (succeeds f s \<and>
       (\<forall>x s'. reaches f s x s' \<longrightarrow>
         (case x of Exception e \<Rightarrow> succeeds (h e) s' | Result v \<Rightarrow> succeeds (g v) s')))"
  apply (cases "run f s")
  apply (simp_all add:
      succeeds_def run_bind_handle bot_post_state_def top_post_state_def
      image_iff eq_commute[of Failure] reaches_def
    split: prod.splits exception_or_result_splits)
  apply auto
  done

lemma succeeds_bind_handle_res:
  "succeeds (bind_handle (f::('s, 'a) res_monad) g h) s \<longleftrightarrow>
     (succeeds f s \<and>
       (\<forall>v s'. reaches f s (Result v) s' \<longrightarrow>
          succeeds (g v) s'))"
  by (simp add: succeeds_bind_handle)

lemma outcomes_bind_handle_succeeds: "succeeds (bind_handle f g h) s \<Longrightarrow>
  outcomes (run (bind_handle f g h) s) =
    \<Union> ((\<lambda>(r, s'). case r of  Exception e => outcomes (run (h e) s')
  | Result v \<Rightarrow> outcomes (run (g v) s'))
       ` (outcomes (run f s)))"
  apply (cases "run f s")
  apply (simp_all add: succeeds_bind_handle succeeds_def run_bind_handle bind_post_state_eq_top)
  apply (simp add: top_post_state_def image_iff split_beta'
              split: exception_or_result_splits)
  apply (intro SUP_cong refl)
  subgoal for X x by (cases "fst x") auto
  done

lemma outcomes_bind_handle_succeeds_res: "succeeds (bind_handle (f::('a, 's) res_monad) g h) s \<Longrightarrow>
  outcomes (run (bind_handle f g h) s) =
    \<Union> ((\<lambda>(r, s'). case r of  Exception e => {} | Result v \<Rightarrow> outcomes (run (g v) s'))
       ` (outcomes (run f s)))"
  apply (simp add: outcomes_bind_handle_succeeds)
  apply (auto split: exception_or_result_splits)
  done

lemma reaches_bind_handle: "reaches (bind_handle f g h) s r t \<longleftrightarrow>
       (succeeds (bind_handle f g h) s \<and>
         (\<exists>r' s'. reaches f s r' s' \<and>
            (case r' of
               Exception e \<Rightarrow> reaches (h e) s' r t
             | Result v \<Rightarrow> reaches (g v) s' r t)))"
  apply standard
  subgoal (* FIXME: understand this and make simp / auto proof *)
    apply (frule reaches_succeeds)
    apply (simp add: reaches_def outcomes_bind_handle_succeeds)
    apply (clarsimp split: exception_or_result_splits)
    apply (metis (no_types, opaque_lifting) Exception_eq_Result the_Exception_simp)
    apply (metis (no_types, opaque_lifting) Result_eq_Result the_Exception_simp the_Exception_Result)
    done
  subgoal
    apply (simp add: reaches_def outcomes_bind_handle_succeeds)
    by (auto split: exception_or_result_splits)
      (metis (mono_tags) case_exception_or_result_Exception case_exception_or_result_Result
        case_prod_conv exception_or_result_cases)
  done

lemma reaches_bind_handle_res: "reaches ((bind_handle (f::('a, 's) res_monad) g h)) s r t \<longleftrightarrow>
       (succeeds (bind_handle f g h) s \<and>
         (\<exists>v s'. reaches f s (Result v) s' \<and> reaches (g v) s' r t))"
  by (simp add: reaches_bind_handle)


subsection \<open>\<^const>\<open>bind\<close>\<close>

lemma succeeds_bind:
  "succeeds (bind f g) s \<longleftrightarrow>
     (succeeds f s \<and> (\<forall>v s'. reaches f s (Result v) s' \<longrightarrow> succeeds (g v) s'))"
  apply (simp add: bind_def succeeds_bind_handle)
  apply (auto split: exception_or_result_splits)
  done

lemma outcomes_bind_succeeds: "succeeds (bind f g) s \<Longrightarrow> outcomes (run (bind f g) s) =
  \<Union> ((\<lambda>(r, s'). case r of Exception e => {(Exception e, s')} | Result v \<Rightarrow> outcomes (run (g v) s'))
     ` (outcomes (run f s)))"
  by (simp add: bind_def outcomes_bind_handle_succeeds outcomes_spec_monad pure_post_state_def)

lemma outcomes_bind_succeeds_res: "succeeds (bind  (f::('a, 's) res_monad) g) s \<Longrightarrow> outcomes (run (bind f g) s) =
  \<Union> ((\<lambda>(r, s'). case r of Exception e => {} | Result v \<Rightarrow> outcomes (run (g v) s'))
     ` (outcomes (run f s)))"
  by (simp add: bind_def outcomes_bind_handle_succeeds_res outcomes_spec_monad)

lemma reaches_bind: "reaches (bind f g) s r t \<longleftrightarrow>
       (succeeds (bind f g) s \<and>
         (\<exists>r' s'. reaches f s r' s' \<and>
            (case r' of
               Exception e \<Rightarrow> r = Exception e \<and> t = s'
             | Result v \<Rightarrow> reaches (g v) s' r t)))"
  by (simp add: bind_def reaches_bind_handle)

lemma reaches_bind_res: "reaches ((bind f g)::('a, 's) res_monad) s r t \<longleftrightarrow>
       (succeeds (bind f g) s \<and>
         (\<exists>v s'. reaches f s (Result v) s' \<and> reaches (g v) s' r t))"
  by (simp add: bind_def reaches_bind_handle_res)

lemma runs_toD_outcomes: "f \<bullet> s \<lbrace> P \<rbrace> \<Longrightarrow> (x, s) \<in> outcomes (run f s) \<Longrightarrow> P x s"
  by (cases "run f s") (auto simp: runs_to.rep_eq)

lemma run_bind_reaches_cong:
  assumes f: "run f s = run f' s"
  assumes g: "\<And>v s'. succeeds f s \<Longrightarrow> succeeds f' s \<Longrightarrow>
     reaches f' s (Result v) s' \<Longrightarrow> run (g v) s' = run (g' v) s'"
  shows "run (bind f g) s = run (bind f' g') s"
  using f g  apply (cases "run f' s") apply (auto simp add: run_bind succeeds_def reaches_def intro!: SUP_cong
split : exception_or_result_splits)
  done

lemma refines_bind_right':
  "succeeds g t \<Longrightarrow> reaches g t (Result a) t' \<Longrightarrow>
    refines f (h a) s t' R \<Longrightarrow>
    refines f (g >>= h) s t R"
  by (force simp: refines_iff succeeds_bind reaches_bind)

lemma outcomes_empty_bind:
  assumes emp: "outcomes (run f s) = {}"
  shows "outcomes (run (f >>= g) s) = {}"
proof (cases "run f s")
  case Failure
  then show ?thesis  by (auto simp add: run_bind)
next
  case (Success x2)
  then show ?thesis using emp
    by (auto simp add: run_bind bot_post_state_def)
qed

lemma refines_bind_bind_exn: 
  assumes f: "refines f f' s s' Q"
  assumes ll: "\<And>e e' t t'.
    Q (Exn e, t) (Exn e', t') \<Longrightarrow>
    R (Exn e, t) (Exn e', t')"
  assumes lr: "\<And>e v' t t'.
    Q (Exn e, t) (Result v', t') \<Longrightarrow>
    refines (throw e) (g' v') t t' R" 
   assumes rl: "\<And>v e' t t'.
    Q (Result v, t) (Exn e', t') \<Longrightarrow>
    refines (g v) (throw e') t t' R" 
   assumes rr: "\<And>v v' t t'.
    Q (Result v, t) (Result v', t') \<Longrightarrow>
    refines (g v) (g' v') t t' R"
   shows "refines (f \<bind> g) (f' \<bind> g') s s' R"
  apply (rule refines_bind')
  apply (rule refines_mono [OF _ f])
  using assms
  apply (auto simp add: default_option_def Exn_def)
  done


subsection \<open>\<^const>\<open>assert\<close>\<close>

lemma outcomes_assert[outcomes_spec_monad]:
  "outcomes (run (assert P) s) = (if P then {(Result (), s)} else {})"
  by (simp add: assert_def outcomes_bind_succeeds outcomes_spec_monad)

lemma succeeds_assert[simp]: "succeeds (assert P) s \<longleftrightarrow> P"
  by (simp add: assert_def)

lemma reaches_assert[simp]: "reaches (assert P) s r t \<longleftrightarrow> (P \<and> r = Result () \<and> t = s)"
  by (simp add: assert_def)


subsection "\<^const>\<open>assume\<close>"

lemma outcomes_assume[outcomes_spec_monad]:
  "outcomes (run (assume P) s) =  (if P then {(Result (), s)} else {})"
  by (simp add: assume_def  outcomes_spec_monad)

lemma succeeds_assume[simp]: "succeeds (assume P) s"
  by (simp add: assume_def)

lemma reaches_assume[simp]: "reaches (assume P) s r t \<longleftrightarrow> (P \<and>  r = Result () \<and> t = s)"
  by (simp add: assume_def)


subsection \<open>\<^const>\<open>assume_outcome\<close>\<close>

lemma outcomes_assume_outcome[outcomes_spec_monad]:
  "outcomes (run (assume_outcome f) s) = f s"
  by simp

lemma succeeds_assume_outcome[simp]:
  "succeeds (assume_outcome f) s"
  by (simp add: succeeds_def top_post_state_def)

lemma reaches_assume_outcome[simp]:
  "reaches (assume_outcome f) s r t \<longleftrightarrow> (r, t) \<in> f s"
  by (simp add: reaches_def)

subsection \<open>\<^const>\<open>assume_result_and_state\<close>\<close>

lemma outcomes_assume_result_and_state[outcomes_spec_monad]:
  "outcomes (run (assume_result_and_state f) s) = ((\<lambda>(v, t). (Result v, t)) `  f s)"
  by simp

lemma succeeds_assume_result_and_state[simp]: "succeeds (assume_result_and_state f) s"
  by (simp add: assume_result_and_state_def succeeds_bind)

lemma Union_outcomes_split:
  "(\<Union>x\<in>f s.
         (outcomes (run (case x of (v, y) \<Rightarrow> g v y) s))) = (\<Union>(v, y)\<in> f s. outcomes (run (g v y) s))"
  using Sup.SUP_cong by auto

lemma reaches_assume_result_and_state [simp]: "reaches (assume_result_and_state f) s r t \<longleftrightarrow> (\<exists>v. r = Result v \<and> (v, t) \<in> f s)"
  by (auto simp add: reaches_def outcomes_spec_monad)

subsection \<open>\<^const>\<open>gets\<close>\<close>

lemma succeeds_gets[simp]: "succeeds (gets f) s"
  by (simp add: gets_def succeeds_bind)

lemma outcomes_gets[simp]: "outcomes (run (gets f) s) = {(Result (f s), s)}"
  by simp

lemma reaches_gets[simp]: "reaches (gets f) s r t \<longleftrightarrow> (r = Result (f s) \<and> t = s)"
  by (simp add: reaches_def)

subsection \<open>\<^const>\<open>assert_result_and_state\<close>\<close>

lemma succeeds_assert_result_and_state[simp]: "succeeds (assert_result_and_state f) s \<longleftrightarrow> f s \<noteq> {}"
  by (simp add: assert_result_and_state_def succeeds_bind)

lemma outcomes_assert_result_and_state[outcomes_spec_monad]:
  "outcomes (run (assert_result_and_state f) s) = (if f s = {} then {} else ((\<lambda>(v, t). (Result v, t)) `  f s))"
proof (cases "f s = {}")
  case True
  hence "\<not> succeeds (assert_result_and_state f) s" by simp
  hence "outcomes (run (assert_result_and_state f) s) = {}"
    by (simp add: not_succeeds_empty_outcomes)
  thus ?thesis by (simp add: True)
next
  case False
  then show ?thesis
    by (auto simp add: assert_result_and_state_def run_bind Sup_Success_pair
        pure_post_state_def)
qed

lemma reaches_assert_result_and_state [simp]: "reaches (assert_result_and_state f) s r t \<longleftrightarrow> (\<exists>v. r = Result v \<and> (v, t) \<in> f s)"
  by (auto simp add: reaches_def outcomes_spec_monad)


subsection "\<^const>\<open>assuming\<close>"

lemma succeeds_assuming[simp]: "succeeds (assuming g) s"
  by (simp add: assuming_def succeeds_bind)

lemma outcomes_assuming[outcomes_spec_monad]: "outcomes (run (assuming g) s) = (if g s then {(Result (), s)} else {})"
  by (simp add: run_assuming)

lemma reaches_assuming[simp]: "reaches (assuming g) s r t \<longleftrightarrow> (g s \<and> r = Result () \<and> t = s)"
  by (simp add: reaches_def outcomes_assuming)


subsection "\<^const>\<open>guard\<close>"

lemma succeeds_guard[simp]: "succeeds (guard g) s \<longleftrightarrow> g s"
  by (simp add: guard_def succeeds_bind)

lemma outcomes_guard[outcomes_spec_monad]: "outcomes (run (guard g) s) = (if g s then {(Result (), s)} else {})"
  by (simp add: run_guard)

lemma reaches_guard[simp]: "reaches (guard g) s r t \<longleftrightarrow> (g s \<and> r = Result () \<and> t = s)"
  by (simp add: reaches_def outcomes_guard)


subsection "\<^const>\<open>assert_opt\<close>"

lemma succeeds_assert_opt[simp]: "succeeds (assert_opt x) s \<longleftrightarrow> (\<exists>v. x = Some v)"
  by (simp add: assert_opt_def split: option.splits)

lemma outcomes_assert_opt[simp]:
  "outcomes (run (assert_opt x) s) = (case x of Some v \<Rightarrow> {(Result v, s)} | None \<Rightarrow> {})"
  by (simp split: option.splits)

lemma reaches_assert_opt[simp]: "reaches (assert_opt x) s r t \<longleftrightarrow> (\<exists>v. x = Some v \<and> r = Result v \<and> t = s)"
  by (simp add: reaches_def split: option.splits)

subsection "\<^const>\<open>gets_the\<close>"

lemma succeeds_gets_the[simp]: "succeeds (gets_the f) s \<longleftrightarrow> (\<exists>v. f s = Some v)"
  by (simp add: gets_the_def succeeds_bind)

lemma outcomes_gets_the[simp]:
  "outcomes (run (gets_the f) s) = (case f s of Some v \<Rightarrow> {(Result v, s)} | None \<Rightarrow> {})"
  by (simp split: option.splits)

lemma reaches_gets_the[simp]: "reaches (gets_the f) s r t \<longleftrightarrow> (\<exists>v. f s = Some v \<and> r = Result v \<and> t = s)"
  by (simp add: reaches_def split: option.splits)

subsection \<open>\<^const>\<open>modify\<close>\<close>

lemma outcomes_run_modify[outcomes_spec_monad]: "outcomes (run (modify f) s) = {(Result (), f s)}"
  by simp

lemma succeeds_modify[simp]: "succeeds (modify f) s"
  by (simp add: modify_def succeeds_bind)

lemma reaches_modify[simp]: "reaches (modify f) s r t \<longleftrightarrow> (r = Result () \<and> t = f s)"
  by (auto simp add: modify_def reaches_bind succeeds_bind)


subsection \<open>condition\<close>

lemma outcomes_condition:
  "outcomes (run (condition c f g) s) = (if c s then outcomes (run f s) else outcomes (run g s))"
proof (cases "succeeds (condition c f g) s")
  case True
  then show ?thesis by (auto simp add: condition_def outcomes_bind_succeeds outcomes_spec_monad
        split: exception_or_result_splits)
next
  case False
  then show ?thesis
    by (simp add: condition_def run_bind)
  qed

lemma succeeds_condition_iff:
  "succeeds (condition c f g) s \<longleftrightarrow> succeeds (if c s then f else g) s"
  by (simp add: condition_def succeeds_bind)

lemma reaches_condition_iff:
  "reaches (condition c f g) s r' s' \<longleftrightarrow> reaches (if c s then f else g) s r' s'"
  by (simp add:  reaches_def outcomes_condition)

lemma reaches_condition_True[simp]:
  "c s \<Longrightarrow> reaches (condition c f g) s r' s' \<longleftrightarrow> reaches f s r' s'"
  by (simp add: reaches_condition_iff)

lemma reaches_condition_False[simp]:
  "\<not> c s \<Longrightarrow> reaches (condition c f g) s r' s' \<longleftrightarrow> reaches g s r' s'"
  by (simp add: reaches_condition_iff)

lemma succeeds_condition_True[simp]:
  "c s \<Longrightarrow> succeeds (condition c f g) s \<longleftrightarrow> succeeds f s"
  by (simp add: succeeds_condition_iff)

lemma succeeds_condition_False[simp]:
  "\<not>(c s) \<Longrightarrow> succeeds (condition c f g) s \<longleftrightarrow> succeeds g s"
  by (simp add: succeeds_condition_iff)

subsection "\<^const>\<open>when\<close>"

lemma succeeds_when: "succeeds (when c f) s \<longleftrightarrow> \<not>c \<or> succeeds f s"
  unfolding when_def by (simp add: succeeds_condition_iff)

lemma outcomes_when[outcomes_spec_monad]:
  "outcomes (run (when c f) s) = (if c then outcomes (run f s) else {(Result (), s)})"
  by (simp add: run_when)

lemma reaches_when_iff:
  "reaches (when c f) s r' s' \<longleftrightarrow> (if c then reaches f  s r' s' else (r' = Result () \<and> s' = s))"
  by (simp add:  reaches_def outcomes_when)

subsection \<open>While\<close>

lemma reaches_whileLoop_cond_false:
  "reaches (whileLoop C B r) s (Result r') s' \<Longrightarrow> \<not> C r' s'"
  using runs_to_partial_whileLoop_cond_false[of C B r s]
  by (auto simp: reaches_succeeds runs_to_partial_def_old)

lemma bind_post_state_cong:
  "(\<And>r . r \<in> outcomes x \<Longrightarrow> g r = g' r) \<Longrightarrow> bind_post_state x g = bind_post_state x g'"
  by (cases x) simp_all

subsection \<open>\<^const>\<open>map_value\<close>\<close>

lemma succeeds_map_value[simp]: "succeeds (map_value f g) s \<longleftrightarrow> succeeds g s"
  by (simp add: succeeds_def run_map_value top_post_state_def
      bot_post_state_def split: post_state.splits)

lemma outcomes_map_value[outcomes_spec_monad]:
  "outcomes (run (map_value f g) s) = ((\<lambda>(v, s). (f v, s)) ` (outcomes (run g s)))"
  by (auto simp add: always_progress_def run_map_value
      top_post_state_def bot_post_state_def split: post_state.splits)

lemma reaches_map_value: "reaches (map_value f g) s r t \<longleftrightarrow> (\<exists>r'. reaches g s r' t \<and> r = f r')"
  by (auto simp add: reaches_def outcomes_map_value)

subsection \<open>\<^const>\<open>liftE\<close>\<close>

lemma succeeds_liftE[simp]: "succeeds (liftE f) s \<longleftrightarrow> succeeds f s"
  by (simp add: liftE_def)

lemma outcomes_liftE[outcomes_spec_monad]:
  "outcomes (run (liftE f) s) =
    ((\<lambda>(v, s). (map_exception_or_result (\<lambda>x. undefined) id v, s)) ` (outcomes (run f s)))"
  by (simp add: liftE_def outcomes_spec_monad)

lemma reaches_liftE: "reaches (liftE f) s r t \<longleftrightarrow> (\<exists>r'. reaches f s (Result r') t \<and> r = Result r')"
  by (auto simp add: liftE_def reaches_map_value)

lemma bind_cong1:
  fixes f::"('a, 's) res_monad"
  shows "\<lbrakk> f = f'; \<And>v s s'. reaches f s (Result v) s' \<Longrightarrow> g v = g' v \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  apply (rule spec_monad_ext)
  apply (rule run_bind_reaches_cong)
   apply auto
  done

lemma bind_liftE_cong1:
  fixes f::"('a, 's) res_monad"
  shows "\<lbrakk> f = f'; \<And>v s s'. reaches f s (Result v) s' \<Longrightarrow> g v = g' v \<rbrakk> \<Longrightarrow>
    (liftE f) >>= g = (liftE f') >>= g'"
  apply (rule spec_monad_ext)
  apply (rule run_bind_reaches_cong)
  apply (auto simp add: reaches_liftE)
  done

subsection \<open>\<^const>\<open>try\<close>\<close>

lemma succeeds_try[simp]: "succeeds (try f) s \<longleftrightarrow> succeeds f s"
  by (simp add: try_def)

lemma outcomes_try[outcomes_spec_monad]:
  "outcomes (run (try f) s) = ((\<lambda>(v, s). (unnest_exn v, s)) ` (outcomes (run f s)))"
  by (simp add: try_def outcomes_spec_monad)

lemma reaches_try: "reaches (try f) s r t \<longleftrightarrow> (\<exists>r'. reaches f s r' t \<and> r = unnest_exn r')"
  by (simp add: try_def reaches_map_value)

subsection \<open>\<^const>\<open>finally\<close>\<close>

lemma succeeds_finally[simp]: "succeeds (finally f) s \<longleftrightarrow> succeeds f s"
  by (simp add: finally_def)

lemma outcomes_finally[outcomes_spec_monad]:
  "outcomes (run (finally f) s) = ((\<lambda>(v, s). (unite v, s)) ` (outcomes (run f s)))"
  by (simp add: finally_def outcomes_spec_monad)

lemma reaches_finally: "reaches (finally f) s r t \<longleftrightarrow> (\<exists>r'. reaches f s r' t \<and> r = unite r')"
  by (simp add: finally_def reaches_map_value)

subsection \<open>\<^const>\<open>catch\<close>\<close>

lemma succeeds_catch: "succeeds (f <catch> h) s \<longleftrightarrow>
  (succeeds f s \<and>
    (\<forall>x s'. reaches f s x s' \<longrightarrow> (case x of Exn e \<Rightarrow> succeeds (h e) s' | Result v \<Rightarrow> True)))"
  unfolding catch_def
  by (fastforce simp add: succeeds_bind_handle default_option_def Exn_def split: exception_or_result_splits xval_splits)

lemma outcomes_catch_succeeds: "succeeds (f <catch> h) s \<Longrightarrow>
  outcomes (run (f <catch> h) s) =
    \<Union> ((\<lambda>(r, s'). case r of  Exn e => outcomes (run (h e) s') | Result v \<Rightarrow> {(Result v, s')})
       ` (outcomes (run f s)))"
  unfolding catch_def
  by (auto simp add: outcomes_bind_handle_succeeds default_option_def Exn_def 
      split: prod.splits exception_or_result_splits xval_splits)
    (metis Exn_def Exn_neq_Result the_Exception_simp fst_conv option.sel snd_conv  
      Pair_inject Result_eq_Result)+

lemma reaches_catch: "reaches (f <catch> h) s r t \<longleftrightarrow>
       (succeeds (f <catch> h) s \<and>
         (\<exists>r' s'. reaches f s r' s' \<and>
            (case r' of
               Exn e \<Rightarrow> reaches (h e) s' r t
             | Result v \<Rightarrow> r = Result v \<and> t = s')))"
  unfolding catch_def
  by (auto simp add: reaches_bind_handle default_option_def Exn_def split: prod.splits exception_or_result_splits xval_splits)
    (metis option.sel)+


subsection \<open>\<^const>\<open>check\<close>\<close>

lemma succeeds_check[simp]: "succeeds (check e p) s"
  by (simp add: succeeds_def run_check top_post_state_def)

lemma outcomes_check[outcomes_spec_monad]: "outcomes (run (check e p) s) =
  (if (\<exists>x. p s x) then ((\<lambda>x. (x, s)) ` (Result ` {x. p s x})) else {(Exn e, s)})"
by (simp add: run_check)

lemma reaches_check: "reaches (check e p) s r t \<longleftrightarrow>
  (t = s) \<and>
   (if (\<exists>x. p s x) then (\<exists>x. r = Result x \<and> p s x) else r = Exn e)"
  by (auto simp add: reaches_def outcomes_check)

lemma refines_bind_ok:
  "succeeds g t \<Longrightarrow> reaches g t (Result a) t' \<Longrightarrow>
    refines f (h a) s t' R \<Longrightarrow>
    refines f (g >>= h) s t R"
 by (fastforce simp: refines_iff succeeds_bind reaches_bind)

subsection \<open>\<^const>\<open>ignoreE\<close>\<close>

lemma succeeds_ignoreE[simp]:
  "succeeds (ignoreE f) s \<longleftrightarrow> (succeeds f s)"
  unfolding ignoreE_def
  by (auto simp add: succeeds_catch split: xval_splits)

lemma outcomes_ignoreE_succeeds: "succeeds f s \<Longrightarrow> outcomes (run (ignoreE f) s) =
   \<Union> ((\<lambda>(r, s'). case r of  Exn e => {} | Result v \<Rightarrow> {(Result v, s')})
       ` (outcomes (run f s)))"
  apply (subst (asm) succeeds_ignoreE [symmetric])
  by (simp add: ignoreE_def outcomes_catch_succeeds)

lemma reaches_ignoreE:
  "reaches (ignoreE f) s r t \<longleftrightarrow> (succeeds f s) \<and> (\<exists>v. r = Result v \<and> reaches f s (Result v) t)"
  apply (simp add:  reaches_catch succeeds_catch ignoreE_def)
  apply (fastforce split: xval_splits)
  done

subsection \<open>\<^const>\<open>bind_exception_or_result\<close>\<close>

lemma succeeds_bind_exception_or_result:
  "succeeds (bind_exception_or_result f g) s \<longleftrightarrow>
    succeeds f s \<and> (\<forall>v s'. reaches f s v s' \<longrightarrow> succeeds (g v) s')"
  by (cases "run f s";
    force simp: succeeds_def bind_exception_or_result.rep_eq
                bind_post_state_eq_top top_post_state_def reaches_def)

lemma reaches_bind_exception_or_result:
  "reaches (bind_exception_or_result f g) s r t \<longleftrightarrow>
    (succeeds (bind_exception_or_result f g) s \<and>
      (\<exists>r' s'. reaches f s r' s' \<and> reaches (g r') s' r t))"
  apply (cases "run f s")
  apply (simp_all add: reaches_def succeeds_def bind_exception_or_result.rep_eq)
  subgoal for X
    apply (cases "\<exists>x\<in>X. case x of (v, x) \<Rightarrow> run (g v) x = \<top>")
    apply (simp_all add: Sup_post_state_def image_iff split_beta' Bex_def Ball_def eq_commute
                 flip: top_post_state_def)
    by (metis outcomes.simps(2) post_state.exhaust top_post_state_def)
  done

lemma refines_bind_exception_or_result_strong:
  assumes f: "refines f f' s s' Q"
  assumes g: "\<And>r t r' t'. Q (r, t) (r', t') \<Longrightarrow> reaches f s r t \<Longrightarrow> reaches f' s' r' t' \<Longrightarrow>  refines (g r) (g' r') t t' R"
  shows "refines (bind_exception_or_result f g) (bind_exception_or_result f' g') s s' R"
  using refines_bind_exception_or_result refines_mono f g
  by (smt (verit, ccfv_threshold) case_prod_conv refines_strengthen')

subsection \<open>\<^const>\<open>bind_finally\<close>\<close>

lemma succeeds_bind_finally:
  "succeeds (bind_finally f g) s = (succeeds f s \<and> (\<forall>v s'. reaches f s v s' \<longrightarrow> succeeds (g v) s'))"
  by (rule succeeds_bind_exception_or_result)

lemma reaches_bind_finally: "reaches (bind_finally f g) s r t \<longleftrightarrow> (succeeds (bind_finally f g) s \<and> (\<exists>r' s'. reaches f s r' s' \<and> reaches (g r') s' r t))"
  by (rule reaches_bind_exception_or_result)

subsection \<open>\<^const>\<open>run_bind\<close>\<close>

lemma succeeds_run_bind:
  "succeeds (run_bind f t g) s \<longleftrightarrow> succeeds f t \<and> (\<forall>r t'. reaches f t r t' \<longrightarrow> succeeds (g r t') s)"
  by (cases "run f t")
     (force simp: succeeds_def run_run_bind top_post_state_def reaches_def
            split: post_state.splits)+

lemma reaches_run_bind: "reaches (run_bind f t g) s r s' \<longleftrightarrow>
         (succeeds (run_bind f t g) s) \<and>
         (\<exists>r' t'. reaches f t r' t' \<and> reaches (g r' t') s r s')"
  apply (cases "run f t")
  apply (simp_all add: reaches_def run_run_bind succeeds_run_bind)
  apply (simp add: succeeds_def split_beta')
  subgoal for A
    apply (cases "\<forall>r t'. (r, t') \<in> A \<longrightarrow> run (g r t') s \<noteq> \<top>")
    subgoal by (subst outcomes_Sup; force simp flip: top_post_state_def)
    subgoal
      apply (subst Sup_eq_Failure[THEN iffD2])
      apply (force simp flip: top_post_state_def)
      apply auto
      done
    done
  done


lemma runs_to_partial_reaches: "f \<bullet> s ?\<lbrace> reaches f s \<rbrace>"
  apply (cases "run f s")
  apply (auto simp add: runs_to_partial_def reaches_def)
  done

lemma refines_strengthen_reaches:
  assumes f_g: "refines f g s t R" 
  assumes reach: "(\<And>x s' y t'. R (x, s') (y, t') \<Longrightarrow> reaches f s x s' \<Longrightarrow> reaches g t y t'  \<Longrightarrow> Q (x, s') (y, t'))"
  shows "refines f g s t Q"
  apply (rule refines_strengthen [OF f_g  runs_to_partial_reaches  runs_to_partial_reaches] )
  using reach
  by blast


lemma refines_bind_bind_strong': 
  assumes f: "refines f f' s s' Q"
  assumes Ex_Ex: "(\<And>e e' t t'.
    Q (Exception e, t) (Exception e', t') \<Longrightarrow>
    e \<noteq> default \<Longrightarrow>
    e' \<noteq> default \<Longrightarrow>
    reaches f s (Exception e) t \<Longrightarrow>
    reaches f' s' (Exception e') t' \<Longrightarrow>
    R (Exception e, t) (Exception e', t'))"
  assumes Res_Ex: "(\<And>e v' t t'.
    Q (Exception e, t) (Result v', t') \<Longrightarrow>
    e \<noteq> default \<Longrightarrow>
    reaches f s (Exception e) t \<Longrightarrow>
    reaches f' s' (Result v') t' \<Longrightarrow>
    refines (yield (Exception e)) (g' v') t t' R)"
  assumes Ex_Ex: "(\<And>v e' t t'.
    Q (Result v, t) (Exception e', t') \<Longrightarrow>
    e' \<noteq> default \<Longrightarrow>
    reaches f s (Result v) t \<Longrightarrow>
    reaches f' s' (Exception e') t' \<Longrightarrow>
    refines (g v) (yield (Exception e')) t t' R)"
  assumes Res_Res: "(\<And>v v' t t'.
    Q (Result v, t) (Result v', t') \<Longrightarrow>
    reaches f s (Result v) t \<Longrightarrow>
    reaches f' s' (Result v') t' \<Longrightarrow>
    refines (g v) (g' v') t t' R)"
  shows "refines (f \<bind> g) (f' \<bind> g') s s' R"
  apply (rule refines_bind')
  apply (rule refines_strengthen_reaches [OF f])
  apply (auto intro: assms)
  done


lemma rel_spec_monad_bind_strong:
  assumes f_f': "rel_spec_monad S P f f'"
  assumes Ex_Ex: "\<And>e e' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P (Exception e) (Exception e') \<Longrightarrow> e \<noteq> default \<Longrightarrow> e' \<noteq> default \<Longrightarrow> 
    reaches f s (Exception e) t \<Longrightarrow> reaches f' s' (Exception e') t' \<Longrightarrow>
    Q (Exception e) (Exception e')"
  assumes Ex_Res: "\<And>e v' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P (Exception e) (Result v') \<Longrightarrow> e \<noteq> default \<Longrightarrow> 
    reaches f s (Exception e) t \<Longrightarrow> reaches f' s' (Result v') t' \<Longrightarrow> 
    rel_spec_monad S Q (yield (Exception e)) (g' v')"
  assumes Res_Ex: "\<And>v e' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P (Result v) (Exception e') \<Longrightarrow> e' \<noteq> default \<Longrightarrow>
     reaches f s (Result v) t \<Longrightarrow> reaches f' s' (Exception e') t' \<Longrightarrow> 
     rel_spec_monad S Q (g v) (yield (Exception e'))"
  assumes Res_Res: "\<And>v v' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P (Result v) (Result v') \<Longrightarrow>
     reaches f s (Result v) t \<Longrightarrow> reaches f' s' (Result v') t' \<Longrightarrow> 
     rel_spec_monad S Q (g v) (g' v')"
  shows "rel_spec_monad S Q (f \<bind> g) (f' \<bind> g')"
  apply (simp add: rel_spec_monad_iff_refines)
  apply (clarify, intro conjI)
  subgoal for s t
    apply (rule refines_bind_bind_strong' [where Q="(rel_prod P S)"])
    subgoal using f_f' by (auto simp add: rel_spec_monad_iff_refines)
    subgoal
      using Ex_Ex by auto
    subgoal
      using Ex_Res by (auto simp add: rel_spec_monad_iff_refines)
    subgoal
      using Res_Ex by (auto simp add: rel_spec_monad_iff_refines)
    subgoal
      using Res_Res by (auto simp add: rel_spec_monad_iff_refines)
    done
  subgoal for s t
    apply (rule refines_bind_bind_strong' [where Q="(rel_prod P\<inverse>\<inverse> S\<inverse>\<inverse>)"])
    subgoal using f_f' by (auto simp add: rel_spec_monad_iff_refines)
    subgoal
      using Ex_Ex by auto
    subgoal
      using Res_Ex by (auto simp add: rel_spec_monad_iff_refines)
    subgoal
      using Ex_Res by (auto simp add: rel_spec_monad_iff_refines)
    subgoal
      using Res_Res by (auto simp add: rel_spec_monad_iff_refines)
    done
  done

lemma rel_spec_monad_bind_strong_exn:
  assumes f_f': "rel_spec_monad S P f f'"
  assumes Ex_Ex: "\<And>e e' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P (Exn e) (Exn e') \<Longrightarrow> 
    reaches f s (Exn e) t \<Longrightarrow> reaches f' s' (Exn e') t' \<Longrightarrow>
    Q (Exn e) (Exn e')"
  assumes Ex_Res: "\<And>e v' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P (Exn e) (Result v') \<Longrightarrow> 
    reaches f s (Exn e) t \<Longrightarrow> reaches f' s' (Result v') t' \<Longrightarrow> 
    rel_spec_monad S Q (throw e) (g' v')"
  assumes Res_Ex: "\<And>v e' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P (Result v) (Exn e') \<Longrightarrow>
     reaches f s (Result v) t \<Longrightarrow> reaches f' s' (Exn e') t' \<Longrightarrow> 
     rel_spec_monad S Q (g v) (throw e')"
  assumes Res_Res: "\<And>v v' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P (Result v) (Result v') \<Longrightarrow>
     reaches f s (Result v) t \<Longrightarrow> reaches f' s' (Result v') t' \<Longrightarrow> 
     rel_spec_monad S Q (g v) (g' v')"
  shows "rel_spec_monad S Q (f \<bind> g) (f' \<bind> g')"
  apply (rule rel_spec_monad_bind_strong [OF f_f'])
  subgoal using Ex_Ex by (auto simp add: Exn_def default_option_def)
  subgoal using Ex_Res by (auto simp add: Exn_def default_option_def)
  subgoal using Res_Ex by (auto simp add: Exn_def default_option_def)
  subgoal using Res_Res by (auto)
  done


lemma rel_spec_monad_rel_xval_bind_strong:
  assumes f_f': "rel_spec_monad S (rel_xval L P) f f'"
  assumes Res_Res: "\<And>v v' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P v v' \<Longrightarrow>
     reaches f s (Result v) t \<Longrightarrow> reaches f' s' (Result v') t' \<Longrightarrow> 
     rel_spec_monad S (rel_xval L R) (g v) (g' v')"
  shows "rel_spec_monad S (rel_xval L R) (f \<bind> g) (f' \<bind> g')"
  apply (rule rel_spec_monad_bind_strong_exn [OF f_f'])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal using Res_Res by auto
  done

lemma rel_spec_monad_bind_exception_or_result_strong:
  assumes f_f': "rel_spec_monad S P f f'"
  assumes g_g': "\<And>r r' s s' t t'. S s s' \<Longrightarrow> S t t' \<Longrightarrow> P r r' \<Longrightarrow>
    reaches f s r t \<Longrightarrow> reaches f' s' r' t' \<Longrightarrow>
    rel_spec_monad S Q (g r) (g' r')"
  shows "rel_spec_monad S Q (bind_exception_or_result f g) (bind_exception_or_result f' g')"
  apply (simp add: rel_spec_monad_iff_refines)
  apply (clarify, intro conjI)
  subgoal for s t
    apply (rule refines_bind_exception_or_result_strong [where Q="rel_prod P S"])
    subgoal
      using f_f' by (auto simp add: rel_spec_monad_iff_refines)
    subgoal
      using g_g' by (auto simp add: rel_spec_monad_iff_refines)
    done
  subgoal for s t
    apply (rule refines_bind_exception_or_result_strong [where Q="rel_prod P\<inverse>\<inverse> S\<inverse>\<inverse>"])
    subgoal
      using f_f' by (auto simp add: rel_spec_monad_iff_refines)
    subgoal
      using g_g' by (auto simp add: rel_spec_monad_iff_refines)
    done
  done

end