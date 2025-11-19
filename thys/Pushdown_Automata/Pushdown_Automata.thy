section \<open>Pushdown Automata (PDA)\<close>

theory Pushdown_Automata
imports Main
begin

subsection \<open>Definitions\<close>

text \<open>In the following, we define \emph{pushdown automata} and show some basic properties of them.
The formalization is based on the Lean formalization by Leichtfried\cite{lean}.\<close>

text \<open>We represent the transition function $\delta$ by splitting it into two different functions
$\delta_1 : Q \times \Sigma \times \Gamma \rightarrow Q \times \Gamma^*$ and
$\delta_2 : Q \times \Gamma \rightarrow Q \times \Gamma^*$,
where $\delta_1(q, a, Z) := \delta(q, a, Z)$ and $\delta_2(q, Z) := \delta(q, \epsilon, Z)$.\<close>

record ('q,'a,'s) pda = init_state    :: 'q
                        init_symbol   :: 's 
                        final_states  :: "'q set"
                        delta     :: "'q \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('q \<times> 's list) set"
                        delta_eps       :: "'q \<Rightarrow> 's \<Rightarrow> ('q \<times> 's list) set"

locale pda =
  fixes M :: "('q :: finite, 'a :: finite, 's :: finite) pda"
  assumes finite_delta: "finite (delta M p a Z)"
      and finite_delta_eps: "finite (delta_eps M p Z)"
begin

notation delta ("\<delta>")
notation delta_eps ("\<delta>\<epsilon>")

(*
TODO?
fun step\<^sub>1 :: "'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool" where
*)
fun step :: "'q \<times> 'a list \<times> 's list \<Rightarrow> ('q \<times> 'a list \<times> 's list) set" where
  "step (p, a#w, Z#\<alpha>) = {(q, w, \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> \<delta> M p a Z}
                        \<union> {(q, a#w, \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> \<delta>\<epsilon> M p Z}"
| "step (p, [], Z#\<alpha>) = {(q, [], \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> \<delta>\<epsilon> M p Z}"
| "step (_, _, []) = {}"

fun step\<^sub>1 :: "'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool"
  ("(_ \<leadsto> _)" [50, 50] 50) where
  "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<in> step (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)"

definition steps :: "'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool"
  ("(_ \<leadsto>* _)" [50, 50] 50) where
  "steps \<equiv> step\<^sub>1 ^**"

(* TODO:
definition stepn :: "nat \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool" where
"stepn n = step\<^sub>1^^n"
*)
inductive stepn :: "nat \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool" where
refl\<^sub>n: "stepn 0 (p, w, \<alpha>) (p, w, \<alpha>)" |
step\<^sub>n: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> step\<^sub>1 (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"

abbreviation stepsn ("(_ /\<leadsto>'(_')/ _)" [50, 0, 50] 50) where
"c \<leadsto>(n) c' \<equiv> stepn n c c'"

text \<open>The language accepted by empty stack:\<close>

definition accept_stack :: "'a list set" where
  "accept_stack \<equiv> {w. \<exists>q. (init_state M, w, [init_symbol M]) \<leadsto>* (q, [], [])}"

text \<open>The language accepted by final state:\<close>

definition accept_final :: "'a list set" where 
  "accept_final \<equiv> {w. \<exists>q \<in> final_states M. \<exists>\<gamma>. (init_state M, w, [init_symbol M]) \<leadsto>* (q, [], \<gamma>)}"

subsection \<open>Basic Lemmas\<close>

subsubsection \<open>\<^const>\<open>step\<close> and \<^const>\<open>step\<^sub>1\<close>\<close>

lemma card_trans_step: "card (\<delta> M p a Z) = card {(q, w, \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> \<delta> M p a Z}"
  by (rule bij_betw_same_card[where ?f = "\<lambda>(q,\<beta>). (q, w, \<beta>@\<alpha>)"]) (auto simp: bij_betw_def inj_on_def)

lemma card_eps_step: "card (\<delta>\<epsilon> M p Z) = card {(q, w, \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> \<delta>\<epsilon> M p Z}"
  by (rule bij_betw_same_card[where ?f = "\<lambda>(q,\<beta>). (q, w, \<beta>@\<alpha>)"]) (auto simp: bij_betw_def inj_on_def)

lemma card_empty_step: "card (step (p, [], Z#\<alpha>)) = card (\<delta>\<epsilon> M p Z)"
  by (rule sym) (simp add: card_eps_step)

lemma finite_delta_step: "finite {(q, w, \<beta> @ \<alpha>) |q \<beta>. (q, \<beta>) \<in> \<delta> M p a Z}" (is "finite ?A")
  using bij_betw_finite[of "\<lambda>(q,\<beta>). (q, w, \<beta>@\<alpha>)" "\<delta> M p a Z" ?A] by (fastforce simp add: bij_betw_def inj_on_def finite_delta)

lemma finite_delta_eps_step: "finite {(q, w, \<beta> @ \<alpha>) |q \<beta>. (q, \<beta>) \<in> \<delta>\<epsilon> M p Z}" (is "finite ?A")
  using bij_betw_finite[of "\<lambda>(q,\<beta>). (q, w, \<beta>@\<alpha>)" "\<delta>\<epsilon> M p Z" ?A] by (fastforce simp add: bij_betw_def inj_on_def finite_delta_eps)

lemma card_nonempty_step: "card (step (p, a#w, Z#\<alpha>)) = card (\<delta> M p a Z) + card (\<delta>\<epsilon> M p Z)"
  apply (simp only: step.simps)
  apply (subst card_trans_step)
  apply (subst card_eps_step)
  apply (rule card_Un_disjoint)
    apply (auto simp: finite_delta_step finite_delta_eps_step)
  done

lemma finite_step: "finite (step (p, w, Z#\<alpha>))"
  by (cases w) (auto simp: finite_delta_step finite_delta_eps_step)

lemma step\<^sub>1_nonempty_stack: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> \<exists>Z' \<alpha>'. \<alpha>\<^sub>1 = Z'#\<alpha>'"
  by (cases \<alpha>\<^sub>1) auto

lemma step\<^sub>1_empty_stack: "\<not> (p\<^sub>1, w\<^sub>1, []) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by simp

lemma step\<^sub>1_rule: "(p\<^sub>1, w\<^sub>1, Z#\<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>\<^sub>1 \<and> (p\<^sub>2, \<beta>) \<in> \<delta>\<epsilon> M p\<^sub>1 Z) 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>\<^sub>1 \<and> (p\<^sub>2, \<beta>) \<in> \<delta> M p\<^sub>1 a Z)"
  by (cases w\<^sub>1) auto

lemma step\<^sub>1_rule_ext: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (\<exists>Z' \<alpha>'. \<alpha>\<^sub>1 = Z'#\<alpha>' \<and> ((\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> \<delta>\<epsilon> M p\<^sub>1 Z') 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> \<delta> M p\<^sub>1 a Z')))" (is "?l \<longleftrightarrow> ?r")
  apply (rule iffI)
   apply (metis step\<^sub>1_nonempty_stack step\<^sub>1_rule)
  apply (use step\<^sub>1_rule in force)
  done

lemma step\<^sub>1_stack_app: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<gamma>) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<gamma>)"
  using step\<^sub>1_rule_ext by auto


subsubsection \<open>\<^const>\<open>steps\<close>\<close>

lemma steps_refl: "(p, w, \<alpha>) \<leadsto>* (p, w, \<alpha>)"
  by (simp add: steps_def)

lemma steps_trans: "\<lbrakk> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2); (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<leadsto>* (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<rbrakk>
 \<Longrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
  unfolding steps_def using rtranclp_trans[where ?r = step\<^sub>1] by blast

lemma step\<^sub>1_steps: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by (simp add: steps_def r_into_rtranclp)

lemma steps_empty_stack: "(p\<^sub>1, w\<^sub>1, []) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> p\<^sub>1 = p\<^sub>2 \<and> w\<^sub>1 = w\<^sub>2 \<and> \<alpha>\<^sub>2 = []"
  unfolding steps_def using converse_rtranclpE2 by fastforce

lemma steps_induct2[consumes 1]:
  assumes "x1 \<leadsto>* x2"
      and "\<And>p w \<alpha>. P (p, w, \<alpha>) (p, w, \<alpha>)"
      and "\<And>p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3. (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<leadsto>* (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> 
                P (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> P (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
    shows "P x1 x2"
using assms[unfolded steps_def]
proof(induction rule: converse_rtranclp_induct)
  case base thus ?case by (metis prod_cases3)
next
  case step thus ?case by simp (metis prod_cases3 step\<^sub>1.simps)
qed

lemma steps_induct2_bw[consumes 1, case_names base step]:
  assumes "steps x1 x2"
      and "\<And>p w \<alpha>. P (p, w, \<alpha>) (p, w, \<alpha>)"
      and "\<And>p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3. (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<leadsto> (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> 
                P (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> P (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
    shows "P x1 x2"
  using assms[unfolded steps_def]
proof(induction rule: rtranclp_induct)
  case base
  then show ?case by (metis prod_cases3)
next
  case (step)
  then show ?case by simp (metis prod_cases3 step\<^sub>1.simps)
qed

lemmas converse_rtranclp_induct3_aux =
  converse_rtranclp_induct [of step\<^sub>1 "(ax, ay, az)" "(bx, by, bz)", split_rule]
lemmas steps_induct =
  converse_rtranclp_induct3_aux [of M, folded steps_def,consumes 1, case_names refl step]

lemma step\<^sub>1_word_app: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> step\<^sub>1 (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
  using step\<^sub>1_rule_ext by simp

lemma decreasing_word: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> \<exists>w. w\<^sub>1 = w @ w\<^sub>2"
  by (induction rule: steps_induct) (use step\<^sub>1_rule_ext in auto)


subsubsection \<open>\<^const>\<open>stepn\<close>\<close>

inductive_cases stepn_zeroE[elim!]: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(0) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
thm stepn_zeroE
inductive_cases stepn_sucE[elim!]: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(Suc n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
thm stepn_sucE

declare stepn.intros[simp, intro]

lemma step\<^sub>1_stepn_one: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by auto

lemma stepn_split_last: "(\<exists>p' w' \<alpha>'. (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p', w', \<alpha>') \<and> (p', w', \<alpha>') \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) 
                                \<longleftrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(Suc n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by auto

lemma stepn_split_first: "(\<exists>p' w' \<alpha>'. (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p', w', \<alpha>') \<and> (p', w', \<alpha>') \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) 
                                \<longleftrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(Suc n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain p' w' \<alpha>' where r1: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p', w', \<alpha>')" and rN: "(p', w', \<alpha>') \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by blast
  from rN r1 show ?r
    by (induction rule: stepn.induct) auto
next
  show "?r \<Longrightarrow> ?l"
    by (induction "Suc n" "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
       (metis old.nat.exhaust refl\<^sub>n step\<^sub>n stepn_zeroE)
qed

lemma stepn_induct[consumes 1, case_names basen stepn]:
  assumes "x1 \<leadsto>(n) x2"
      and "\<And>p w \<alpha>. P 0 (p, w, \<alpha>) (p, w, \<alpha>)"
      and "\<And>n p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3. (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<leadsto>(n) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> 
                P n (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> P (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
    shows "P n x1 x2"
using assms proof (induction n arbitrary: x1)
  case 0
  obtain p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 where [simp]: "x1 = (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" and [simp]: "x2 = (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    by (metis prod_cases3)
  from "0.prems"(1) have "x1 = x2" by auto
  with "0.prems"(2) show ?case by simp
next
  case (Suc n)
  obtain p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 where [simp]: "x1 = (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" and x2_def[simp]: "x2 = (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    by (metis prod_cases3)
  from Suc.prems(1) obtain p' w' \<alpha>' where 
      r1: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p', w', \<alpha>')" and rN: "(p', w', \<alpha>') \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using stepn_split_first[of p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2] by auto
  have "P n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using Suc.IH[unfolded x2_def, OF rN Suc.prems(2,3)] by simp
  then show ?case
    using Suc.prems(3)[OF r1 rN] by simp
qed

lemma stepn_trans:
  assumes "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<leadsto>(m) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
    shows "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n+m) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
using assms(2,1) by (induction rule: stepn.induct) auto

lemma stepn_steps: "(\<exists>n. (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) \<longleftrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof 
  assume ?l
  then obtain n where "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by blast
  thus "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
    apply (induction rule: stepn.induct) 
     apply (rule steps_refl)
    apply (simp add: step\<^sub>1_steps steps_trans)
    done
next
  show "?r \<Longrightarrow> ?l"
    by (induction rule: steps_induct) (use stepn_split_first in blast)+
qed

lemma stepn_word_app: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    by (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct) (use step\<^sub>1_word_app in auto)
next
  show "?r \<Longrightarrow> ?l"
  proof (induction n "(p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 \<alpha>\<^sub>3 w\<^sub>3)
    obtain w' where w\<^sub>2_def: "w\<^sub>2 = w' @ w\<^sub>3 @ w"
      using decreasing_word[OF step\<^sub>1_steps[OF step\<^sub>n(3)]] by blast

    with step\<^sub>n(2) have "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w' @ w\<^sub>3, \<alpha>\<^sub>2)" by simp

    moreover from step\<^sub>n(3) w\<^sub>2_def have "(p\<^sub>2, w' @ w\<^sub>3, \<alpha>\<^sub>2) \<leadsto> (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
      using step\<^sub>1_word_app by force

    ultimately show ?case by simp
  qed simp
qed

lemma steps_word_app: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
  using stepn_steps stepn_word_app by metis

lemma stepn_not_refl_split_first:
  assumes "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<noteq> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>n' p' w' \<alpha>'. n = Suc n' \<and> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p', w', \<alpha>') \<and> (p', w', \<alpha>') \<leadsto>(n') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms have "n > 0" by fast
  then obtain n' where "n = Suc n'"
    using not0_implies_Suc by blast
  with assms(1) show ?thesis
    using stepn_split_first by simp
qed

lemma stepn_not_refl_split_last:
  assumes "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<noteq> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>n' p' w' \<alpha>'. n = Suc n' \<and> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n') (p', w', \<alpha>') \<and> (p', w', \<alpha>') \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms have "n > 0" by fast
  then obtain n' where "n = Suc n'"
    using not0_implies_Suc by blast
  with assms(1) show ?thesis
    using stepn_split_last by simp
qed

lemma steps_not_refl_split_first:
  assumes "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<noteq> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>p' w' \<alpha>'. (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p', w', \<alpha>') \<and> (p', w', \<alpha>') \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
using assms stepn_steps stepn_not_refl_split_first by metis

lemma steps_not_refl_split_last:
  assumes "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<noteq> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>p' w' \<alpha>'. (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p', w', \<alpha>') \<and> (p', w', \<alpha>') \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
using assms stepn_steps stepn_not_refl_split_last by metis

lemma stepn_stack_app: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<beta>)"
  by (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct) (fastforce intro: step\<^sub>1_stack_app)+

lemma steps_stack_app: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<beta>)"
  using stepn_steps stepn_stack_app by metis

lemma step\<^sub>1_stack_drop: 
  assumes "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<gamma>) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<gamma>)"
      and "\<alpha>\<^sub>1 \<noteq> []"
    shows "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms(1) obtain Z' \<alpha>' where \<alpha>\<^sub>1_\<gamma>_def: "\<alpha>\<^sub>1 @ \<gamma> = Z' # \<alpha>'" and
           rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2@\<gamma> = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> \<delta>\<epsilon> M p\<^sub>1 Z') 
                     \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2@\<gamma> = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> \<delta> M p\<^sub>1 a Z')"
    using step\<^sub>1_rule_ext by auto
  from \<alpha>\<^sub>1_\<gamma>_def assms(2) obtain \<alpha>'' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z' # \<alpha>''" and \<alpha>'_def: "\<alpha>' = \<alpha>'' @ \<gamma>"
    using Cons_eq_append_conv[of Z' \<alpha>' \<alpha>\<^sub>1 \<gamma>] by auto
  from rule \<alpha>'_def have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>'' \<and> (p\<^sub>2, \<beta>) \<in> \<delta>\<epsilon> M p\<^sub>1 Z') 
           \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>'' \<and> (p\<^sub>2,\<beta>) \<in> \<delta> M p\<^sub>1 a Z')" by auto
  with \<alpha>\<^sub>1_def show ?thesis
    using step\<^sub>1_rule by simp
qed

lemma stepn_reads_input:
  assumes "(p\<^sub>1, a # w, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, [], \<alpha>\<^sub>2)"
  shows "\<exists>n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2. n = Suc n' \<and> k \<le> n' \<and> (p\<^sub>1, a # w, \<alpha>\<^sub>1) \<leadsto>(k) (q\<^sub>1, a # w, \<gamma>\<^sub>1) \<and> 
            (q\<^sub>1, a # w, \<gamma>\<^sub>1) \<leadsto> (q\<^sub>2, w, \<gamma>\<^sub>2) \<and> (q\<^sub>2, w, \<gamma>\<^sub>2) \<leadsto>(n'-k) (p\<^sub>2, [], \<alpha>\<^sub>2)"
using assms proof (induction n "(p\<^sub>1, a # w, \<alpha>\<^sub>1)" "(p\<^sub>2, [] :: 'a list, \<alpha>\<^sub>2)" arbitrary: p\<^sub>1 \<alpha>\<^sub>1 rule: stepn_induct)
  case (stepn n p\<^sub>1 \<alpha>\<^sub>1 p' w' \<alpha>')
  from stepn(1) have case_dist: "w' = w \<or> w' = a#w" (is "?l \<or> ?r")
    using step\<^sub>1_rule_ext by auto
  show ?case proof (rule disjE[OF case_dist])
    assume l: ?l 

    from l stepn(1) have "step\<^sub>1 (p\<^sub>1, a # w, \<alpha>\<^sub>1) (p', w, \<alpha>')" by simp

    moreover from l stepn(2) have "(p', w, \<alpha>') \<leadsto>(n) (p\<^sub>2, [], \<alpha>\<^sub>2)" by simp

    ultimately show ?case by fastforce
  next 
    assume r: ?r
    obtain n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where IH1: "n = Suc n'" and IH2: "k \<le> n'" and 
        IH3: "(p', a # w, \<alpha>') \<leadsto>(k) (q\<^sub>1, a # w, \<gamma>\<^sub>1)" and IH4: "(q\<^sub>1, a # w, \<gamma>\<^sub>1) \<leadsto> (q\<^sub>2, w, \<gamma>\<^sub>2)" and 
        IH5: "(q\<^sub>2, w, \<gamma>\<^sub>2) \<leadsto>(n'-k) (p\<^sub>2, [], \<alpha>\<^sub>2)"
      using stepn(3)[OF r] by blast

    from IH1 IH2 have "Suc k \<le> n" by simp

    moreover from stepn(1) r IH3 have "(p\<^sub>1, a # w, \<alpha>\<^sub>1) \<leadsto>(Suc k) (q\<^sub>1, a # w, \<gamma>\<^sub>1)"
      using stepn_split_first by blast

    moreover from IH1 IH5 have "stepn (n - Suc k) (q\<^sub>2, w, \<gamma>\<^sub>2) (p\<^sub>2, [], \<alpha>\<^sub>2)" by simp

    ultimately show ?case
      using IH4 by metis
  qed
qed

lemma split_word:
"(p\<^sub>1, w @ w', \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, [], \<alpha>\<^sub>2) \<Longrightarrow> \<exists>k q \<gamma>. k \<le> n \<and> (p\<^sub>1, w, \<alpha>\<^sub>1) \<leadsto>(k) (q, [], \<gamma>) \<and> (q, w', \<gamma>) \<leadsto>(n-k) (p\<^sub>2, [], \<alpha>\<^sub>2)"
proof (induction w arbitrary: n p\<^sub>1 \<alpha>\<^sub>1)
  case (Cons a w)
  from Cons(2) obtain n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where n_def: "n = Suc n'" and k_lesseq_n': "k \<le> n'" and stepk: "(p\<^sub>1, a # (w @ w'), \<alpha>\<^sub>1) \<leadsto>(k) (q\<^sub>1, a # (w @ w'), \<gamma>\<^sub>1)" and
                    step1: "(q\<^sub>1, a # (w @ w'), \<gamma>\<^sub>1) \<leadsto> (q\<^sub>2, w @ w', \<gamma>\<^sub>2)" and stepnk: "(q\<^sub>2, w @ w', \<gamma>\<^sub>2) \<leadsto>(n'-k) (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using stepn_reads_input[of n p\<^sub>1 a "w @ w'" \<alpha>\<^sub>1 p\<^sub>2 \<alpha>\<^sub>2] by auto
  obtain k'' q \<gamma> where k''_lesseq_n'k: "k'' \<le> n'-k" and stepk'': "(q\<^sub>2, w, \<gamma>\<^sub>2) \<leadsto>(k'') (q, [], \<gamma>)" and stepn'kk'': "(q, w', \<gamma>) \<leadsto>(n'-k-k'') (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using Cons.IH[OF stepnk] by blast
  from stepk step1 have stepSuck: "stepn (Suc k) (p\<^sub>1, a # w, \<alpha>\<^sub>1) (q\<^sub>2, w, \<gamma>\<^sub>2)"
    using stepn_word_app[of "Suc k" p\<^sub>1 "a # w" \<alpha>\<^sub>1 q\<^sub>2 w \<gamma>\<^sub>2 w'] by simp

  have "(p\<^sub>1, a # w, \<alpha>\<^sub>1) \<leadsto>(Suc k + k'') (q, [], \<gamma>)" 
    using stepn_trans[OF stepSuck stepk''] .

  moreover from n_def stepn'kk'' have "(q, w', \<gamma>) \<leadsto>(n - (Suc k + k'')) (p\<^sub>2, [], \<alpha>\<^sub>2)" by simp

  moreover from n_def k_lesseq_n' k''_lesseq_n'k have "Suc k + k'' \<le> n" by simp

  ultimately show ?case by blast
qed fastforce

lemma split_stack: 
"stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>\<^sub>1) (p\<^sub>2, [], []) \<Longrightarrow> \<exists>p' m\<^sub>1 m\<^sub>2 y y'. w\<^sub>1 = y @ y' \<and> m\<^sub>1 + m\<^sub>2 = n 
                                          \<and> (p\<^sub>1, y, \<alpha>\<^sub>1) \<leadsto>(m\<^sub>1) (p', [], []) \<and> (p', y', \<beta>\<^sub>1) \<leadsto>(m\<^sub>2) (p\<^sub>2, [], [])"
proof (induction n arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1)
  case (Suc n)
  show ?case proof (cases \<alpha>\<^sub>1)
    case Nil

    from Nil have "stepn 0 (p\<^sub>1, [], \<alpha>\<^sub>1) (p\<^sub>1, [], [])" by simp

    moreover from Suc.prems Nil have "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp

    ultimately show ?thesis by force
  next
    case (Cons Z \<alpha>)
    with Suc.prems obtain p' w' \<alpha>' where r1: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, Z # \<alpha> @ \<beta>\<^sub>1) (p', w', \<alpha>')" and rN: "stepn n (p', w', \<alpha>') (p\<^sub>2, [], [])"
      using stepn_split_first[of p\<^sub>1 w\<^sub>1 "Z # \<alpha> @ \<beta>\<^sub>1" n p\<^sub>2 "[]" "[]"] by auto 
    from r1 have rule: "(\<exists>\<beta>. w' = w\<^sub>1 \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p', \<beta>) \<in> \<delta>\<epsilon> M p\<^sub>1 Z) 
           \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w' \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p',\<beta>) \<in> \<delta> M p\<^sub>1 a Z)" (is "?l \<or> ?r")
      using step\<^sub>1_rule by blast
    show ?thesis proof (rule disjE[OF rule])
      assume ?l
      then obtain \<beta> where w1_def: "w\<^sub>1 = w'" and \<alpha>'_def: "\<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1" and e: "(p',\<beta>) \<in> \<delta>\<epsilon> M p\<^sub>1 Z" by blast
      from rN \<alpha>'_def have rN2: "stepn n (p', w', (\<beta> @ \<alpha>) @ \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
      obtain p'' m\<^sub>1 m\<^sub>2 y y' where w'_def: "w' = y @ y'" and m1_m2_n: "m\<^sub>1 + m\<^sub>2 = n" 
          and rm1: "stepn m\<^sub>1 (p', y, \<beta> @ \<alpha>) (p'', [], [])" and rm2: "stepn m\<^sub>2 (p'', y', \<beta>\<^sub>1) (p\<^sub>2, [], [])"
        using Suc.IH[OF rN2] by blast
      from e have s1: "step\<^sub>1 (p\<^sub>1, y, Z#\<alpha>) (p', y, \<beta>@\<alpha>)"
        using step\<^sub>1_rule by blast

      from w1_def w'_def have "w\<^sub>1 = y @ y'" by simp

      moreover from m1_m2_n have "Suc m\<^sub>1 + m\<^sub>2 = Suc n" by simp

      moreover from s1 rm1 Cons have "stepn (Suc m\<^sub>1) (p\<^sub>1, y, \<alpha>\<^sub>1) (p'', [], [])"
        using stepn_split_first by blast

      ultimately show ?thesis
        using rm2 by metis
    next
      assume ?r
      then obtain a \<beta> where w1_def: "w\<^sub>1 = a # w'" and \<alpha>'_def: "\<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1" and tr: "(p',\<beta>) \<in> \<delta> M p\<^sub>1 a Z" by blast
      from rN \<alpha>'_def have rN2: "stepn n (p', w', (\<beta> @ \<alpha>) @ \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
      obtain p'' m\<^sub>1 m\<^sub>2 y y' where w'_def: "w' = y @ y'" and m1_m2_n: "m\<^sub>1 + m\<^sub>2 = n" 
          and rm1: "stepn m\<^sub>1 (p', y, \<beta> @ \<alpha>) (p'', [], [])" and rm2: "stepn m\<^sub>2 (p'', y', \<beta>\<^sub>1) (p\<^sub>2, [], [])"
        using Suc.IH[OF rN2] by blast
      from tr have s1: "step\<^sub>1 (p\<^sub>1, a#y, Z#\<alpha>) (p', y, \<beta>@\<alpha>)" by simp

      from w1_def w'_def have "w\<^sub>1 = (a # y) @ y'" by simp

      moreover from m1_m2_n have "Suc m\<^sub>1 + m\<^sub>2 = Suc n" by simp

      moreover from s1 rm1 Cons have "stepn (Suc m\<^sub>1) (p\<^sub>1, a#y, \<alpha>\<^sub>1) (p'', [], [])"
        using stepn_split_first by blast

      ultimately show ?thesis 
        using rm2 by metis
    qed
  qed
qed blast

end

end