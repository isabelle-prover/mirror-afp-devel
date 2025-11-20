(* Authors: Tassilo Lemke, Tobias Nipkow *)

section \<open>$Pre^*$\<close>

theory Pre_Star
imports
  Context_Free_Grammar.Context_Free_Grammar
  LTS_Automata
  "HOL-Library.While_Combinator"
begin

(* Internal polishing: One could get rid of \<open>reachable_from\<close> and use \<open>states_lts \<subseteq> Q\<close> instead. *)

text\<open>This theory defines \<open>pre\<^sup>*(L)\<close> (\<open>pre_star\<close> below) and verifies a simple saturation algorithm
\<open>pre_star_auto\<close> that computes \<open>pre\<^sup>*(M)\<close> given an NFA \<open>M\<close> and a finite set of context-free productions.
Most of the work is on the level of finite LTS (via \<open>pre_star_lts\<close>).

A closely related formalization is \<open>AFP/Pushdown_Systems\<close>where \<open>pre\<^sup>*\<close> is computed for pushdown systems instead of CFGs.
\<close>

definition pre_star :: "('n,'t)Prods \<Rightarrow> ('n,'t) syms set \<Rightarrow> ('n,'t) syms set" where
"pre_star P L = {\<alpha>. \<exists>\<beta> \<in> L. P \<turnstile> \<alpha> \<Rightarrow>* \<beta>}"


subsection \<open>Definition on LTS as Fixpoint\<close>

text\<open>
  The algorithm works by repeatedly adding transitions to the LTS, such that at after every step,
  the LTS accepts the original language and its \textbf{direct} predecessors.

  Since no new states are added, the number of transitions that can be added is bounded,
  which allow to both prove termination and the property of a fixpoint:
  At some point, adding another layer of direct predecessors no-longer changes anything,
  i.e.\ the LTS is saturated and \<open>pre\<^sup>*\<close> has been reached.\<close>

definition pre_lts :: "('n,'t) Prods \<Rightarrow> 's set \<Rightarrow> ('s, ('n,'t) sym) lts \<Rightarrow> ('s, ('n,'t) sym) lts"
  where
"pre_lts P Q T =
  { (q, Nt A, q') | q q' A. q \<in> Q \<and> (\<exists>\<beta>. (A, \<beta>) \<in> P \<and> q' \<in> steps_lts T \<beta> q)}"

lemma pre_lts_code[code]: "pre_lts P Q T =
   (\<Union>q \<in> Q. \<Union>(A,\<beta>) \<in> P. \<Union>q' \<in> steps_lts T \<beta> q. {(q, Nt A, q')})"
  unfolding pre_lts_def image_def by(auto)

definition pre_star_lts :: "('n, 't) Prods \<Rightarrow> 's set
    \<Rightarrow> ('s, ('n, 't) sym) lts \<Rightarrow> ('s, ('n, 't) sym) lts option" where
"pre_star_lts P Q = while_option (\<lambda>T. T \<union> pre_lts P Q T \<noteq> T) (\<lambda>T. T \<union> pre_lts P Q T)"

lemma pre_star_lts_rule:
  assumes "\<And>T. H T \<Longrightarrow> T \<union> pre_lts P Q T \<noteq> T \<Longrightarrow> H (T \<union> pre_lts P Q T)"
    and "pre_star_lts P Q T = Some T'" and "H T"
  shows "H T'"
  using assms unfolding pre_star_lts_def by (rule while_option_rule)

lemma pre_star_lts_fp: "pre_star_lts P Q T = Some T' \<Longrightarrow> T' \<union> (pre_lts P Q T') = T'"
  unfolding pre_star_lts_def using while_option_stop by fast

lemma pre_star_lts_mono: "pre_star_lts P Q T = Some T' \<Longrightarrow> T \<subseteq> T'"
  by (rule pre_star_lts_rule) blast+


subsection\<open>Propagation of Reachability\<close>

text\<open>
  No new states are added. Expressing this fact within the \<open>auto\<close> model is to show that the
  set of reachable states from any given start state remains unaltered.
\<close>

lemma pre_lts_reachable:
  "reachable_from T q = reachable_from (T \<union> pre_lts P Q T) q"
  unfolding pre_lts_def by (rule reachable_add_trans) blast

lemma pre_star_lts_reachable:
  assumes "pre_star_lts P Q T = Some T'"
  shows "reachable_from T q = reachable_from T' q"
  by (rule pre_star_lts_rule; use assms pre_lts_reachable in fast)

lemma states_pre_lts: assumes "states_lts T \<subseteq> Q" shows "states_lts (pre_lts P Q T) \<subseteq> Q"
using steps_states_lts[OF assms] unfolding pre_lts_def states_lts_def by auto

lemma states_pre_star_lts:
  assumes "pre_star_lts P Q T = Some T'" and "states_lts T \<subseteq> Q"
  shows "states_lts T' \<subseteq> Q"
apply (rule pre_star_lts_rule[OF _ assms(1)])
 apply (simp add: states_lts_Un states_pre_lts)
by(fact assms(2))


subsection\<open>Correctness\<close>

lemma pre_lts_keeps:
  assumes "q' \<in> steps_lts T \<beta> q"
  shows "q' \<in> steps_lts (T \<union> pre_lts P Q T) \<beta> q"
  using assms steps_lts_mono by (metis insert_absorb insert_subset sup_ge1)

lemma pre_lts_prod:
  assumes "(A, \<beta>) \<in> P" and "q \<in> Q" and "q' \<in> Q" and "q' \<in> steps_lts T \<beta> q"
  shows "q' \<in> steps_lts (T \<union> pre_lts P Q T) [Nt A] q"
  using assms unfolding pre_lts_def Steps_lts_def Step_lts_def step_lts_def by force

lemma pre_lts_pre:
  assumes "P \<turnstile> w\<^sub>\<alpha> \<Rightarrow> w\<^sub>\<beta>" and "reachable_from T q \<subseteq> Q" and "q' \<in> steps_lts T w\<^sub>\<beta> q"
  shows "q' \<in> steps_lts (T \<union> pre_lts P Q T) w\<^sub>\<alpha> q"
proof -
  obtain w\<^sub>p w\<^sub>s A \<beta> where prod: "(A, \<beta>) \<in> P"
      and w\<^sub>\<alpha>_split: "w\<^sub>\<alpha> = w\<^sub>p@[Nt A]@w\<^sub>s"
      and w\<^sub>\<beta>_split: "w\<^sub>\<beta> = w\<^sub>p@\<beta>@w\<^sub>s"
    using assms(1) by (meson derive.cases)

  obtain q1 q2 where step_w\<^sub>p: "q1 \<in> steps_lts T w\<^sub>p q"
      and step_\<beta>: "q2 \<in> steps_lts T \<beta> q1"
      and step_w\<^sub>s: "q' \<in> steps_lts T w\<^sub>s q2"
    using Steps_lts_split3 assms(3)[unfolded w\<^sub>\<beta>_split] by fast
  then have q1_reach: "q1 \<in> reachable_from T q" and "q2 \<in> reachable_from T q1"
    using assms(2) unfolding reachable_from_def by blast+
  then have q2_reach: "q2 \<in> reachable_from T q"
    using assms(2) reachable_from_trans by fast

  have "q2 \<in> steps_lts (T \<union> pre_lts P Q T) [Nt A] q1"
    by (rule pre_lts_prod; use q1_reach q2_reach assms(2) prod step_\<beta> in blast)
  moreover have "q1 \<in> steps_lts (T \<union> pre_lts P Q T) w\<^sub>p q"
      and "q' \<in> steps_lts (T \<union> pre_lts P Q T) w\<^sub>s q2"
    using step_w\<^sub>p step_w\<^sub>s pre_lts_keeps by fast+
  ultimately have "q' \<in> steps_lts (T \<union> pre_lts P Q T) w\<^sub>\<alpha> q"
    unfolding w\<^sub>\<alpha>_split using Steps_lts_join3 by fast
  then show ?thesis .
qed

lemma pre_lts_fp:
  assumes "P \<turnstile> w\<^sub>\<alpha> \<Rightarrow>* w\<^sub>\<beta>" and "reachable_from T q \<subseteq> Q" and "q' \<in> steps_lts T w\<^sub>\<beta> q"
    and fp: "T \<union> pre_lts P Q T = T"
  shows "q' \<in> steps_lts T w\<^sub>\<alpha> q"
proof (insert assms, induction rule: converse_rtranclp_induct[where r="derive P"])
  case base thus ?case by simp
next
  case (step y z)
  then show ?case
    using pre_lts_pre by fastforce
qed

lemma pre_lts_while:
  assumes "P \<turnstile> w\<^sub>\<alpha> \<Rightarrow>* w\<^sub>\<beta>" and "reachable_from T q \<subseteq> Q" and "q' \<in> steps_lts T w\<^sub>\<beta> q"
    and "pre_star_lts P Q T = Some T'"
  shows "q' \<in> steps_lts T' w\<^sub>\<alpha> q"
proof -
  have "T' \<union> pre_lts P Q T' = T'"
    using assms(4) by (rule pre_star_lts_fp)
  moreover have "reachable_from T' q \<subseteq> Q"
    using assms(2,4) pre_star_lts_reachable by fast
  moreover have "q' \<in> steps_lts T' w\<^sub>\<beta> q"
    by (rule steps_lts_mono'[where T\<^sub>1=T]; use assms(3,4) pre_star_lts_mono in blast)
  ultimately show ?thesis
    using assms(1) pre_lts_fp by fast
qed

lemma pre_lts_sub_aux:
  assumes "q' \<in> steps_lts (T \<union> pre_lts P Q T) w q"
  shows "\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps_lts T w' q"
proof (insert assms, induction w arbitrary: q)
  case Nil
  then show ?case
    by (simp add: Steps_lts_def)
next
  case (Cons c w)
  then obtain q1 where step_w: "q' \<in> steps_lts (T \<union> pre_lts P Q T) w q1"
      and step_c: "q1 \<in> steps_lts (T \<union> pre_lts P Q T) [c] q"
    using Steps_lts_split by (metis (no_types, lifting) append_Cons append_Nil)

  obtain w' where "q' \<in> steps_lts T w' q1" and "P \<turnstile> w \<Rightarrow>* w'"
    using Cons step_w by blast

  have "\<exists>c'. q1 \<in> steps_lts T c' q \<and> P \<turnstile> [c] \<Rightarrow>* c'"
  proof (cases "q1 \<in> steps_lts T [c] q")
    case True
    then show ?thesis
      by blast
  next
    case False
    then have "q1 \<in> steps_lts (pre_lts P Q T) [c] q"
      using step_c unfolding Steps_lts_def Step_lts_def step_lts_def by force
    then have "(q, c, q1) \<in> pre_lts P Q T"
      by (auto simp: Steps_lts_def Step_lts_def step_lts_def)
    then obtain A \<beta> where "(A, \<beta>) \<in> P" and "c = Nt A" and "q1 \<in> steps_lts T \<beta> q"
      unfolding pre_lts_def by blast
    moreover have "P \<turnstile> [c] \<Rightarrow>* \<beta>"
      using calculation by (simp add: derive_singleton r_into_rtranclp)
    ultimately show ?thesis
      by blast
  qed
  then obtain c' where "q1 \<in> steps_lts T c' q" and "P \<turnstile> [c] \<Rightarrow>* c'"
    by blast

  have "q' \<in> steps_lts T (c'@w') q"
    using \<open>q1 \<in> steps_lts T c' q\<close> \<open>q' \<in> steps_lts T w' q1\<close> Steps_lts_join by fast
  moreover have "P \<turnstile> (c#w) \<Rightarrow>* (c'@w')"
    using \<open>P \<turnstile> [c] \<Rightarrow>* c'\<close> \<open>P \<turnstile> w \<Rightarrow>* w'\<close>
    by (metis (no_types, opaque_lifting) Cons_eq_appendI derives_append_decomp self_append_conv2)
  ultimately show ?case
    by blast
qed

lemma pre_lts_sub:
  assumes "\<forall>w. (q' \<in> steps_lts T' w q) \<longrightarrow> (\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps_lts T w' q)"
    and "q' \<in> steps_lts (T' \<union> pre_lts P Q T') w q"
  shows "\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps_lts T w' q"
proof -
  obtain w' where "P \<turnstile> w \<Rightarrow>* w'" and "q' \<in> steps_lts T' w' q"
    using pre_lts_sub_aux assms by fast
  then obtain w'' where "P \<turnstile> w' \<Rightarrow>* w''" and "q' \<in> steps_lts T w'' q"
    using assms(1) by blast
  moreover have "P \<turnstile> w \<Rightarrow>* w''"
    using \<open>P \<turnstile> w \<Rightarrow>* w'\<close> calculation(1) by simp
  ultimately show ?thesis
    by blast
qed

lemma pre_star_lts_sub:
  assumes "pre_star_lts P Q T = Some T'"
  shows "(q' \<in> steps_lts T' w q) \<Longrightarrow> (\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps_lts T w' q)"
proof -
  let ?I = "\<lambda>T'. \<forall>w. (q' \<in> steps_lts T' w q) \<longrightarrow> (\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps_lts T w' q)"
  have "\<And>T'. ?I T' \<Longrightarrow> ?I (T' \<union> pre_lts P Q T')"
    by (simp add: pre_lts_sub[where T=T])
  then have "?I T'"
    by (rule pre_star_lts_rule[where T=T and T'=T']; use assms in blast)
  then show "(q' \<in> steps_lts T' w q) \<Longrightarrow> (\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps_lts T w' q)"
    by simp
qed

lemma pre_star_lts_correct:                 
  assumes "reachable_from T q\<^sub>0 \<subseteq> Q" and "pre_star_lts P Q T = Some T'"
  shows "Lang_lts T' q\<^sub>0 F = pre_star P (Lang_lts T q\<^sub>0 F)"
proof (standard; standard)
  fix w
  assume "w \<in> Lang_lts T' q\<^sub>0 F"
  then obtain q\<^sub>f where "q\<^sub>f \<in> steps_lts T' w q\<^sub>0" and "q\<^sub>f \<in> F"
    by blast
  then obtain w' where "P \<turnstile> w \<Rightarrow>* w'" and "q\<^sub>f \<in> steps_lts T w' q\<^sub>0"
    using pre_star_lts_sub assms by fast
  moreover have "w' \<in> Lang_lts T q\<^sub>0 F"
    using calculation \<open>q\<^sub>f \<in> F\<close> by blast
  ultimately show "w \<in> pre_star P (Lang_lts T q\<^sub>0 F)"
    unfolding pre_star_def by blast
next
  fix w
  assume "w \<in> pre_star P (Lang_lts T q\<^sub>0 F)"
  then obtain w' where "P \<turnstile> w \<Rightarrow>* w'" and "w' \<in> Lang_lts T q\<^sub>0 F"
    unfolding pre_star_def by blast
  then obtain q\<^sub>f where "q\<^sub>f \<in> steps_lts T w' q\<^sub>0" and "q\<^sub>f \<in> F"
    by blast
  then have "q\<^sub>f \<in> steps_lts T' w' q\<^sub>0"
    using steps_lts_mono pre_star_lts_mono assms by (metis in_mono)
  moreover have "reachable_from T' q\<^sub>0 \<subseteq> Q"
    using assms pre_star_lts_reachable by fast
  moreover have "T' \<union> pre_lts P Q T' = T'"
    by (rule pre_star_lts_fp; use assms(2) in simp)
  moreover note \<open>P \<turnstile> w \<Rightarrow>* w'\<close>
  ultimately have "q\<^sub>f \<in> steps_lts T' w q\<^sub>0"
    by (elim pre_lts_fp) simp+
  with \<open>q\<^sub>f \<in> F\<close> show "w \<in> Lang_lts T' q\<^sub>0 F"
    by blast
qed


subsection\<open>Termination\<close>

lemma while_option_finite_subset_Some':
  fixes C :: "'a set"
  assumes "mono f" and "\<And>X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C" and "finite C" and "S \<subseteq> C" and "\<And>X. X \<subseteq> f X"
  shows "\<exists>P. while_option (\<lambda>A. f A \<noteq> A) f S = Some P"
proof (rule measure_while_option_Some[where
    f= "%A::'a set. card C - card A" and P= "%A. A \<subseteq> C \<and> A \<subseteq> f A" and s=S])
  fix A assume A: "A \<subseteq> C \<and> A \<subseteq> f A" "f A \<noteq> A"
  show "(f A \<subseteq> C \<and> f A \<subseteq> f (f A)) \<and> card C - card (f A) < card C - card A"
    (is "?L \<and> ?R")
  proof
    show ?L by (metis A(1) assms(2) monoD[OF \<open>mono f\<close>])
    show ?R by (metis A assms(2,3) card_seteq diff_less_mono2 equalityI linorder_le_less_linear rev_finite_subset)
  qed
qed (simp add: assms)

lemma pre_star_lts_terminates:
  fixes P :: "('n, 't) Prods" and Q :: "'s set" and T\<^sub>0 :: "('s, ('n, 't) sym) lts"
  assumes "finite P" and "finite Q" and "finite T\<^sub>0" and "states_lts T\<^sub>0 \<subseteq> Q"
  shows "\<exists>T. pre_star_lts P Q T\<^sub>0 = Some T"
proof -
  define b :: "('s, ('n, 't) sym) lts \<Rightarrow> bool" where
    [simp]: "b = (\<lambda>T. T \<union> pre_lts P Q T \<noteq> T)"
  define f :: "('s, ('n, 't) sym) lts \<Rightarrow> ('s, ('n, 't) sym) lts" where
    [simp]: "f = (\<lambda>T. T \<union> pre_lts P Q T)"
  then have "mono f"
    unfolding mono_def pre_lts_def
    by (smt (verit, ccfv_threshold) UnCI UnE in_mono mem_Collect_eq Steps_lts_mono2 subsetI)

  define U :: "('s, ('n, 't) sym) lts" where
    "U = { (q, Nt A, q') | q q' A. q \<in> Q \<and> (\<exists>\<beta>. (A, \<beta>) \<in> P \<and> q' \<in> Q)} \<union> T\<^sub>0"
  have "\<And>p a q. (p,a,q) \<in> T\<^sub>0 \<Longrightarrow> p \<in> Q \<and> q \<in> Q"
    using assms(4) unfolding states_lts_def by auto
  then have "pre_lts P Q T \<subseteq> U" if asm: "T \<subseteq> U" for T
    using asm steps_states_lts[of T Q] unfolding U_def pre_lts_def states_lts_def
    by fastforce
  then have U_bounds: "\<And>X. X \<subseteq> U \<Longrightarrow> f X \<subseteq> U"
    by simp

  have "finite U"
  proof -
    define U' :: "('s, ('n, 't) sym) lts" where
      [simp]: "U' = Q \<times> ((\<lambda>(A,_). Nt A) ` P) \<times> Q"
    have "finite ((\<lambda>(A,_). Nt A) ` P)"
      using assms(1) by simp
    then have "finite U'"
      using assms(2) U'_def by blast

    define T' :: "('s, ('n, 't) sym) lts" where
      [simp]: "T' = { (q,Nt A,q') | q q' A. q \<in> Q \<and> (\<exists>\<beta>. (A, \<beta>) \<in> P \<and> q' \<in> Q)}"
    then have "T' \<subseteq> U'"
      unfolding T'_def U'_def using assms(1) by fast
    moreover note \<open>finite U'\<close>
    ultimately have "finite T'"
      using rev_finite_subset[of U' T'] by blast
    then show "finite U"
      by (simp add: U_def assms)
  qed

  note criteria = \<open>finite U\<close> U_def f_def U_bounds \<open>mono f\<close>
  have "\<exists>P. while_option (\<lambda>A. f A \<noteq> A) f T\<^sub>0 = Some P"
    by (rule while_option_finite_subset_Some'[where C=U]; use criteria in blast)
  then show ?thesis
    by (simp add: pre_star_lts_def)
qed

subsection \<open>The Automaton Level\<close>

definition pre_star_auto :: "('n, 't) Prods \<Rightarrow> ('s, ('n, 't) sym) auto \<Rightarrow> ('s, ('n, 't) sym) auto" where
  "pre_star_auto P M = (
    let Q = {auto.start M} \<union> states_lts (auto.lts M) in
    case pre_star_lts P Q (auto.lts M) of
      Some T' \<Rightarrow> M \<lparr> auto.lts := T' \<rparr>
  )"

lemma pre_star_auto_correct:
  assumes "finite P" and "finite (auto.lts M)"
  shows "Lang_auto (pre_star_auto P M) = pre_star P (Lang_auto M)"
proof -
  define T where "T \<equiv> auto.lts M"
  define Q where "Q \<equiv> {auto.start M} \<union> states_lts T"
  then have "finite Q"
    unfolding T_def states_lts_def using assms(2) by auto
  have MQ: "states_lts (auto.lts M) \<subseteq> Q" unfolding Q_def T_def by (force)
  have "reachable_from T (auto.start M) \<subseteq> Q"
    using reachable_from_computable unfolding Q_def states_lts_def by fastforce
  moreover obtain T' where T'_def: "pre_star_lts P Q T = Some T'"
    using pre_star_lts_terminates[OF assms(1) \<open>finite Q\<close> assms(2) MQ] T_def by blast
  ultimately have "Lang_lts T' (auto.start M) (auto.finals M)
    = pre_star P (Lang_lts T (auto.start M) (auto.finals M))"
    by (rule pre_star_lts_correct)
  then have "Lang_auto (M \<lparr> auto.lts := T' \<rparr>) = pre_star P (Lang_auto M)"
    by (simp add: T_def)
  then show ?thesis
    unfolding pre_star_auto_def using Q_def T'_def T_def
    by(force)
qed

lemma pre_star_lts_refl:
  assumes "pre_star_lts P Q T = Some T'" and "(A, []) \<in> P" and "q \<in> Q"
  shows "(q, Nt A, q) \<in> T'"
proof -
  have "q \<in> steps_lts T' [] q"
    unfolding Steps_lts_def using assms by force
  then have "(q, Nt A, q) \<in> pre_lts P Q T'"
    unfolding pre_lts_def using assms by blast
  moreover have "T' = T' \<union> pre_lts P Q T'"
    using pre_star_lts_fp assms(1) by blast
  ultimately show ?thesis
    by blast
qed

lemma pre_star_lts_singleton:
  assumes "pre_star_lts P Q T = Some T'" and "(A, [B]) \<in> P"
    and "(q, B, q') \<in> T'" and "q \<in> Q" and "q' \<in> Q"
  shows "(q, Nt A, q') \<in> T'"
proof -
  have "q' \<in> steps_lts T' [B] q"
    unfolding steps_lts_defs using assms by force
  then have "(q, Nt A, q') \<in> pre_lts P Q T'"
    unfolding pre_lts_def using assms by blast
  moreover have "T' = T' \<union> (pre_lts P Q T')"
    using pre_star_lts_fp assms(1) by blast
  ultimately show ?thesis
    by blast
qed

lemma pre_star_lts_impl:
  assumes "pre_star_lts P Q T = Some T'" and "(A, [B, C]) \<in> P"
    and "(q, B, q') \<in> T'" and "(q', C, q'') \<in> T'"
    and "q \<in> Q" and "q' \<in> Q" and "q'' \<in> Q"
  shows "(q, Nt A, q'') \<in> T'"
proof -
  have "q'' \<in> steps_lts T' [B, C] q"
    unfolding steps_lts_defs using assms by force
  then have "(q, Nt A, q'') \<in> pre_lts P Q T'"
    unfolding pre_lts_def using assms by blast
  moreover have "T' = T' \<union> pre_lts P Q T'"
    using pre_star_lts_fp assms(1) by blast
  ultimately show ?thesis
    by blast
qed

end
