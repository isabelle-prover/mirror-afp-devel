(* Authors: Tassilo Lemke, Tobias Nipkow *)

section\<open>Labeled Transition System\<close>

text \<open>This theory could be unified with \<open>AFP/Labeled_Transition_Systems\<close>\<close>

theory Labeled_Transition_System
  imports Main
begin

text \<open>Labeled Transition Systems are sets of triples of type @{typ "'s \<times> 'a \<times> 's"}.\<close>

type_synonym ('s, 'l) lts = "('s \<times> 'l \<times> 's) set"

text\<open>The following lemma ensure that Isabelle can evaluate set comprehensions over triples.\<close>
lemma Collect_triple_code[code_unfold]:
  "{(x,y,z) \<in> A. P x y z} = {p \<in> A. P (fst p) (fst (snd p)) (snd (snd p))}"
  by fastforce

subsection\<open>Step Relations\<close>

text\<open>
  A step from a state \<open>q\<close> over a single symbol \<open>c\<close> is the set of all \<open>q'\<close>, such that \<open>(q, c, q') \<in> T\<close>:
\<close>

definition step_lts :: "('s, 'l) lts \<Rightarrow> 'l \<Rightarrow> 's \<Rightarrow> 's set" where
  "step_lts T c s = (\<lambda>(q, c, q'). q') ` {(q, c', q') \<in> T. c = c' \<and> q = s}"

text\<open>
  A step of a single symbol \<open>c\<close> from a set of states \<open>S\<close> is the union of @{const step_lts} over \<open>S\<close>:
\<close>

definition Step_lts :: "('s, 'l) lts \<Rightarrow> 'l \<Rightarrow> 's set \<Rightarrow> 's set" where
  "Step_lts T c S = \<Union>(step_lts T c ` S)"

text\<open>
  Repeated steps of a word \<open>w\<close> consisting of multiple letters is achieved using a standard @{term fold}:
\<close>

definition Steps_lts :: "('s, 'l) lts \<Rightarrow> 'l list \<Rightarrow> 's set \<Rightarrow> 's set" where
  "Steps_lts T w s = fold (Step_lts T) w s"

text\<open>Often, merely a single starting-state is of relevance:\<close>

abbreviation steps_lts :: "('s, 'l) lts \<Rightarrow> 'l list \<Rightarrow> 's \<Rightarrow> 's set" where
  "steps_lts T w s \<equiv> Steps_lts T w {s}"

lemmas steps_lts_defs = step_lts_def Step_lts_def Steps_lts_def

text\<open>
  We now prove some key properties of this step relation:
\<close>

lemma Step_union: "Step_lts T w (S\<^sub>1 \<union> S\<^sub>2) = Step_lts T w S\<^sub>1 \<union> Step_lts T w S\<^sub>2"
  unfolding Step_lts_def by blast

lemma Steps_lts_mono: "s\<^sub>1 \<subseteq> s\<^sub>2 \<Longrightarrow> Steps_lts T w s\<^sub>1 \<subseteq> Steps_lts T w s\<^sub>2"
proof (induction w arbitrary: s\<^sub>1 s\<^sub>2)
  case Nil thus ?case by (simp add: Steps_lts_def)
next
  case (Cons w ws)

  define s\<^sub>1' where [simp]: "s\<^sub>1' \<equiv> Step_lts T w s\<^sub>1"
  define s\<^sub>2' where [simp]: "s\<^sub>2' \<equiv> Step_lts T w s\<^sub>2"
  
  have "s\<^sub>1' \<subseteq> s\<^sub>2'"
    by (simp add: Step_lts_def, use \<open>s\<^sub>1 \<subseteq> s\<^sub>2\<close> in blast)
  then have "Steps_lts T ws s\<^sub>1' \<subseteq> Steps_lts T ws s\<^sub>2'"
    by (elim Cons.IH)
  moreover have "Steps_lts T (w#ws) s\<^sub>1 = Steps_lts T ws s\<^sub>1'"
    by (simp add: Steps_lts_def)
  moreover have "Steps_lts T (w#ws) s\<^sub>2 = Steps_lts T ws s\<^sub>2'"
    by (simp add: Steps_lts_def)
  ultimately show ?case
    by simp
qed

lemma Steps_lts_mono2:
  assumes "T\<^sub>1 \<subseteq> T\<^sub>2" and "q\<^sub>1 \<subseteq> q\<^sub>2"
  shows "Steps_lts T\<^sub>1 w q\<^sub>1 \<subseteq> Steps_lts T\<^sub>2 w q\<^sub>2"
using assms(2) proof (induction w arbitrary: q\<^sub>1 q\<^sub>2)
  case Nil thus ?case by (simp add: Steps_lts_def)
next
  case (Cons w ws)
  have "Step_lts T\<^sub>1 w q\<^sub>1 \<subseteq> Step_lts T\<^sub>2 w q\<^sub>2"
    unfolding steps_lts_defs using assms(1) Cons(2) by blast
  then have "Steps_lts T\<^sub>1 ws (Step_lts T\<^sub>1 w q\<^sub>1) \<subseteq> Steps_lts T\<^sub>1 ws (Step_lts T\<^sub>2 w q\<^sub>2)"
    by (rule Steps_lts_mono)
  then have "Steps_lts T\<^sub>1 ws (Step_lts T\<^sub>1 w q\<^sub>1) \<subseteq> Steps_lts T\<^sub>2 ws (Step_lts T\<^sub>2 w q\<^sub>2)"
    using Cons(1) by blast
  then show ?case
    by (simp add: Steps_lts_def)
qed

lemma steps_lts_mono: "T\<^sub>1 \<subseteq> T\<^sub>2 \<Longrightarrow> steps_lts T\<^sub>1 w q \<subseteq> steps_lts T\<^sub>2 w q"
  using Steps_lts_mono2[of T\<^sub>1 T\<^sub>2 "{q}" "{q}" w] by simp

lemma steps_lts_mono': "T\<^sub>1 \<subseteq> T\<^sub>2 \<Longrightarrow> q' \<in> steps_lts T\<^sub>1 w q \<Longrightarrow> q' \<in> steps_lts T\<^sub>2 w q"
proof -
  assume "T\<^sub>1 \<subseteq> T\<^sub>2"
  then have "steps_lts T\<^sub>1 w q \<subseteq> steps_lts T\<^sub>2 w q"
    by (rule steps_lts_mono)
  then show "q' \<in> steps_lts T\<^sub>1 w q \<Longrightarrow> q' \<in> steps_lts T\<^sub>2 w q"
    by blast
qed

lemma steps_lts_union: "q' \<in> steps_lts T w q \<Longrightarrow> q' \<in> steps_lts (T \<union> T') w q"
proof -
  have "T \<subseteq> (T \<union> T')"
    by simp
  then show "q' \<in> steps_lts T w q \<Longrightarrow> q' \<in> steps_lts (T \<union> T') w q"
    by (rule steps_lts_mono')
qed

lemma Steps_lts_path:
  assumes "q\<^sub>f \<in> Steps_lts T w s"
  shows "\<exists>q\<^sub>0 \<in> s. q\<^sub>f \<in> steps_lts T w q\<^sub>0"
proof (insert assms; induction w arbitrary: s)
  case Nil thus ?case by (simp add: Steps_lts_def)
next
  case (Cons w ws)
  then have "q\<^sub>f \<in> Steps_lts T ws (Step_lts T w s)"
    by (simp add: Steps_lts_def)
  moreover obtain q\<^sub>0 where "q\<^sub>0 \<in> (Step_lts T w s)" and "q\<^sub>f \<in> steps_lts T ws q\<^sub>0"
    using Cons.IH calculation by blast
  ultimately obtain q' where "q\<^sub>0 \<in> step_lts T w q'" and "q' \<in> s"
    unfolding steps_lts_defs by blast

  note \<open>q\<^sub>0 \<in> step_lts T w q'\<close> and \<open>q\<^sub>f \<in> steps_lts T ws q\<^sub>0\<close>
  then have "q\<^sub>f \<in> Steps_lts T ws (step_lts T w q')"
    using Steps_lts_mono[of "{q\<^sub>0}"] by blast
  moreover have "Steps_lts T ws (step_lts T w q') = steps_lts T (w#ws) q'"
    by (simp add: steps_lts_defs)
  ultimately show ?case
    using \<open>q' \<in> s\<close> by blast
qed

lemma Steps_lts_split:
  assumes "q\<^sub>f \<in> Steps_lts T (w\<^sub>1@w\<^sub>2) Q\<^sub>0"
  shows "\<exists>q'. q' \<in> Steps_lts T w\<^sub>1 Q\<^sub>0 \<and> q\<^sub>f \<in> steps_lts T w\<^sub>2 q'"
proof -
  define Q\<^sub>f where [simp]: "Q\<^sub>f = Steps_lts T (w\<^sub>1@w\<^sub>2) Q\<^sub>0"
  define Q' where [simp]: "Q' = Steps_lts T w\<^sub>1 Q\<^sub>0"
  have "Q\<^sub>f = Steps_lts T w\<^sub>2 Q'"
    by (simp add: Steps_lts_def)
  then obtain q' where "q' \<in> Q'" and "q\<^sub>f \<in> steps_lts T w\<^sub>2 q'"
    using assms Steps_lts_path by force
  moreover have "q' \<in> Steps_lts T w\<^sub>1 Q\<^sub>0"
    using calculation by simp
  ultimately show ?thesis
    by blast
qed

lemma Steps_lts_join:
  assumes "q' \<in> Steps_lts T w\<^sub>1 Q\<^sub>0" and "q\<^sub>f \<in> steps_lts T w\<^sub>2 q'"
  shows "q\<^sub>f \<in> Steps_lts T (w\<^sub>1@w\<^sub>2) Q\<^sub>0"
proof -
  define Q' where [simp]: "Q' = Steps_lts T w\<^sub>1 Q\<^sub>0"
  define Q\<^sub>f where [simp]: "Q\<^sub>f = Steps_lts T w\<^sub>2 Q'"

  have "{q'} \<subseteq> Q'"
    using assms(1) by simp
  then have "Steps_lts T w\<^sub>2 {q'} \<subseteq> Steps_lts T w\<^sub>2 Q'"
    using Steps_lts_mono by blast
  then have "q\<^sub>f \<in> Steps_lts T w\<^sub>2 Q'"
    using assms(2) by fastforce
  moreover have "Q\<^sub>f = Steps_lts T (w\<^sub>1@w\<^sub>2) Q\<^sub>0"
    by (simp add: Steps_lts_def)
  ultimately show ?thesis
    by simp
qed

lemma Steps_lts_split3:
  assumes "q\<^sub>f \<in> Steps_lts T (w\<^sub>1@w\<^sub>2@w\<^sub>3) Q\<^sub>0"
  shows "\<exists>q' q''. q' \<in> Steps_lts T w\<^sub>1 Q\<^sub>0 \<and> q'' \<in> steps_lts T w\<^sub>2 q' \<and> q\<^sub>f \<in> steps_lts T w\<^sub>3 q''"
proof -
  obtain q' where "q' \<in> Steps_lts T (w\<^sub>1@w\<^sub>2) Q\<^sub>0 \<and> q\<^sub>f \<in> steps_lts T w\<^sub>3 q'"
    using assms Steps_lts_split[where w\<^sub>1 = "w\<^sub>1@w\<^sub>2"] by fastforce
  moreover then obtain q'' where "q'' \<in> Steps_lts T w\<^sub>1 Q\<^sub>0 \<and> q' \<in> steps_lts T w\<^sub>2 q''"
    using Steps_lts_split by fast
  ultimately show ?thesis
    by blast
qed

lemma Steps_lts_join3:
  assumes "q' \<in> steps_lts T w\<^sub>1 q\<^sub>0" and "q'' \<in> steps_lts T w\<^sub>2 q'" and "q\<^sub>f \<in> steps_lts T w\<^sub>3 q''"
  shows "q\<^sub>f \<in> steps_lts T (w\<^sub>1@w\<^sub>2@w\<^sub>3) q\<^sub>0"
proof -
  have "q\<^sub>f \<in> steps_lts T (w\<^sub>2@w\<^sub>3) q'"
    using assms(2) assms(3) Steps_lts_join by fast
  moreover then have "q\<^sub>f \<in> steps_lts T (w\<^sub>1@w\<^sub>2@w\<^sub>3) q\<^sub>0"
    using assms(1) Steps_lts_join by fast
  ultimately show ?thesis
    by blast
qed

lemma Steps_lts_noState: "Steps_lts T w {} = {}"
proof (induction w)
  case Nil
  then show ?case
    by (simp add: Steps_lts_def)
next
  case (Cons w ws)
  moreover have "Steps_lts T [w] {} = {}"
    by (simp add: steps_lts_defs)
  ultimately show ?case
    by (simp add: Steps_lts_def)
qed


subsection\<open>Reachable States\<close>

definition reachable_from :: "('s, 'l) lts \<Rightarrow> 's \<Rightarrow> 's set" where
  "reachable_from T q \<equiv> {q'. \<exists>w. q' \<in> steps_lts T w q}"

lemma reachable_from_computable: "reachable_from T q \<subseteq> {q} \<union> (snd ` snd ` T)"
proof
  fix q'
  assume "q' \<in> reachable_from T q"
  then obtain w where w_def: "q' \<in> steps_lts T w q"
    unfolding reachable_from_def by blast
  then consider "w = []" | "\<exists>ws c. w = ws@[c]"
    by (meson rev_exhaust)
  then show "q' \<in> {q} \<union> (snd ` snd ` T)"
  proof (cases)
    case 1
    then show ?thesis
      using w_def Steps_lts_def by force
  next
    case 2
    then obtain ws c where "w = ws@[c]"
      by blast
    then obtain q1 where "q1 \<in> steps_lts T ws q" and "q' \<in> steps_lts T [c] q1"
      using Steps_lts_split w_def by fast
    then have "(q1, c, q') \<in> T"
      by (auto simp: steps_lts_defs)
    then show ?thesis
      by force
  qed
qed

lemma reachable_from_trans[trans]:
  assumes "q1 \<in> reachable_from T q0" and "q2 \<in> reachable_from T q1"
  shows "q2 \<in> reachable_from T q0"
  using assms Steps_lts_join unfolding reachable_from_def by fast

lemma reachable_add_trans:
  assumes "\<forall>(q1, _, q2) \<in> T'. \<exists>w. q2 \<in> steps_lts T w q1"
  shows "reachable_from T q = reachable_from (T \<union> T') q"
proof (standard; standard)
  fix q'
  assume "q' \<in> reachable_from T q"
  then show "q' \<in> reachable_from (T \<union> T') q"
    unfolding reachable_from_def using steps_lts_union by fast
next
  fix q'
  assume "q' \<in> reachable_from (T \<union> T') q"
  then obtain w where "q' \<in> steps_lts (T \<union> T') w q"
    unfolding reachable_from_def by blast
  then have "\<exists>w'. q' \<in> steps_lts T w' q"
  proof (induction w arbitrary: q)
    case Nil
    then have "q = q'" and "q \<in> steps_lts T [] q"
      unfolding Steps_lts_def by simp+
    then show ?case
      by blast
  next
    case (Cons c w)
    then obtain q1 where "q' \<in> steps_lts (T \<union> T') w q1" and "q1 \<in> steps_lts (T \<union> T') [c] q"
      using Steps_lts_split[where w\<^sub>1="[c]" and w\<^sub>2=w] by force
    then obtain w' where w'_def: "q' \<in> steps_lts T w' q1"
      using Cons by blast

    have "q1 \<in> step_lts (T \<union> T') c q"
      using \<open>q1 \<in> steps_lts (T \<union> T') [c] q\<close> by (simp add: steps_lts_defs)
    then consider "q1 \<in> step_lts T c q" | "q1 \<in> step_lts T' c q"
      unfolding step_lts_def by blast
    then show ?case
    proof (cases)
      case 1
      then have "q1 \<in> steps_lts T [c] q"
        by (simp add: steps_lts_defs)
      then have "q' \<in> steps_lts T (c#w') q"
        using w'_def Steps_lts_join by force
      then show ?thesis
        by blast
    next
      case 2
      then have "(q, c, q1) \<in> T'"
        by (auto simp: step_lts_def)
      then obtain w'' where "q1 \<in> steps_lts T w'' q"
        using assms by blast
      then have "q' \<in> steps_lts T (w''@w') q"
        using w'_def Steps_lts_join by fast
      then show ?thesis
        by blast
    qed
  qed
  then show "q' \<in> reachable_from T q"
    by (simp add: reachable_from_def)
qed


definition states_lts :: "('s,'a)lts \<Rightarrow> 's set" where
"states_lts T = (\<Union>(p,a,q)\<in>T. {p,q})"

lemma Step_states_lts: "states_lts T \<subseteq> Q \<Longrightarrow> Q0 \<subseteq> Q \<Longrightarrow> Step_lts T a Q0 \<subseteq> Q"
  unfolding Step_lts_def step_lts_def states_lts_def by auto

lemma Steps_states_lts: assumes "states_lts T \<subseteq> Q" shows "Q0 \<subseteq> Q \<Longrightarrow> Steps_lts T u Q0 \<subseteq> Q"
  unfolding Steps_lts_def
  apply(induction u arbitrary: Q0)
   apply simp
  using assms by (simp add: Step_states_lts)

corollary steps_states_lts: "\<lbrakk> states_lts T \<subseteq> Q; q \<in> Q \<rbrakk> \<Longrightarrow> steps_lts T u q \<subseteq> Q"
  using Steps_states_lts[of T Q "{q}"] by blast

lemma states_lts_Un: "states_lts (T \<union> T') = states_lts T \<union> states_lts T'"
  unfolding states_lts_def by auto


subsection\<open>Language\<close>

abbreviation accepts_lts :: "('s, 'l) lts \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> 'l list \<Rightarrow> bool" where
  "accepts_lts T s F w \<equiv> (steps_lts T w s \<inter> F \<noteq> {})"

abbreviation Lang_lts :: "('s, 'l) lts \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> ('l list) set" where
  "Lang_lts T S F \<equiv> { w. accepts_lts T S F w }"

(* unused
lemma Lang_lts_trans:
  assumes "s' \<in> steps_lts T w\<^sub>1 s" and "w\<^sub>2 \<in> Lang_lts T s' F"
  shows "(w\<^sub>1@w\<^sub>2) \<in> Lang_lts T s F"
proof -
  obtain q\<^sub>f where "q\<^sub>f \<in> steps_lts T w\<^sub>2 s'" and "q\<^sub>f \<in> F"
    using assms(2) by blast
  moreover have "q\<^sub>f \<in> steps_lts T (w\<^sub>1@w\<^sub>2) s"
    using assms(1) \<open>q\<^sub>f \<in> steps_lts T w\<^sub>2 s'\<close> by (rule Steps_lts_join)
  ultimately show ?thesis
    using \<open>q\<^sub>f \<in> F\<close> by blast
qed

lemma Lang_lts_split:
  assumes "(w\<^sub>1@w\<^sub>2) \<in> Lang_lts T q F"
  obtains q' where "q' \<in> steps_lts T w\<^sub>1 q" and "w\<^sub>2 \<in> Lang_lts T q' F"
proof -
  obtain q\<^sub>f where "q\<^sub>f \<in> steps_lts T (w\<^sub>1@w\<^sub>2) q" and "q\<^sub>f \<in> F"
    using assms by blast
  then obtain q' where "q' \<in> steps_lts T w\<^sub>1 q" and "q\<^sub>f \<in> steps_lts T w\<^sub>2 q'"
    using Steps_lts_split by fast
  moreover then have "w\<^sub>2 \<in> Lang_lts T q' F"
    using \<open>q\<^sub>f \<in> F\<close> by blast
  ultimately show ?thesis
    using that by blast
qed

lemma Lang_steps_lts_mono: "T\<^sub>1 \<subseteq> T\<^sub>2 \<Longrightarrow> Lang_lts T\<^sub>1 s f \<subseteq> Lang_lts T\<^sub>2 s f"
  using steps_lts_mono[of T\<^sub>1 T\<^sub>2] by fast
*)

end
