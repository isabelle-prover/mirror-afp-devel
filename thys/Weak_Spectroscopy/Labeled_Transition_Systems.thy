(* License: LGPL *)

section \<open>Labeled Transition Systems\<close>

theory Labeled_Transition_Systems
  imports Main
begin

subsection \<open>Base LTS\<close>

text \<open>
  The locale \<open>LTS\<close> represents a labeled transition system consisting of a set of states $\mathcal{P}$, a set of actions $\Sigma$, and a transition relation $\mapsto \subseteq \mathcal{P}\times\Sigma\times\mathcal{P}$.
  We formalize the sets of states and actions by the type variables \<open>'s\<close> and \<open>'a\<close>. An LTS is then determined by the transition relation \<open>step\<close>.
\<close>

locale lts =
  fixes step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto> _ _\<close> [70,70,70] 80)
begin

text \<open>One may lift \<^term>\<open>step\<close> to sets of states, written as \<open>P \<mapsto>S \<alpha> Q\<close>.\<close>
abbreviation step_setp (\<open>_ \<mapsto>S _ _\<close> [70,70,70] 80) where
  \<open>P \<mapsto>S \<alpha> Q \<equiv> (\<forall>q \<in> Q. \<exists>p \<in> P. p \<mapsto> \<alpha> q) \<and> (\<forall>p \<in> P. \<forall>q. p \<mapsto> \<alpha> q \<longrightarrow> q \<in> Q)\<close>

text \<open>The set of \<open>\<alpha>\<close>-derivatives for a set of states \<open>P\<close>.\<close>
definition step_set :: \<open>'s set \<Rightarrow> 'a \<Rightarrow> 's set\<close> where
  \<open>step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto> \<alpha> q }\<close>

text \<open>The set of possible \<open>\<alpha>\<close>-steps for a set of states \<open>P\<close> is an instance of \<^term>\<open>step\<close> lifted to sets of steps.\<close>
lemma step_set_is_step_set: \<open>P \<mapsto>S \<alpha> (step_set P \<alpha>)\<close>
  using step_set_def by force

text \<open>The lifted \<^term>\<open>step_setp\<close> (\<open>P \<mapsto>S \<alpha> Q\<close>) is therefore this set \<open>Q\<close>.\<close>
lemma step_set_eq:
  assumes \<open>P \<mapsto>S \<alpha> Q\<close>
  shows \<open>Q = step_set P \<alpha>\<close>
  using assms step_set_is_step_set by fastforce

end \<comment> \<open>of locale \<open>lts\<close>\<close>

subsection \<open>Labeled Transition Systems with Silent Steps\<close>

text \<open>
  We formalize labeled transition systems with silent steps as an extension of ordinary labeled transition systems with a fixed internal action \<open>\<tau>\<close>.
\<close>

locale lts_tau =
  lts step
    for step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto> _ _\<close> [70,70,70] 80) +
    fixes \<tau> :: 'a
begin

text \<open>
  The paper \<^cite>\<open>bj2023silentStepSpectroscopyArxiv\<close> introduces a transition $p \xrightarrow{(\alpha)}p'$ if $p \xrightarrow{\alpha} p'$, or if $\alpha = \tau$ and $p = p'$.
  We define \<^term>\<open>soft_step\<close> analogously and provide the notation \<open>p \<mapsto>a \<alpha> p'\<close>.
\<close>
abbreviation soft_step (\<open>_ \<mapsto>a _ _\<close> [70,70,70] 80) where
  \<open>p \<mapsto>a \<alpha> q \<equiv> p \<mapsto>\<alpha> q \<or> (\<alpha> = \<tau> \<and> p = q)\<close>

inductive silent_reachable :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>  (infix \<open>\<Zsurj>\<close> 80)
  where
    refl: \<open>p \<Zsurj> p\<close> |
    step: \<open>p \<Zsurj> p''\<close> if \<open>p \<mapsto> \<tau> p'\<close> and \<open>p' \<Zsurj> p''\<close>

text \<open>If \<open>p'\<close> is silent-reachable from \<open>p\<close> and there is a \<open>\<tau>\<close>-transition from \<open>p'\<close> to \<open>p''\<close> then \<open>p''\<close> is silent reachable from \<open>p\<close>.\<close>
lemma silent_reachable_append_\<tau>: \<open>p \<Zsurj> p' \<Longrightarrow> p' \<mapsto> \<tau> p'' \<Longrightarrow> p \<Zsurj> p''\<close>
proof (induct rule: silent_reachable.induct)
  case (refl p)
  then show ?case using silent_reachable.intros by blast
next
  case (step p p' p'')
  then show ?case using silent_reachable.intros by blast
qed

text \<open>The relation \<^term>\<open>silent_reachable\<close> is transitive.\<close>
lemma silent_reachable_trans:
  assumes
    \<open>p \<Zsurj> p'\<close>
    \<open>p' \<Zsurj> p''\<close>
  shows
    \<open>p \<Zsurj> p''\<close>
using assms silent_reachable.intros(2)
  by (induct, blast+)

text \<open>The relation \<open>silent_reachable_loopless\<close> is a variation of \<^term>\<open>silent_reachable\<close> that does not use self-loops.\<close>
inductive silent_reachable_loopless :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close>  (infix \<open>\<Zsurj>L\<close> 80)
  where
    \<open>p \<Zsurj>L p\<close> |
    \<open>p \<Zsurj>L p''\<close> if \<open>p \<mapsto> \<tau> p'\<close> and \<open>p' \<Zsurj>L p''\<close> and \<open>p \<noteq> p'\<close>

text \<open>If a state \<open>p'\<close> is \<^term>\<open>silent_reachable\<close> from \<open>p\<close> it is also \<^term>\<open>silent_reachable_loopless\<close>.\<close>
lemma silent_reachable_impl_loopless:
  assumes \<open>p \<Zsurj> p'\<close>
  shows \<open>p \<Zsurj>L p'\<close>
  using assms
proof(induct rule: silent_reachable.induct)
  case (refl p)
  thus ?case by (rule silent_reachable_loopless.intros(1))
next
  case (step p p' p'')
  thus ?case proof(cases \<open>p = p'\<close>)
    case True
    thus ?thesis using step.hyps(3) by auto
  next
    case False
    thus ?thesis using step.hyps silent_reachable_loopless.intros(2) by blast
  qed
qed

lemma tau_chain_reachabilty:
  assumes \<open>\<forall>i < length pp - 1.  pp!i \<mapsto> \<tau> pp!(Suc i)\<close>
  shows \<open>\<forall>j < length pp. \<forall>i \<le> j. pp!i \<Zsurj> pp!j\<close>
proof safe
  fix j i
  assume \<open>j < length pp\<close> \<open>i \<le> j\<close>
  thus \<open>pp!i \<Zsurj> pp!j\<close>
  proof (induct j)
    case 0
    then show ?case
      using silent_reachable.refl by blast
  next
    case (Suc j)
    then show ?case
    proof (induct i)
      case 0
      then show ?case using assms silent_reachable_append_\<tau>
        by (metis Suc_lessD Suc_lessE bot_nat_0.extremum diff_Suc_1)
    next
      case (Suc i)
      then show ?case using silent_reachable.refl assms silent_reachable_append_\<tau>
        by (metis Suc_lessD Suc_lessE  diff_Suc_1 le_SucE)
    qed
  qed
qed

text \<open>A state \<open>p\<close> can reach \<open>p'\<close> weakly by performing an \<open>\<alpha>\<close>-transition, possibly proceeded and followed by any number of \<open>\<tau>\<close>-transitions.\<close>
definition weak_step (\<open>_ \<Zsurj>\<mapsto>\<Zsurj> _ _\<close> [70, 70, 70] 80) where
  \<open>p  \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p' \<equiv> if \<alpha> = \<tau>
                    then p \<Zsurj> p'
                    else \<exists>p1 p2. p \<Zsurj> p1 \<and> p1 \<mapsto> \<alpha> p2 \<and> p2 \<Zsurj> p'\<close>

lemma silent_prepend_weak_step: \<open>p \<Zsurj> p' \<Longrightarrow> p' \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p'' \<Longrightarrow> p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''\<close>
  unfolding weak_step_def using silent_reachable_trans[of p p'] by fastforce

text \<open>A sequence of \<^term>\<open>weak_step\<close>s from one state \<open>p\<close> to another \<open>p'\<close>.\<close>
inductive weak_step_sequence :: \<open>'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<Zsurj>\<mapsto>\<Zsurj>$ _ _\<close> [70,70,70] 80) where
  \<open>p \<Zsurj>\<mapsto>\<Zsurj>$ [] p'\<close> if \<open>p \<Zsurj> p'\<close> |
  \<open>p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha>#rt) p''\<close> if \<open>p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p'\<close> \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ rt p''\<close>

lemma weak_step_sequence_trans:
  assumes \<open>p \<Zsurj>\<mapsto>\<Zsurj>$ tr_1 p'\<close> and \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr_2 p''\<close>
  shows \<open>p \<Zsurj>\<mapsto>\<Zsurj>$ (tr_1 @ tr_2) p''\<close>
  using assms weak_step_sequence.intros(2)
proof induct
  case (1 p p')
  then show ?case
    by (metis weak_step_sequence.simps append_Nil silent_prepend_weak_step silent_reachable_trans)
next
  case (2 p \<alpha> p' rt p'')
  then show ?case by fastforce
qed

text \<open>The weak traces of a state are all possible sequences of weak transitions that can be performed.\<close>
abbreviation weak_traces :: \<open>'s \<Rightarrow> 'a list set\<close>
  where \<open>weak_traces p \<equiv> {tr. \<exists>p'. p \<Zsurj>\<mapsto>\<Zsurj>$ tr p'}\<close>

text \<open>The empty trace is in \<^term>\<open>weak_traces\<close> for all states.\<close>
lemma empty_trace_allways_weak_trace:
  shows \<open>[] \<in> weak_traces p\<close>
  using silent_reachable.intros(1) weak_step_sequence.intros(1) by fastforce

text \<open>\<open>\<tau>\<close> can be prepended to any weak trace.\<close>
lemma prepend_\<tau>_weak_trace:
  assumes \<open>tr \<in> weak_traces p\<close>
  shows \<open>(\<tau> # tr) \<in> weak_traces p\<close>
  using assms silent_reachable.intros(1) mem_Collect_eq
    weak_step_sequence.intros(2) weak_step_def by fastforce

lemma silent_prepend_weak_traces:
  assumes
    \<open>p \<Zsurj> p'\<close>
    \<open>tr \<in> weak_traces p'\<close>
  shows
    \<open>tr \<in> weak_traces p\<close>
  using assms
proof -
  assume \<open>p \<Zsurj> p'\<close>
     and \<open>tr \<in> weak_traces p'\<close>
  hence \<open>\<exists>p''. p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close> by auto
  then obtain p'' where \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close> by auto
  from \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close>
    and \<open>p \<Zsurj> p'\<close>
  have \<open>p \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close>
    by (metis append_self_conv2 weak_step_sequence.intros(1) weak_step_sequence_trans)
  hence \<open>\<exists>p''. p \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close> by auto
  then show \<open>tr \<in> weak_traces p\<close>
    by blast
qed

text \<open>If there is an \<open>\<alpha>\<close>-transition from \<open>p\<close> to \<open>p'\<close>, and \<open>p'\<close> has a weak trace \<open>tr\<close>, then the sequence \<open>(\<alpha> # tr)\<close> is a valid (weak) trace of \<open>p\<close>.\<close>
lemma step_prepend_weak_traces:
  assumes
    \<open>p \<mapsto> \<alpha> p'\<close>
    \<open>tr \<in> weak_traces p'\<close>
  shows
    \<open>(\<alpha> # tr) \<in> weak_traces p\<close>
  using assms
proof -
  from \<open>tr \<in> weak_traces p'\<close>
  have \<open>\<exists>p''. p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close> by auto
  then obtain p'' where \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close> by auto
  with \<open>p \<mapsto> \<alpha> p'\<close>
  have \<open>p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha> # tr) p''\<close>
    by (metis lts_tau.silent_reachable.intros(1) lts_tau.silent_reachable_append_\<tau>
        lts_tau.weak_step_def lts_tau.weak_step_sequence.intros(2))
  then have \<open>\<exists>p''. p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha> # tr) p''\<close> by auto
  then show \<open>(\<alpha> # tr) \<in> weak_traces p\<close> by auto
qed

text \<open>A state is weakly trace pre-ordered to another other, \<open>weakly_trace_preordered\<close>
denoted by \<open>\<lesssim>WT\<close> if all its traces can also be observed from the second process.\<close>
definition weakly_trace_preordered (infix \<open>\<lesssim>WT\<close> 60) where
  \<open>p \<lesssim>WT q \<equiv> weak_traces p \<subseteq> weak_traces q\<close>

definition weakly_trace_equivalent (infix \<open>\<simeq>WT\<close> 60) where
  \<open>p \<simeq>WT q \<equiv> p \<lesssim>WT q \<and> q \<lesssim>WT p\<close>

text \<open>Just like \<^term>\<open>step_setp\<close>, one can lift \<^term>\<open>silent_reachable\<close> to sets of states.\<close>
abbreviation silent_reachable_setp (infix \<open>\<Zsurj>S\<close> 80) where
  \<open>P \<Zsurj>S P' \<equiv> ((\<forall>p' \<in> P'. \<exists>p \<in> P. p \<Zsurj> p') \<and> (\<forall>p \<in> P. \<forall>p'. p \<Zsurj> p' \<longrightarrow> p' \<in> P'))\<close>

definition silent_reachable_set :: \<open>'s set \<Rightarrow> 's set\<close> where
  \<open>silent_reachable_set P \<equiv> { q . \<exists>p \<in> P. p \<Zsurj> q }\<close>

lemma sreachable_set_is_sreachable: \<open>P \<Zsurj>S (silent_reachable_set P)\<close>
  using silent_reachable_set_def by auto

lemma sreachable_set_eq:
  assumes \<open>P \<Zsurj>S Q\<close>
  shows \<open>Q = silent_reachable_set P\<close>
  using sreachable_set_is_sreachable assms by fastforce

text \<open>We likewise lift \<^term>\<open>soft_step\<close> to sets of states.\<close>
abbreviation soft_step_setp (\<open>_ \<mapsto>aS _ _\<close> [70,70,70] 80) where
  \<open>P \<mapsto>aS \<alpha> Q \<equiv> (\<forall>q \<in> Q. \<exists>p \<in> P. p \<mapsto>a \<alpha> q) \<and> (\<forall>p \<in> P. \<forall>q. p \<mapsto>a \<alpha> q \<longrightarrow> q \<in> Q)\<close>

definition soft_step_set :: \<open>'s set \<Rightarrow> 'a \<Rightarrow> 's set\<close> where
  \<open>soft_step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto>a \<alpha> q }\<close>

lemma soft_step_set_is_soft_step_set:
  \<open>P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)\<close>
  using soft_step_set_def by auto

lemma exactly_one_soft_step_set:
  \<open>\<exists>!Q. P \<mapsto>aS \<alpha> Q\<close>
proof -
  from soft_step_set_is_soft_step_set
  have \<open>P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)\<close>
    and \<open>\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)\<close>
    by fastforce+
  show \<open>\<exists>!Q. P \<mapsto>aS \<alpha> Q\<close>
  proof
    from \<open>P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)\<close>
    show \<open>P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)\<close> .
  next
    from \<open>\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)\<close>
    show \<open>\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)\<close> .
  qed
qed

lemma soft_step_set_eq:
  assumes \<open>P \<mapsto>aS \<alpha> Q\<close>
  shows \<open>Q = soft_step_set P \<alpha>\<close>
  using exactly_one_soft_step_set soft_step_set_is_soft_step_set assms
  by fastforce

text \<open>A state is stable if it cannot make any further internal steps.\<close>
abbreviation \<open>stable_state p \<equiv> \<forall>p'. \<not>(p \<mapsto> \<tau> p')\<close>

lemma stable_state_stable:
  assumes \<open>stable_state p\<close> \<open>p \<Zsurj> p'\<close>
  shows \<open>p = p'\<close>
  using assms(2,1) by (cases, blast+)

definition stability_respecting :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>stability_respecting R \<equiv> \<forall> p q. R p q \<and> stable_state p \<longrightarrow>
    (\<exists>q'. q \<Zsurj> q' \<and> R p q' \<and> stable_state q')\<close>

end \<comment> \<open>of locale \<open>lts_tau\<close>\<close>

end