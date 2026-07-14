section \<open>A certificate-producing bounded search\<close>

theory Bounded_Certificate_Search
  imports Equality_Saturation_Checker
begin

text \<open>
  The trusted result in this theory is independent of matching and scheduling.
  An arbitrary generator proposes certificate steps; only proposals accepted by
  \<^const>\<open>apply_step\<close> enter the frontier.  Consequently every path emitted by
  the bounded search is accepted by the independent checker.
\<close>

definition step_children ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    (('f, 'v) term \<Rightarrow> ('f, 'v) certificate_step list) \<Rightarrow>
    ('f, 'v) term \<Rightarrow> ('f, 'v) certificate_step list \<Rightarrow>
    (('f, 'v) term \<times> ('f, 'v) certificate_step list) list" where
  "step_children R \<Gamma> gen u sts =
     concat (map (\<lambda>st. case apply_step R \<Gamma> st u of
                         None \<Rightarrow> []
                       | Some u' \<Rightarrow> [(u', sts @ [st])]) (gen u))"

definition expand ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    (('f, 'v) term \<Rightarrow> ('f, 'v) certificate_step list) \<Rightarrow>
    (('f, 'v) term \<times> ('f, 'v) certificate_step list) \<Rightarrow>
    (('f, 'v) term \<times> ('f, 'v) certificate_step list) list" where
  "expand R \<Gamma> gen p = step_children R \<Gamma> gen (fst p) (snd p)"

fun iterate_search ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    (('f, 'v) term \<Rightarrow> ('f, 'v) certificate_step list) \<Rightarrow> nat \<Rightarrow>
    (('f, 'v) term \<times> ('f, 'v) certificate_step list) list \<Rightarrow>
    (('f, 'v) term \<times> ('f, 'v) certificate_step list) list" where
  "iterate_search R \<Gamma> gen 0 F = F"
| "iterate_search R \<Gamma> gen (Suc n) F =
     iterate_search R \<Gamma> gen n
       (F @ concat (map (expand R \<Gamma> gen) F))"

definition run_bounded_search ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    (('f, 'v) term \<Rightarrow> ('f, 'v) certificate_step list) \<Rightarrow> nat \<Rightarrow>
    ('f, 'v) term \<Rightarrow>
    (('f, 'v) term \<times> ('f, 'v) certificate_step list) list" where
  "run_bounded_search R \<Gamma> gen n t =
    iterate_search R \<Gamma> gen n [(t, [])]"

lemma apply_steps_append:
  "apply_steps R \<Gamma> (as @ bs) t =
     (case apply_steps R \<Gamma> as t of
        None \<Rightarrow> None
      | Some u \<Rightarrow> apply_steps R \<Gamma> bs u)"
  by (induction as arbitrary: t) (auto split: option.splits)

lemma apply_steps_snoc:
  assumes "apply_steps R \<Gamma> sts t = Some u"
    and "apply_step R \<Gamma> st u = Some u'"
  shows "apply_steps R \<Gamma> (sts @ [st]) t = Some u'"
  using assms by (auto simp: apply_steps_append)

lemma step_children_accepted:
  assumes "apply_steps R \<Gamma> sts t = Some u"
    and "(u', sts') \<in> set (step_children R \<Gamma> gen u sts)"
  shows "apply_steps R \<Gamma> sts' t = Some u'"
proof -
  from assms(2) obtain st where
    emit: "(u', sts') \<in>
      set (case apply_step R \<Gamma> st u of
             None \<Rightarrow> []
           | Some v \<Rightarrow> [(v, sts @ [st])])"
    unfolding step_children_def by auto
  then obtain v where
    accepted: "apply_step R \<Gamma> st u = Some v" and
    pair: "(u', sts') = (v, sts @ [st])"
    by (auto split: option.splits)
  from apply_steps_snoc[OF assms(1) accepted] pair show ?thesis by simp
qed

lemma expand_accepted:
  assumes "apply_steps R \<Gamma> (snd p) t = Some (fst p)"
    and "q \<in> set (expand R \<Gamma> gen p)"
  shows "apply_steps R \<Gamma> (snd q) t = Some (fst q)"
proof -
  obtain u sts where q: "q = (u, sts)" by (cases q)
  from assms(2) q have
    "(u, sts) \<in> set (step_children R \<Gamma> gen (fst p) (snd p))"
    by (simp add: expand_def)
  from step_children_accepted[OF assms(1) this] q show ?thesis by simp
qed

lemma iterate_search_accepted:
  assumes "\<forall>p \<in> set F.
      apply_steps R \<Gamma> (snd p) t = Some (fst p)"
  shows "\<forall>p \<in> set (iterate_search R \<Gamma> gen n F).
      apply_steps R \<Gamma> (snd p) t = Some (fst p)"
  using assms
proof (induction n arbitrary: F)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?F = "F @ concat (map (expand R \<Gamma> gen) F)"
  have "\<forall>p \<in> set ?F.
      apply_steps R \<Gamma> (snd p) t = Some (fst p)"
  proof
    fix p
    assume "p \<in> set ?F"
    then consider "p \<in> set F"
      | "p \<in> set (concat (map (expand R \<Gamma> gen) F))"
      by auto
    then show "apply_steps R \<Gamma> (snd p) t = Some (fst p)"
    proof cases
      case 1
      then show ?thesis using Suc.prems by blast
    next
      case 2
      then obtain q where
        "q \<in> set F" and "p \<in> set (expand R \<Gamma> gen q)"
        by auto
      then show ?thesis using expand_accepted Suc.prems by blast
    qed
  qed
  from Suc.IH[OF this] show ?case by simp
qed

theorem run_bounded_search_accepted:
  assumes "(u, sts) \<in> set (run_bounded_search R \<Gamma> gen n t)"
  shows "check_explanation R \<Gamma> sts t u"
proof -
  have "\<forall>p \<in> set [(t, [])].
      apply_steps R \<Gamma> (snd p) t = Some (fst p)"
    by simp
  from assms iterate_search_accepted[OF this]
  have "apply_steps R \<Gamma> sts t = Some u"
    by (fastforce simp: run_bounded_search_def)
  then show ?thesis by (simp add: check_explanation_def)
qed

corollary run_bounded_search_sound:
  assumes merges: "\<forall>ab \<in> set \<Gamma>.
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    and result: "(u, sts) \<in> set (run_bounded_search R \<Gamma> gen n t)"
  shows "(t, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule check_explanation_sound[
        OF merges run_bounded_search_accepted[OF result]])

definition find_explanation ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    (('f, 'v) term \<Rightarrow> ('f, 'v) certificate_step list) \<Rightarrow> nat \<Rightarrow>
    ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) certificate_step list option" where
  "find_explanation R \<Gamma> gen n t u =
     (case filter (\<lambda>p. fst p = u)
       (run_bounded_search R \<Gamma> gen n t) of
        [] \<Rightarrow> None
      | p # _ \<Rightarrow> Some (snd p))"

theorem find_explanation_accepted:
  assumes "find_explanation R \<Gamma> gen n t u = Some sts"
  shows "check_explanation R \<Gamma> sts t u"
proof -
  from assms have
    "filter (\<lambda>p. fst p = u)
      (run_bounded_search R \<Gamma> gen n t) \<noteq> []"
    unfolding find_explanation_def by (auto split: list.splits)
  then obtain p ps where
    filter: "filter (\<lambda>p. fst p = u)
      (run_bounded_search R \<Gamma> gen n t) = p # ps"
    by (cases "filter (\<lambda>p. fst p = u)
          (run_bounded_search R \<Gamma> gen n t)") auto
  from assms filter have snd_p: "snd p = sts"
    unfolding find_explanation_def by simp
  have in_filter:
    "p \<in> set (filter (\<lambda>p. fst p = u)
      (run_bounded_search R \<Gamma> gen n t))"
    using filter by simp
  then have mem:
    "p \<in> set (run_bounded_search R \<Gamma> gen n t)" by simp
  from in_filter have fst_p: "fst p = u" by simp
  from fst_p snd_p have p: "p = (u, sts)" by (cases p) simp
  from mem p have
    "(u, sts) \<in> set (run_bounded_search R \<Gamma> gen n t)" by simp
  then show ?thesis by (rule run_bounded_search_accepted)
qed

corollary find_explanation_sound:
  assumes "\<forall>ab \<in> set \<Gamma>.
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    and "find_explanation R \<Gamma> gen n t u = Some sts"
  shows "(t, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule check_explanation_sound[OF assms(1)
        find_explanation_accepted[OF assms(2)]])

end
