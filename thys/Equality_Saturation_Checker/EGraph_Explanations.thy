section \<open>Explanations from checked e-class merges\<close>

theory EGraph_Explanations
  imports Equality_Saturation_Checker
begin

text \<open>
  An equality-saturation engine accumulates equalities as it merges e-classes.
  Later explanations should be able to reuse those equalities without replaying
  the original rewrites.  A merge log therefore stores each concrete equality
  together with a flat explanation that may cite only earlier entries.  Checking
  the log from left to right prevents circular justification.

  This is the main distinction from IsaFoR/CeTA's general equational proof
  checker.  The certificate here represents an e-graph's chronological merge
  history and its reuse sites.  All underlying rewriting remains the AFP
  relation \<^const>\<open>rstep\<close>.
\<close>

type_synonym ('f, 'v) merge_log =
  "(('f, 'v) rule \<times> ('f, 'v) certificate_step list) list"

fun check_merge_log_from ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    ('f, 'v) merge_log \<Rightarrow> bool" where
  "check_merge_log_from R \<Gamma> [] = True"
| "check_merge_log_from R \<Gamma> ((ab, sts) # es) =
     (check_explanation R \<Gamma> sts (fst ab) (snd ab) \<and>
      check_merge_log_from R (\<Gamma> @ [ab]) es)"

definition check_merge_log ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) merge_log \<Rightarrow> bool" where
  "check_merge_log R log \<longleftrightarrow> check_merge_log_from R [] log"

definition recorded_merges ::
  "('f, 'v) merge_log \<Rightarrow> ('f, 'v) rule list" where
  "recorded_merges log = map fst log"

lemma check_merge_log_from_sound:
  assumes check: "check_merge_log_from R \<Gamma> es"
    and base: "\<forall>ab \<in> set \<Gamma>.
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  shows "\<forall>ab \<in> set (\<Gamma> @ map fst es).
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  using check base
proof (induction es arbitrary: \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain ab sts where e: "e = (ab, sts)" by (cases e)
  from Cons.prems e have
    cert: "check_explanation R \<Gamma> sts (fst ab) (snd ab)" and
    rest: "check_merge_log_from R (\<Gamma> @ [ab]) es"
    by auto
  have ab_sound:
    "(fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule check_explanation_sound[OF Cons.prems(2) cert])
  have extended: "\<forall>ab' \<in> set (\<Gamma> @ [ab]).
      (fst ab', snd ab') \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    using Cons.prems(2) ab_sound by auto
  have "\<forall>ab' \<in> set ((\<Gamma> @ [ab]) @ map fst es).
      (fst ab', snd ab') \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule Cons.IH[OF rest extended])
  moreover have "(\<Gamma> @ [ab]) @ map fst es = \<Gamma> @ map fst (e # es)"
    using e by simp
  ultimately show ?case by simp
qed

theorem checked_merge_log_sound:
  assumes "check_merge_log R log"
    and "ab \<in> set (recorded_merges log)"
  shows "(fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  have all: "\<forall>ab \<in> set ([] @ map fst log).
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule check_merge_log_from_sound[
          OF assms(1)[unfolded check_merge_log_def]]) simp
  from assms(2) obtain entry where
    entry: "entry \<in> set log" and fst_entry: "fst entry = ab"
    unfolding recorded_merges_def by auto
  from all entry have
    "(fst (fst entry), snd (fst entry))
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by simp
  with fst_entry show ?thesis by simp
qed

theorem egraph_explanation_sound:
  assumes log: "check_merge_log R mlog"
    and cert: "check_explanation R (recorded_merges mlog) sts t u"
  shows "(t, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
proof (rule check_explanation_sound[OF _ cert])
  show "\<forall>ab \<in> set (recorded_merges mlog).
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  proof (intro ballI)
    fix ab
    assume "ab \<in> set (recorded_merges mlog)"
    then show "(fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
      by (rule checked_merge_log_sound[OF log])
  qed
qed

end
