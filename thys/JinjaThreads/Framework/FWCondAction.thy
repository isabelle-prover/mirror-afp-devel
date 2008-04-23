(*  Title:      JinjaThreads/Framework/FWCondAction.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of the thread actions for purely conditional purpose such as Join} *}

theory FWCondAction imports FWState begin

locale final_thread =
  fixes final :: "'x \<Rightarrow> bool"
begin

fun cond_action_ok :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 't conditional_action \<Rightarrow> bool" where
  "cond_action_ok s t (Join T) = (case thr s T of None \<Rightarrow> True | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> final x \<and> ln = no_wait_locks \<and> wset s T = None)"

fun cond_action_oks :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 't conditional_action list \<Rightarrow> bool" where
  "cond_action_oks s t [] = True"
| "cond_action_oks s t (ct#cts) = (cond_action_ok s t ct \<and> cond_action_oks s t cts)"

lemma cond_action_oks_append [simp]:
  "cond_action_oks s t (cts @ cts') \<longleftrightarrow> cond_action_oks s t cts \<and> cond_action_oks s t cts'"
by(induct cts, auto)

lemma cond_action_ok_Join:
  "\<lbrakk> cond_action_ok s t (Join T); thr s T = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> final x \<and> ln = no_wait_locks \<and> wset s T = None"
by(auto)

lemma cond_action_oks_Join:
  "\<lbrakk> cond_action_oks s t cas; Join T \<in> set cas; thr s T = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> final x \<and> ln = no_wait_locks \<and> wset s T = None"
by(induct cas)(auto)


fun cond_action_ok' :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 't conditional_action \<Rightarrow> bool" where
  "cond_action_ok' _ _ _ = True"

fun cond_action_oks' :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 't conditional_action list \<Rightarrow> bool" where
  "cond_action_oks' s t [] = True"
| "cond_action_oks' s t (ct#cts) = (cond_action_ok' s t ct \<and> cond_action_oks' s t cts)"

lemma cond_action_oks'_append [simp]:
  "cond_action_oks' s t (cts @ cts') \<longleftrightarrow> cond_action_oks' s t cts \<and> cond_action_oks' s t cts'"
by(induct cts, auto)

lemma cond_action_oks'_True [simp]:
  "cond_action_oks' s t cts"
by(induct cts, auto)


definition collect_cond_actions :: "'t conditional_action list \<Rightarrow> 't set" where
  "collect_cond_actions cts = {t. Join t \<in> set cts}"

declare collect_cond_actions_def [simp]

end

end
