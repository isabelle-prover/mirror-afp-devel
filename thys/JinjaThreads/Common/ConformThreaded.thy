(*  Title:      JinjaThreads/Common/ConformThreaded.thy
    Author:     Andreas Lochbihler
*)

header{* \isaheader{Conformance for threads} *}

theory ConformThreaded imports "../Framework/FWState" Exceptions  begin

text {* Every thread must be represented as an object whose address is its thread ID *}

definition thread_conf :: "'m prog \<Rightarrow> (addr,thread_id,'x) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where "thread_conf P ts h \<equiv> \<forall>t xln. ts t = \<lfloor>xln\<rfloor> \<longrightarrow> (\<exists>T. typeof\<^bsub>h\<^esub> (Addr t) = Some T \<and> P \<turnstile> T \<le> Class Thread)"

lemma thread_confI:
  "(\<And>t xln. ts t = \<lfloor>xln\<rfloor> \<Longrightarrow> \<exists>T. typeof\<^bsub>h\<^esub> (Addr t) = Some T \<and> P \<turnstile> T \<le> Class Thread) \<Longrightarrow> thread_conf P ts h"
unfolding thread_conf_def by blast

lemma thread_confDE:
  assumes "thread_conf P ts h" "ts t = \<lfloor>xln\<rfloor>"
  obtains T where "typeof\<^bsub>h\<^esub> (Addr t) = Some T" "P \<turnstile> T \<le> Class Thread"
using assms unfolding thread_conf_def by blast

lemma thread_conf_hext:
  "\<lbrakk> thread_conf P ts h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> thread_conf P ts h'"
apply(rule thread_confI)
apply(erule thread_confDE, assumption)
apply(clarsimp split: heapobj.split_asm)
 apply(drule hext_objD, assumption)
 apply(fastsimp)
apply(drule hext_arrD, assumption)
apply(fastsimp)
done

lemma thread_conf_ts_upd_eq [simp]:
  assumes tst: "ts t = \<lfloor>xln\<rfloor>"
  shows "thread_conf P (ts(t \<mapsto> xln')) h \<longleftrightarrow> thread_conf P ts h"
proof
  assume tc: "thread_conf P (ts(t \<mapsto> xln')) h"
  show "thread_conf P ts h"
  proof(rule thread_confI)
    fix T XLN
    assume "ts T = \<lfloor>XLN\<rfloor>"
    with tc show "\<exists>T'. typeof\<^bsub>h\<^esub> (Addr T) = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> Class Thread"
      by(cases "T = t")(auto elim: thread_confDE)
  qed
next
  assume tc: "thread_conf P ts h"
  show "thread_conf P (ts(t \<mapsto> xln')) h"
  proof(rule thread_confI)
    fix T XLN
    assume "(ts(t \<mapsto> xln')) T = \<lfloor>XLN\<rfloor>"
    with tst obtain XLN' where "ts T = \<lfloor>XLN'\<rfloor>"
      by(cases "T = t")(auto)
    with tc show "\<exists>T'. typeof\<^bsub>h\<^esub> (Addr T) = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> Class Thread"
      by(auto elim: thread_confDE)
  qed
qed

end