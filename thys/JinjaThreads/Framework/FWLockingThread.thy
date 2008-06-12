(*  Title:      JinjaThreads/Framework/FWLockingThread.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of the thread action ReleaseAcquire for the thread state} *}

theory FWLockingThread imports FWLocking begin

fun upd_threadR :: "nat \<Rightarrow> 't lock \<Rightarrow> 't \<Rightarrow> lock_action \<Rightarrow> nat"
where
  "upd_threadR n l t ReleaseAcquire = n + has_locks l t"
| "upd_threadR n l t _ = n"

fun upd_threadRs :: "nat \<Rightarrow> 't lock \<Rightarrow> 't \<Rightarrow> lock_action list \<Rightarrow> nat"
where
  "upd_threadRs n l t [] = n"
| "upd_threadRs n l t (la # las) = upd_threadRs (upd_threadR n l t la) (upd_lock l t la) t las"

lemma upd_threadRs_append [simp]:
  "upd_threadRs n l t (las @ las') = upd_threadRs (upd_threadRs n l t las) (upd_locks l t las) t las'"
by(induct las arbitrary: n l, auto)


definition redT_updLns :: "('l,'t) locks \<Rightarrow> 't \<Rightarrow> ('l \<Rightarrow> nat) \<Rightarrow> 'l lock_actions \<Rightarrow> ('l \<Rightarrow> nat)"
where "redT_updLns ls t ln las \<equiv> (\<lambda>l. upd_threadRs (ln l) (ls l) t (las l))"

lemma redT_updLns_iff [simp]:
  "redT_updLns ls t ln las l = upd_threadRs (ln l) (ls l) t (las l)"
by(simp add: redT_updLns_def)



end
