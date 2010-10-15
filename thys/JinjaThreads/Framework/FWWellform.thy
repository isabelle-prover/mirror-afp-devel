(*  Title:      JinjaThreads/Framework/FWWellform.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Wellformedness conditions for the multithreaded state } *}

theory FWWellform imports FWLocking FWThread FWWait begin

text{* Well-formedness property: Locks are held by real threads *}

definition
  lock_thread_ok :: "('l, 't) locks \<Rightarrow> ('l, 't,'x) thread_info \<Rightarrow> bool"
where [code del]:
  "lock_thread_ok ls ts \<equiv> \<forall>l t. has_lock (ls\<^sub>f l) t \<longrightarrow> (\<exists>xw. ts t = \<lfloor>xw\<rfloor>)"

lemma lock_thread_ok_code [code]: 
  "lock_thread_ok ls ts = finfun_All ((\<lambda>l. case l of None \<Rightarrow> True | \<lfloor>(t, n)\<rfloor> \<Rightarrow> (ts t \<noteq> None)) \<circ>\<^isub>f ls)"
by(simp add: lock_thread_ok_def finfun_All_All has_lock_has_locks_conv has_locks_iff o_def)

lemma lock_thread_okI:
  "(\<And>l t. has_lock (ls\<^sub>f l) t \<Longrightarrow> \<exists>xw. ts t = \<lfloor>xw\<rfloor>) \<Longrightarrow> lock_thread_ok ls ts"
by(auto simp add: lock_thread_ok_def)

lemma lock_thread_okD:
  "\<lbrakk> lock_thread_ok ls ts; has_lock (ls\<^sub>f l) t \<rbrakk> \<Longrightarrow> \<exists>xw. ts t = \<lfloor>xw\<rfloor>"
by(fastsimp simp add: lock_thread_ok_def)

lemma lock_thread_okD':
  "\<lbrakk> lock_thread_ok ls ts; has_locks (ls\<^sub>f l) t = Suc n \<rbrakk> \<Longrightarrow> \<exists>xw. ts t = \<lfloor>xw\<rfloor>"
by(auto elim: lock_thread_okD[where l=l] simp del: split_paired_Ex)

lemma lock_thread_okE:
  "\<lbrakk> lock_thread_ok ls ts; \<forall>l t. has_lock (ls\<^sub>f l) t \<longrightarrow> (\<exists>xw. ts t = \<lfloor>xw\<rfloor>) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: lock_thread_ok_def simp del: split_paired_Ex)

lemma lock_thread_ok_upd:
  "lock_thread_ok ls ts \<Longrightarrow> lock_thread_ok ls (ts(t \<mapsto> xw))"
by(auto intro!: lock_thread_okI dest: lock_thread_okD)

lemma lock_thread_ok_has_lockE:
  assumes "lock_thread_ok ls ts"
  and "has_lock (ls\<^sub>f l) t"
  obtains x ln where "ts t = \<lfloor>(x, ln)\<rfloor>"
using assms
by(auto dest!: lock_thread_okD)

lemma redT_updLs_preserves_lock_thread_ok:
  assumes lto: "lock_thread_ok ls ts"
  and tst: "ts t = \<lfloor>xw\<rfloor>"
  shows "lock_thread_ok (redT_updLs ls t las) ts"
proof(rule lock_thread_okI)
  fix L T
  assume ru: "has_lock ((redT_updLs ls t las)\<^sub>f L) T"
  show "\<exists>xw. ts T = \<lfloor>xw\<rfloor>"
  proof(cases "t = T")
    case True
    thus ?thesis using tst lto
      by(auto elim: lock_thread_okE)
  next
    case False
    with ru have "has_lock (ls\<^sub>f L) T"
      by(rule redT_updLs_Some_thread_idD) 
    thus ?thesis using lto
      by(auto elim!: lock_thread_okE simp del: split_paired_Ex)
  qed
qed

lemma redT_updTs_preserves_lock_thread_ok:
  assumes lto: "lock_thread_ok ls ts"
  shows "lock_thread_ok ls (redT_updTs ts nts)"
proof(rule lock_thread_okI)
  fix l t
  assume "has_lock (ls\<^sub>f l) t"
  with lto have "\<exists>xw. ts t = \<lfloor>xw\<rfloor>"
    by(auto elim!: lock_thread_okE simp del: split_paired_Ex)
  thus "\<exists>xw. redT_updTs ts nts t = \<lfloor>xw\<rfloor>"
    by(auto intro: redT_updTs_Some1 simp del: split_paired_Ex)
qed

lemma lock_thread_ok_has_lock:
  assumes "lock_thread_ok ls ts"
  and "has_lock (ls\<^sub>f l) t"
  obtains xw where "ts t = \<lfloor>xw\<rfloor>"
using assms
by(auto dest!: lock_thread_okD)

lemma lock_thread_ok_None_has_locks_0:
  "\<lbrakk> lock_thread_ok ls ts; ts t = None \<rbrakk> \<Longrightarrow> has_locks (ls\<^sub>f l) t = 0"
by(rule ccontr)(auto dest: lock_thread_okD)

lemma redT_upds_preserves_lock_thread_ok:
  "\<lbrakk>lock_thread_ok ls ts; ts t = \<lfloor>xw\<rfloor>; thread_oks ts tas\<rbrakk>
  \<Longrightarrow> lock_thread_ok (redT_updLs ls t las) (redT_updTs ts tas(t \<mapsto> xw'))"
apply(rule lock_thread_okI)
apply(clarsimp simp del: split_paired_Ex)
apply(drule has_lock_upd_locks_implies_has_lock, simp)
apply(drule lock_thread_okD, assumption)
apply(erule exE)
by(rule redT_updTs_Some1)

lemma acquire_all_preserves_lock_thread_ok:
  "\<lbrakk> lock_thread_ok ls ts; ts t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> lock_thread_ok (acquire_all ls t ln) (ts(t \<mapsto> xw))"
by(rule lock_thread_okI, auto dest!: has_lock_acquire_locks_implies_has_lock dest: lock_thread_okD)

text {* Well-formedness condition: Wait sets contain only real threads *}

definition wset_thread_ok :: "('w, 't) wait_sets \<Rightarrow> ('l, 't, 'x) thread_info \<Rightarrow> bool"
where "wset_thread_ok ws ts \<equiv> \<forall>t. ts t = None \<longrightarrow> ws t = None"

lemma wset_thread_okI:
  "(\<And>t. ts t = None \<Longrightarrow> ws t = None) \<Longrightarrow> wset_thread_ok ws ts"
by(simp add: wset_thread_ok_def)

lemma wset_thread_okD:
  "\<lbrakk> wset_thread_ok ws ts; ts t = None \<rbrakk> \<Longrightarrow> ws t = None"
by(simp add: wset_thread_ok_def)

lemma wset_thread_ok_upd:
  "wset_thread_ok ls ts \<Longrightarrow> wset_thread_ok ls (ts(t \<mapsto> xw))"
by(auto intro!: wset_thread_okI dest: wset_thread_okD split: split_if_asm)

lemma wset_thread_ok_upd_None:
  "wset_thread_ok ws ts \<Longrightarrow> wset_thread_ok (ws(t := None)) (ts(t := None))"
by(auto intro!: wset_thread_okI dest: wset_thread_okD split: split_if_asm)

lemma wset_thread_ok_upd_Some:
  "wset_thread_ok ws ts \<Longrightarrow> wset_thread_ok (ws(t := wo)) (ts(t \<mapsto> xln))"
by(auto intro!: wset_thread_okI dest: wset_thread_okD split: split_if_asm)

lemma wset_thread_ok_upd_ws:
  "\<lbrakk> wset_thread_ok ws ts; ts t = \<lfloor>xln\<rfloor> \<rbrakk> \<Longrightarrow> wset_thread_ok (ws(t := w)) ts"
by(auto intro!: wset_thread_okI dest: wset_thread_okD)

lemma wset_thread_ok_NotifyAllI: 
  "wset_thread_ok ws ts \<Longrightarrow> wset_thread_ok (\<lambda>t. if ws t = \<lfloor>w t\<rfloor> then \<lfloor>w' t\<rfloor> else ws t) ts"
by(simp add: wset_thread_ok_def)

lemma redT_updTs_preserves_wset_thread_ok:
  assumes wto: "wset_thread_ok ws ts"
  shows "wset_thread_ok ws (redT_updTs ts nts)"
proof(rule wset_thread_okI)
  fix t
  assume "redT_updTs ts nts t = None"
  hence "ts t = None" by(rule redT_updTs_None)
  with wto show "ws t = None" by(rule wset_thread_okD)
qed

lemma redT_updW_preserve_wset_thread_ok: 
  "\<lbrakk> wset_thread_ok ws ts; redT_updW t ws wa ws'; ts t = \<lfloor>xln\<rfloor> \<rbrakk> \<Longrightarrow> wset_thread_ok ws' ts"
by(fastsimp simp add: redT_updW.simps intro: wset_thread_okI wset_thread_ok_NotifyAllI wset_thread_ok_upd_ws dest: wset_thread_okD)

lemma redT_updWs_preserve_wset_thread_ok:
  "\<lbrakk> wset_thread_ok ws ts; redT_updWs t ws was ws'; ts t = \<lfloor>xln\<rfloor> \<rbrakk> \<Longrightarrow> wset_thread_ok ws' ts"
unfolding redT_updWs_def apply(rotate_tac 1)
by(induct rule: rtrancl3p_converse_induct)(auto intro: redT_updW_preserve_wset_thread_ok)

end
