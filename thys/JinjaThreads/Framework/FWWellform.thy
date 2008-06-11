(*  Title:      JinjaThreads/Framework/FWWellform.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Wellformedness conditions for the multithreaded state } *}

theory FWWellform imports FWLocking FWThread begin

(* well-formedness properties *)

(* locks are held by real threads *)
definition
  lock_thread_ok :: "('l, 't) locks \<Rightarrow> ('t,'x) thread_info \<Rightarrow> bool"
where
  "lock_thread_ok ls ts \<equiv> \<forall>l. (case ls l of None     \<Rightarrow> True
                                       | \<lfloor>(t, n)\<rfloor>  \<Rightarrow> \<exists>x. ts t = \<lfloor>x\<rfloor>)"

lemma lock_thread_okI:
  "(\<And>l t n. ls l = \<lfloor>(t, n)\<rfloor> \<Longrightarrow> \<exists>x. ts t = \<lfloor>x\<rfloor>) \<Longrightarrow> lock_thread_ok ls ts"
by(simp add: lock_thread_ok_def)

lemma lock_thread_okD:
  "\<lbrakk> lock_thread_ok ls ts; ls l = \<lfloor>(t, n)\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>x. ts t = \<lfloor>x\<rfloor>"
by(fastsimp simp add: lock_thread_ok_def)

lemma lock_thread_okE:
  "\<lbrakk> lock_thread_ok ls ts; \<forall>l t n. ls l = \<lfloor>(t, n)\<rfloor> \<longrightarrow> (\<exists>x. ts t = \<lfloor>x\<rfloor>) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: lock_thread_ok_def)

lemma lock_thread_ok_upd:
  "lock_thread_ok ls ts \<Longrightarrow> lock_thread_ok ls (ts(t \<mapsto> x))"
by(auto intro!: lock_thread_okI dest: lock_thread_okD)

lemma redT_updLs_preserves_lock_thread_ok:
  assumes lto: "lock_thread_ok ls ts"
  and tst: "ts t = \<lfloor>x\<rfloor>"
  shows "lock_thread_ok (redT_updLs ls t las) ts"
proof(rule lock_thread_okI)
  fix L T N
  assume ru: "redT_updLs ls t las L = \<lfloor>(T, N)\<rfloor>"
  show "\<exists>x. ts T = \<lfloor>x\<rfloor>"
  proof(cases "t = T")
    case True
    thus ?thesis using tst lto
      by(auto elim: lock_thread_okE)
  next
    case False
    with ru have "\<exists>n. ls L = \<lfloor>(T, n)\<rfloor>"
      by -(erule redT_updLs_Some_thread_idD)
    thus ?thesis using lto by(auto elim!: lock_thread_okE)
  qed
qed

lemma redT_updTs_preserves_lock_thread_ok:
  assumes lto: "lock_thread_ok ls ts"
  shows "lock_thread_ok ls (redT_updTs ts nts)"
proof(rule lock_thread_okI)
  fix l t n
  assume "ls l = \<lfloor>(t, n)\<rfloor>"
  with lto have "\<exists>x. ts t = \<lfloor>x\<rfloor>"
    by(auto elim!: lock_thread_okE)
  thus "\<exists>x. redT_updTs ts nts t = \<lfloor>x\<rfloor>"
    by(auto intro: redT_updTs_Some1)
qed

lemmas redT_upds_preserves_lock_thread_ok = redT_updTs_preserves_lock_thread_ok[OF redT_updLs_preserves_lock_thread_ok]

end
