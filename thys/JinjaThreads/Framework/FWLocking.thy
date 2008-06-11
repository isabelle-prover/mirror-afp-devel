(*  Title:      JinjaThreads/Framework/FWLocking.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of the thread actions for locking} *}

theory FWLocking imports FWState begin

(* Abstractions for the locks map *)

definition has_locks :: "'t lock \<Rightarrow> 't \<Rightarrow> nat \<Rightarrow> bool" where
  "has_locks l t n \<equiv> case l of None \<Rightarrow> n = 0 | \<lfloor>(t', n')\<rfloor> \<Rightarrow> (t \<noteq> t' \<and> n = 0) \<or> (t = t' \<and> n = Suc n')"

lemma has_locksI:
  "(l = None \<and> n = 0) \<or> (\<exists>n'. l = \<lfloor>(t, n')\<rfloor> \<and> Suc n' = n) \<or> (\<exists>t' n'. l = \<lfloor>(t', n')\<rfloor> \<and> t' \<noteq> t \<and> n = 0) \<Longrightarrow> has_locks l t n"
by(auto simp add: has_locks_def)

lemma has_locksE:
  "\<lbrakk> has_locks l t n;
     \<lbrakk> l = None; n = 0 \<rbrakk> \<Longrightarrow> P;
     \<And>n'. \<lbrakk> l = \<lfloor>(t, n')\<rfloor>; Suc n' = n \<rbrakk> \<Longrightarrow> P;
     \<And>t' n'. \<lbrakk> l = \<lfloor>(t', n')\<rfloor>; t' \<noteq> t; n = 0 \<rbrakk> \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
by(auto simp add: has_locks_def)

definition may_lock :: "'t lock \<Rightarrow> 't \<Rightarrow> bool" where
  "may_lock l t \<equiv> (l = None) \<or> (\<exists>n. l = \<lfloor>(t, n)\<rfloor>)"

lemma may_lockI:
  "l = None \<or> (\<exists>n. l = \<lfloor>(t, n)\<rfloor>) \<Longrightarrow> may_lock l t"
by(simp add: may_lock_def)

lemma may_lockE:
  "\<lbrakk> may_lock l t; l = None \<Longrightarrow> P; \<And>n. l = \<lfloor>(t, n)\<rfloor>  \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: may_lock_def)

lemma may_lock_may_lock_t_eq:
  "\<lbrakk> may_lock l t; may_lock l t' \<rbrakk> \<Longrightarrow> (l = None) \<or> (t = t')"
by(auto elim!: may_lockE)

definition
  has_lock :: "'t lock \<Rightarrow> 't \<Rightarrow> bool"
  where "has_lock l t \<equiv> \<exists>n. has_locks l t (Suc n)"

lemma has_lockI:
  "\<exists>n. l = \<lfloor>(t, n)\<rfloor> \<Longrightarrow> has_lock l t"
by(auto simp add: has_lock_def intro: has_locksI)

lemma has_lockE:
  "\<lbrakk> has_lock l t; \<And>n. l = \<lfloor>(t, n)\<rfloor> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: has_lock_def elim!: has_locksE)

lemma has_locks_Suc_has_lock:
  "has_locks l t (Suc n) \<Longrightarrow> has_lock l t"
by(auto simp add: has_lock_def)

lemma has_lock_has_locks_Suc:
  "has_lock l t \<Longrightarrow> \<exists>n. has_locks l t (Suc n)"
by(auto simp add: has_lock_def)

lemma has_lock_has_locks_conv:
  "has_lock l t \<longleftrightarrow> (\<exists>n. has_locks l t (Suc n))"
by(auto intro: has_locks_Suc_has_lock has_lock_has_locks_Suc)

lemma has_lock_may_lock:
  "has_lock l t \<Longrightarrow> may_lock l t"
by(auto intro!: may_lockI elim!: has_lockE)

lemma has_lock_may_lock_t_eq:
  "\<lbrakk> has_lock l t; may_lock l t' \<rbrakk> \<Longrightarrow> t = t'"
by(auto elim!: has_lockE may_lockE)

lemma has_lock_has_lock_t_eq:
  "\<lbrakk> has_lock l t; has_lock l t' \<rbrakk> \<Longrightarrow> t = t'"
by(auto elim!: has_lockE)

lemma not_may_lock_conv:
  "\<not> may_lock l t \<longleftrightarrow> (\<exists>t'. t' \<noteq> t \<and> has_lock l t')"
proof(rule iffI)
  assume nml: "\<not> may_lock l t"
  show "\<exists>t'. t' \<noteq> t \<and> has_lock l t'"
  proof(cases l)
    case None
    with nml show ?thesis
      by(auto intro: may_lockI)
  next
    case (Some a)
    then obtain t' n where l: "l = \<lfloor>(t', n)\<rfloor>" by (cases a, auto)
    from nml l have "t' \<noteq> t"
      by(auto intro: may_lockI)
    moreover from l have "has_lock l t'"
      by(auto intro: has_lockI)
    ultimately show ?thesis by blast
  qed
next
  assume "\<exists>t'. t' \<noteq> t \<and> has_lock l t'"
  then obtain t'
    where t't: "t' \<noteq> t"
    and hl: "has_lock l t'"
    by blast
  show "\<not> may_lock l t"
  proof(rule notI)
    assume "may_lock l t"
    with hl have "t' = t"
      by(rule has_lock_may_lock_t_eq)
    with t't show False by simp
  qed  
qed

(* State update functions for locking *)

fun
  lock_lock :: "'t lock \<Rightarrow> 't \<Rightarrow> 't lock"
where
  "lock_lock None t = \<lfloor>(t, 0)\<rfloor>"
| "lock_lock \<lfloor>(t', n)\<rfloor> t = \<lfloor>(t', Suc n)\<rfloor>"


fun
  unlock_lock :: "'t lock \<Rightarrow> 't lock"
where
  "unlock_lock None = None"
| "unlock_lock \<lfloor>(t, n)\<rfloor> = (case n of 0 \<Rightarrow> None | Suc n' \<Rightarrow> \<lfloor>(t, n')\<rfloor>)"



lemma lock_lock_ls_Some:
  "\<exists>t' n. lock_lock l t = \<lfloor>(t', n)\<rfloor>"
by(cases l, auto)

lemma unlock_lock_SomeD:
  "unlock_lock l = \<lfloor>(t', n)\<rfloor> \<Longrightarrow> l = \<lfloor>(t', Suc n)\<rfloor>"
apply(cases l, auto)
by(case_tac b, auto)+


lemma has_locks_Suc_lock_lock_has_locks_Suc_Suc:
  "has_locks l t (Suc n) \<Longrightarrow> has_locks (lock_lock l t) t (Suc (Suc n))"
by(auto elim!: has_locksE intro: has_locksI)

lemma may_lock_has_locks_lock_lock_has_locks_Suc:
  "\<lbrakk> may_lock l t; has_locks l t n \<rbrakk> \<Longrightarrow> has_locks (lock_lock l t) t (Suc n)"
by(auto elim!: has_locksE may_lockE intro: has_locksI)

lemma has_locks_Suc_unlock_lock_has_locks:
  "has_locks l t (Suc n) \<Longrightarrow> has_locks (unlock_lock l) t n"
apply(auto elim!: has_locksE intro!: has_locksI)
by(cases n, auto)+

lemma has_lock_lock_lock_unlock_lock_id:
  "has_lock l t \<Longrightarrow> lock_lock (unlock_lock l) t = l"
apply(auto elim!: has_lockE intro: ext)
by(case_tac n, auto intro: ext)

lemma may_lock_unlock_lock_lock_lock_id:
  "may_lock l t \<Longrightarrow> unlock_lock (lock_lock l t) = l"
by(auto intro: ext elim!: may_lockE)


lemma may_lock_t_may_lock_unlock_lock_t: 
  "may_lock l t \<Longrightarrow> may_lock (unlock_lock l) t"
apply(rule may_lockI, erule may_lockE, auto )
apply(case_tac n, auto)
done



fun upd_lock :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action \<Rightarrow> 't lock"
where
  "upd_lock l t Lock = lock_lock l t"
| "upd_lock l t Unlock = unlock_lock l"
| "upd_lock l t UnlockFail = l"

fun upd_locks :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action list \<Rightarrow> 't lock"
where
  "upd_locks l t [] = l"
| "upd_locks l t (L # Ls) = upd_locks (upd_lock l t L) t Ls"

lemma upd_locks_append [simp]:
  "upd_locks l t (Ls @ Ls') = upd_locks (upd_locks l t Ls) t Ls'"
apply(induct Ls arbitrary: l)
apply(auto)
done
lemma upd_lock_Some_thread_idD:
  assumes ul: "upd_lock l t L = \<lfloor>(t', n)\<rfloor>"
  and tt': "t \<noteq> t'"
  shows "\<exists>n. l = \<lfloor>(t', n)\<rfloor>"
proof(cases L)
  case Lock
  with ul tt' show ?thesis
    by(cases l, auto)
next
  case Unlock
  with ul tt' show ?thesis
    by(auto dest: unlock_lock_SomeD)
next
  case UnlockFail
  with ul show ?thesis by simp
qed

lemma upd_locks_Some_thread_idD:
  assumes ul: "upd_locks l t Ls = \<lfloor>(t', n)\<rfloor>"
  and tt': "t \<noteq> t'"
  shows "\<exists>n. l = \<lfloor>(t', n)\<rfloor>"
using ul
proof(induct Ls arbitrary: l)
  case Nil thus ?case by simp
next
  case (Cons L LS l)
  note IH = `\<And>l. upd_locks l t LS = \<lfloor>(t', n)\<rfloor> \<Longrightarrow> \<exists>n. l = \<lfloor>(t', n)\<rfloor>`
  note `upd_locks l t (L # LS) = \<lfloor>(t', n)\<rfloor>`
  hence ul: "upd_locks (upd_lock l t L) t LS = \<lfloor>(t', n)\<rfloor>" by(simp)
  hence "\<exists>n. upd_lock l t L = \<lfloor>(t', n)\<rfloor>" by(rule IH)
  thus ?case using tt'
    by(auto intro: upd_lock_Some_thread_idD)
qed


definition redT_updLs :: "('l,'t) locks \<Rightarrow> 't \<Rightarrow> 'l lock_actions \<Rightarrow> ('l,'t) locks" where
  "redT_updLs ls t las \<equiv> \<lambda>l. upd_locks (ls l) t (las l)"

lemma redT_updLs_append[simp]:
  "redT_updLs ls t (las @@ las') = redT_updLs (redT_updLs ls t las) t las'"
apply(simp add: lock_actions_append_def redT_updLs_def)
done


lemma redT_updLs_Some_thread_idD:
  "\<lbrakk> redT_updLs ls t las l = \<lfloor>(t', n)\<rfloor>; t \<noteq> t' \<rbrakk> \<Longrightarrow> \<exists>n. ls l = \<lfloor>(t', n)\<rfloor>"
by(auto simp add: redT_updLs_def intro: upd_locks_Some_thread_idD)


(* Preconditions for lock actions *)

fun lock_action_ok :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action \<Rightarrow> bool" where
  "lock_action_ok l t Lock = may_lock l t"
| "lock_action_ok l t Unlock = has_lock l t"
| "lock_action_ok l t UnlockFail = (\<not> has_lock l t)"

fun lock_actions_ok :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action list \<Rightarrow> bool" where
  "lock_actions_ok l t [] = True"
| "lock_actions_ok l t (L # Ls) = (lock_action_ok l t L \<and> lock_actions_ok (upd_lock l t L) t Ls)"

lemma lock_actions_ok_append [simp]:
  "lock_actions_ok l t (Ls @ Ls') \<longleftrightarrow> lock_actions_ok l t Ls \<and> lock_actions_ok (upd_locks l t Ls) t Ls'"
apply(induct Ls arbitrary: l)
apply(auto)
done

lemma not_lock_action_okE:
  "\<lbrakk> \<not> lock_action_ok l t L;
     \<lbrakk> L = Lock; \<not> may_lock l t \<rbrakk> \<Longrightarrow> Q;
     \<lbrakk> L = Unlock; \<not> has_lock l t \<rbrakk> \<Longrightarrow> Q;
     \<lbrakk> L = UnlockFail; has_lock l t \<rbrakk> \<Longrightarrow> Q\<rbrakk>
  \<Longrightarrow> Q"
by(cases L, auto)

lemma not_lock_actions_ok_conv:
  "(\<not> lock_actions_ok l t las) = (\<exists>xs L ys. las = xs @ L # ys \<and> lock_actions_ok l t xs \<and> \<not> lock_action_ok (upd_locks l t xs) t L)"
proof(induct las arbitrary: l)
  case Nil thus ?case by(simp)
next
  case (Cons la las l)
  note IH = `\<And>l. (\<not> lock_actions_ok l t las) = (\<exists>xs L ys. las = xs @ L # ys \<and> lock_actions_ok l t xs \<and> \<not> lock_action_ok (upd_locks l t xs) t L)`
  have IH': "(\<not> lock_actions_ok (upd_lock l t la) t las) =
             (\<exists>xs L ys. las = xs @ L # ys \<and> lock_actions_ok (upd_lock l t la) t xs 
                      \<and> \<not> lock_action_ok (upd_locks (upd_lock l t la) t xs) t L)"
    by(rule IH)
  show ?case
  proof(cases "lock_action_ok l t la")
    case True
    hence "(\<not> lock_actions_ok l t (la # las)) = (\<not> lock_actions_ok (upd_lock l t la) t las)"
      by auto
    also note IH'
    also have "(\<exists>xs L ys. las = xs @ L # ys \<and> lock_actions_ok (upd_lock l t la) t xs \<and> \<not> lock_action_ok (upd_locks (upd_lock l t la) t xs) t L) = 
               (\<exists>xs L ys. la # las = xs @ L # ys \<and> lock_actions_ok l t xs \<and> \<not> lock_action_ok (upd_locks l t xs) t L)" 
    proof(rule iffI)
      assume "\<exists>xs L ys. las = xs @ L # ys \<and> lock_actions_ok (upd_lock l t la) t xs \<and> \<not> lock_action_ok (upd_locks (upd_lock l t la) t xs) t L"
      then obtain xs L ys
	where "las = xs @ L # ys"
	and "lock_actions_ok (upd_lock l t la) t xs"
	and "\<not> lock_action_ok (upd_locks (upd_lock l t la) t xs) t L"
	by blast
      with True 
      have "(la # las) = (la # xs) @ L # ys"
	and "lock_actions_ok l t (la # xs)"
	and "\<not> lock_action_ok (upd_locks l t (la # xs)) t L"
	by(auto)
      thus "\<exists>xs L ys. la # las = xs @ L # ys \<and> lock_actions_ok l t xs \<and> \<not> lock_action_ok (upd_locks l t xs) t L"
	by blast
    next
      assume "\<exists>xs L ys. la # las = xs @ L # ys \<and> lock_actions_ok l t xs \<and> \<not> lock_action_ok (upd_locks l t xs) t L"
      then obtain xs L ys
	where "la # las = xs @ L # ys"
	and "lock_actions_ok l t xs"
	and "\<not> lock_action_ok (upd_locks l t xs) t L"
	by blast
      moreover
      with True have "xs \<noteq> []" by(auto)
      then obtain la' xs' where "xs = la' # xs'" by(cases xs, auto)
      ultimately
      have "las = xs' @ L # ys"
	and "lock_actions_ok (upd_lock l t la) t xs'"
	and "\<not> lock_action_ok (upd_locks (upd_lock l t la) t xs') t L"
	by(auto)
      thus "\<exists>xs L ys. las = xs @ L # ys \<and> lock_actions_ok (upd_lock l t la) t xs \<and> \<not> lock_action_ok (upd_locks (upd_lock l t la) t xs) t L" by blast
    qed
    finally show ?thesis .
  next
    case False
    hence "\<not> lock_actions_ok l t (la # las)" by simp
    moreover
    with False have "la # las = [] @ la # las"
      and "lock_actions_ok l t []"
      and "\<not> lock_action_ok (upd_locks l t []) t la"
      by (auto)
    ultimately show ?thesis
      by blast
  qed
qed


lemma lock_action_ok_may_lock_upd_lock_may_lock:
  assumes lao: "lock_action_ok l t L"
  and ml: "may_lock (upd_lock l t L) t"
  shows "may_lock l t"
proof(cases L)
  case Lock
  with lao show ?thesis by simp
next
  case Unlock
  with lao show ?thesis by(auto intro: has_lock_may_lock)
next
  case UnlockFail
  with ml show ?thesis by(simp)
qed

lemma lock_actions_ok_may_lock_upd_locks_may_lock:
  "\<lbrakk> lock_actions_ok l t Ls; may_lock (upd_locks l t Ls) t \<rbrakk> \<Longrightarrow> may_lock l t"
proof(induct Ls arbitrary: l)
  case Nil thus ?case by(auto intro: has_lock_may_lock)
next
  case (Cons L LS l)
  note IH = `\<And>l. \<lbrakk>lock_actions_ok l t LS; may_lock (upd_locks l t LS) t\<rbrakk> \<Longrightarrow> may_lock l t`
  note `lock_actions_ok l t (L # LS)`
  hence lao: "lock_action_ok l t L"
    and laos: "lock_actions_ok (upd_lock l t L) t LS"
    by auto
  note `may_lock (upd_locks l t (L # LS)) t`
  hence "may_lock (upd_locks (upd_lock l t L) t LS) t" by(simp)
  with IH[OF laos] have "may_lock (upd_lock l t L) t" .
  with lao show ?case by(rule lock_action_ok_may_lock_upd_lock_may_lock)
qed




definition lock_ok_las :: "('l,'t) locks \<Rightarrow> 't \<Rightarrow> 'l lock_actions \<Rightarrow> bool" where
  "lock_ok_las ls t las \<equiv> \<forall>l. lock_actions_ok (ls l) t (las l)"

lemma lock_ok_lasI:
  "(\<And>l. lock_actions_ok (ls l) t (las l)) \<Longrightarrow> lock_ok_las ls t las"
by(simp add: lock_ok_las_def)

lemma lock_ok_lasE:
  "\<lbrakk> lock_ok_las ls t las; (\<And>l. lock_actions_ok (ls l) t (las l)) \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(simp add: lock_ok_las_def)

lemma lock_ok_las_append [simp]:
  "lock_ok_las ls t (las @@ las') \<longleftrightarrow> lock_ok_las ls t las \<and> lock_ok_las (redT_updLs ls t las) t las'"
apply(auto simp add: lock_actions_append_def lock_ok_las_def redT_updLs_def)
done


lemma lock_actions_ok_Lock_may_lock:
  "\<lbrakk> lock_actions_ok l t Ls; Lock \<in> set Ls \<rbrakk> \<Longrightarrow> may_lock l t"
proof(induct Ls arbitrary: l)
  case Nil thus ?case by simp
next
  case (Cons L LS l)
  note IH = `\<And>l. \<lbrakk> lock_actions_ok l t LS; Lock \<in> set LS\<rbrakk> \<Longrightarrow> may_lock l t`
  note `lock_actions_ok l t (L # LS)`
  hence lao: "lock_action_ok l t L"
    and laos: "lock_actions_ok (upd_lock l t L) t LS" by auto
  note Lock = `Lock \<in> set (L # LS)`
  { assume L: "L = Lock"
    with lao have ?case by simp }
  moreover
  { assume Ls: "Lock \<in> set LS"
    with laos have "may_lock (upd_lock l t L) t" by(rule IH)
    with lao have ?case
      by(cases L, auto intro: has_lock_may_lock) }
  ultimately show ?case using Lock by auto
qed

lemma lock_ok_las_may_lock:
  "\<lbrakk> lock_ok_las ls t las; Lock \<in> set (las l) \<rbrakk> \<Longrightarrow> may_lock (ls l) t"
apply(erule lock_ok_lasE)
by(rule lock_actions_ok_Lock_may_lock)

lemma may_lock_lock_action_ok_may_lock_upd_lock:
  "\<lbrakk> may_lock l t; lock_action_ok l t L \<rbrakk> \<Longrightarrow> may_lock (upd_lock l t L) t"
apply(cases L, auto intro!: may_lockI elim!: may_lockE has_lockE)
apply(case_tac na, auto)
done

lemma may_lock_lock_actions_ok_may_lock_upd_locks:
  "\<lbrakk> may_lock l t; lock_actions_ok l t Ls \<rbrakk> \<Longrightarrow> may_lock (upd_locks l t Ls) t"
proof(induct Ls arbitrary: l)
  case Nil thus ?case by simp
next
  case (Cons L LS l)
  note IH = `\<And>l. \<lbrakk>may_lock l t; lock_actions_ok l t LS\<rbrakk> \<Longrightarrow> may_lock (upd_locks l t LS) t`
  note ml = `may_lock l t`
  note `lock_actions_ok l t (L # LS)`
  hence lao: "lock_action_ok l t L" and laos: "lock_actions_ok (upd_lock l t L) t LS" by auto
  from ml lao have "may_lock (upd_lock l t L) t"
    by(rule may_lock_lock_action_ok_may_lock_upd_lock)
  thus ?case
    by(auto intro: IH[OF _ laos])
qed

lemma redT_updLs_may_lock:
  "\<lbrakk> may_lock (ls l) t; lock_ok_las ls t las \<rbrakk> \<Longrightarrow> may_lock (redT_updLs ls t las l) t"
apply(unfold lock_ok_las_def redT_updLs_def)
apply(erule_tac x="l" in allE)
by(rule may_lock_lock_actions_ok_may_lock_upd_locks)

lemma lock_action_ok_has_locks_upd_lock_eq_has_locks:
  assumes tt': "t \<noteq> t'"
  and lao: "lock_action_ok l t' L"
  shows "has_locks (upd_lock l t' L) t n \<longleftrightarrow> has_locks l t n"
proof(cases L)
  case Lock
  with lao have mlt: "may_lock l t'" by(simp)
  have "has_locks (lock_lock l t') t n = has_locks l t n"
  proof(rule iffI)
    assume hlll: "has_locks (lock_lock l t') t n"
    note mlt
    thus "has_locks l t n"
    proof(rule may_lockE)
      assume lNone: "l = None"
      with hlll tt' have "n = 0" by(auto elim: has_locksE)
      thus ?thesis using tt' lNone by(auto intro!: has_locksI)
    next
      fix n''
      assume lSome: "l = \<lfloor>(t', n'')\<rfloor>"
      with hlll tt' have "n = 0" by(auto elim: has_locksE)
      thus ?thesis using lSome tt' by(auto intro!: has_locksI)
    qed
  next
    assume hl: "has_locks l t n"
    note mlt
    thus "has_locks (lock_lock l t') t n"
    proof(rule may_lockE)
      assume lNone: "l = None"
      with hl have "n = 0" by(auto elim: has_locksE)
      thus ?thesis using tt' lNone by(auto intro!: has_locksI)
    next
      fix n''
      assume lSome: "l = \<lfloor>(t', n'')\<rfloor>"
      with hl tt' have "n = 0" by(auto elim: has_locksE)
      thus ?thesis using lSome tt' by(auto intro!: has_locksI)
    qed
  qed
  with Lock show ?thesis by(simp)
next
  case Unlock
  with lao have mlt: "has_lock l t'" by(simp)
  then obtain n' where l: "l = \<lfloor>(t', n')\<rfloor>" by(erule has_lockE)
  with tt' have "has_locks (unlock_lock l) t n = has_locks l t n"
    by(cases n')(auto intro!: has_locksI elim!: has_locksE)
  with Unlock show ?thesis by simp
next
  case UnlockFail
  thus ?thesis by simp
qed

lemma lock_actions_ok_has_locks_upd_locks_eq_has_locks:
  assumes tt': "t \<noteq> t'"
  and lao: "lock_actions_ok l t' Ls"
  shows "has_locks (upd_locks l t' Ls) t = has_locks l t"
proof(rule ext)
  fix n
  from lao show "has_locks (upd_locks l t' Ls) t n = has_locks l t n"
  proof(induct Ls arbitrary: l)
    case Nil thus ?case by simp
  next
    case (Cons L LS l)
    note IH = `\<And>l. lock_actions_ok l t' LS \<Longrightarrow> has_locks (upd_locks l t' LS) t n = has_locks l t n`
    note `lock_actions_ok l t' (L # LS)`
    hence lao: "lock_action_ok l t' L" and laos: "lock_actions_ok (upd_lock l t' L) t' LS" by auto
    have "has_locks (upd_locks (upd_lock l t' L) t' LS) t n = has_locks (upd_lock l t' L) t n"
      by(rule IH[OF laos])
    also have "\<dots> = has_locks l t n"
      by(rule lock_action_ok_has_locks_upd_lock_eq_has_locks[OF tt' lao])
    finally show ?case by simp
  qed
qed

lemma redT_updLs_has_locks:
  "\<lbrakk> lock_ok_las ls t' las; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks (redT_updLs ls t' las l) t = has_locks (ls l) t"
apply(unfold lock_ok_las_def redT_updLs_def)
apply(erule_tac x="l" in allE)
by(rule lock_actions_ok_has_locks_upd_locks_eq_has_locks)

lemma has_locks_lock_actions_ok_replicate_Unlock:
  "has_locks l t n \<Longrightarrow> lock_actions_ok l t (replicate n Unlock)"
proof(induct n arbitrary: l)
  case 0 thus ?case by simp
next
  case (Suc n)
  note IH = `\<And>l. has_locks l t n \<Longrightarrow> lock_actions_ok l t (replicate n Unlock)`
  from `has_locks l t (Suc n)`
  have "has_lock l t"
    and "has_locks (unlock_lock l) t n"
    by(auto intro: has_locks_Suc_has_lock has_locks_Suc_unlock_lock_has_locks)
  thus ?case
    by(auto intro: IH)
qed


definition collect_locks :: "'l lock_actions \<Rightarrow> 'l set" where
  "collect_locks las = {l. Lock \<in> set (las l)}"

lemma collect_locksI:
  "Lock \<in> set (las l) \<Longrightarrow> l \<in> collect_locks las"
by(simp add: collect_locks_def)

lemma collect_locksE:
  "\<lbrakk> l \<in> collect_locks las; Lock \<in> set (las l) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(simp add: collect_locks_def)

lemma collect_locksD:
  "l \<in> collect_locks las \<Longrightarrow> Lock \<in> set (las l)"
apply(simp add: collect_locks_def)
done

fun must_acquire_lock :: "lock_action list \<Rightarrow> bool" where
  "must_acquire_lock [] = False"
| "must_acquire_lock (Lock # las) = True"
| "must_acquire_lock (Unlock # las) = False"
| "must_acquire_lock (_ # las) = must_acquire_lock las"

lemma must_acquire_lock_append:
  "must_acquire_lock (xs @ ys) \<longleftrightarrow> (if Lock \<in> set xs \<or> Unlock \<in> set xs then must_acquire_lock xs else must_acquire_lock ys)"
proof(induct xs)
  case Nil thus ?case by simp
next
  case (Cons L Ls)
  thus ?case by (cases L, simp_all)
qed

lemma must_acquire_lock_contains_lock:
  "must_acquire_lock las \<Longrightarrow> Lock \<in> set las"
apply(induct las)
 apply(simp)
apply(case_tac a, auto)
done

definition collect_locks' :: "'l lock_actions \<Rightarrow> 'l set" where
  "collect_locks' ls \<equiv> {l. must_acquire_lock (ls l)}"

lemma collect_locks'I:
  "must_acquire_lock (ls l) \<Longrightarrow> l \<in> collect_locks' ls"
apply(simp add: collect_locks'_def)
done

lemma collect_locks'E:
  "\<lbrakk> l \<in> collect_locks' ls; must_acquire_lock (ls l) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(simp add: collect_locks'_def)
done

lemma collect_locks'_subset_collect_locks:
  "collect_locks' las \<subseteq> collect_locks las"
by(auto simp add: collect_locks'_def collect_locks_def intro: must_acquire_lock_contains_lock)


definition lock_actions_ok' :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action list \<Rightarrow> bool" where
  "lock_actions_ok' l t las \<equiv> lock_actions_ok l t las \<or> (\<exists>xs ys. las = xs @ Lock # ys \<and> lock_actions_ok l t xs \<and> \<not> may_lock (upd_locks l t xs) t)"

definition lock_ok_las' :: "('l,'t) locks \<Rightarrow> 't \<Rightarrow> 'l lock_actions \<Rightarrow> bool" where
  "lock_ok_las' ls t las \<equiv> \<forall>l. lock_actions_ok' (ls l) t (las l)"

lemma lock_actions_ok'I:
  "lock_actions_ok l t las \<or> (\<exists>xs ys. las = xs @ Lock # ys \<and> lock_actions_ok l t xs \<and> \<not> may_lock (upd_locks l t xs) t) \<Longrightarrow> lock_actions_ok' l t las"
by(simp add: lock_actions_ok'_def)

lemma lock_actions_ok'E:
  "\<lbrakk> lock_actions_ok' l t las;
     lock_actions_ok l t las \<Longrightarrow> P;
     \<exists>xs ys. las = xs @ Lock # ys \<and> lock_actions_ok l t xs \<and> \<not> may_lock (upd_locks l t xs) t \<Longrightarrow> P \<rbrakk> 
  \<Longrightarrow> P"
by(auto simp add: lock_actions_ok'_def)

lemma not_lock_actions_ok'_conv: 
  "(\<not> lock_actions_ok' l t las) \<longleftrightarrow> \<not> lock_actions_ok l t las \<and> (\<forall>xs ys. las = xs @ Lock # ys \<and> lock_actions_ok l t xs \<longrightarrow> may_lock (upd_locks l t xs) t)"
by(auto simp add: lock_actions_ok'_def)

lemma not_lock_ok_las'_conv:
  "\<not> lock_ok_las' ls t las \<longleftrightarrow> (\<exists>l. \<not> lock_actions_ok' (ls l) t (las l))"
by(simp add: lock_ok_las'_def)


lemma lock_ok_las'_collect_locks'_may_lock:
  assumes lot': "lock_ok_las' ls t las"
  and mayl: "\<forall>l \<in> collect_locks' las. may_lock (ls l) t"
  shows "\<forall>l \<in> collect_locks las. may_lock (ls l) t"
proof
  fix l
  assume l: "l \<in> collect_locks las"
  show "may_lock (ls l) t"
  proof(cases "l \<in> collect_locks' las")
    case True
    thus ?thesis using mayl by auto
  next
    case False
    hence nmal: "\<not> must_acquire_lock (las l)"
      by(auto intro: collect_locks'I)
    from l have locklasl: "Lock \<in> set (las l)"
      by(rule collect_locksD)
    then obtain ys zs
      where las: "las l = ys @ Lock # zs"
      and notin: "Lock \<notin> set ys"
      by(auto dest: split_list_first)
    from lot' have "lock_actions_ok' (ls l) t (las l)"
      by(auto simp add: lock_ok_las'_def)
    thus ?thesis
    proof(rule lock_actions_ok'E)
      assume "lock_actions_ok (ls l) t (las l)"
      with locklasl show ?thesis
	by -(rule lock_actions_ok_Lock_may_lock)
    next
      assume "\<exists>xs ys. las l = xs @ Lock # ys \<and> lock_actions_ok (ls l) t xs \<and> \<not> may_lock (upd_locks (ls l) t xs) t"
      then obtain YS ZS
	where LAS: "las l = YS @ Lock # ZS"
	and lao: "lock_actions_ok (ls l) t YS"
	and nml: "\<not> may_lock (upd_locks (ls l) t YS) t"
	by blast
      from LAS las nmal notin have "Unlock \<in> set YS"
	apply -
	apply(erule contrapos_np)
	apply(auto simp add: must_acquire_lock_append append_eq_append_conv2 append_eq_Cons_conv)
	done
      then obtain ys' zs'
	where YS: "YS = ys' @ Unlock # zs'"
	and unlock: "Unlock \<notin> set ys'"
	by(auto dest: split_list_first)
      from YS las LAS lao have lao': "lock_actions_ok (ls l) t (ys' @ [Unlock])" by(auto)
      hence "has_lock (upd_locks (ls l) t ys') t" by simp
      hence "may_lock (upd_locks (ls l) t ys') t"
	by(rule has_lock_may_lock)
      moreover from lao' have "lock_actions_ok (ls l) t ys'" by simp
      ultimately show ?thesis
	by -(rule lock_actions_ok_may_lock_upd_locks_may_lock)
    qed
  qed
qed

lemma lock_actions_ok'_must_acquire_lock_lock_actions_ok:
  "\<lbrakk> lock_actions_ok' l t Ls; must_acquire_lock Ls \<longrightarrow> may_lock l t\<rbrakk> \<Longrightarrow> lock_actions_ok l t Ls"
proof(induct Ls arbitrary: l)
  case Nil thus ?case by(simp)
next
  case (Cons L LS l)
  note IH = `\<And>l. \<lbrakk>lock_actions_ok' l t LS; must_acquire_lock LS \<longrightarrow> may_lock l t\<rbrakk> \<Longrightarrow> lock_actions_ok l t LS`
  note laos' = `lock_actions_ok' l t (L # LS)`
  note malml = `must_acquire_lock (L # LS) \<longrightarrow> may_lock l t`
  show ?case
  proof(cases L)
    case Lock
    with malml have mll: "may_lock l t" by(simp)
    with Lock have "lock_action_ok l t L" by simp
    moreover
    with mll have "may_lock (upd_lock l t L) t"
      by(rule may_lock_lock_action_ok_may_lock_upd_lock)
    with laos' Lock mll have "lock_actions_ok (upd_lock l t L) t LS"
      apply -
      apply(rule IH)
      apply(auto simp add: lock_actions_ok'_def Cons_eq_append_conv)
      done
    ultimately show ?thesis by simp
  next
    case Unlock
    with laos' have hl: "has_lock l t"
      by(auto simp: lock_actions_ok'_def Cons_eq_append_conv)
    with Unlock have lao: "lock_action_ok l t L" by simp
    moreover
    from hl have mll: "may_lock l t" by(rule has_lock_may_lock)
    with lao have "may_lock (upd_lock l t L) t"
      by-(rule may_lock_lock_action_ok_may_lock_upd_lock)
    with laos' Unlock mll have "lock_actions_ok (upd_lock l t L) t LS"
      apply -
      apply(rule IH)
      apply(auto simp add: lock_actions_ok'_def Cons_eq_append_conv)
      done
    ultimately show ?thesis by simp
  next
    case UnlockFail
    with laos' have nhl: "\<not> has_lock l t"
      by(auto simp add: lock_actions_ok'_def Cons_eq_append_conv)
    from UnlockFail laos' have "lock_actions_ok' l t LS"
      by(auto simp add: lock_actions_ok'_def Cons_eq_append_conv)
    moreover
    from malml UnlockFail
    have "must_acquire_lock LS \<longrightarrow> may_lock l t" by simp
    ultimately have "lock_actions_ok l t LS" by(rule IH)
    with UnlockFail nhl show ?thesis by(simp)
  qed
qed

lemma lock_ok_las'_collect_locks_lock_ok_las:
  "\<lbrakk> lock_ok_las' ls t las; \<forall>l\<in> collect_locks las. may_lock (ls l) t \<rbrakk> \<Longrightarrow> lock_ok_las ls t las"
proof(rule lock_ok_lasI)
  fix l
  assume lol': "lock_ok_las' ls t las"
  assume ml: "\<forall>l\<in>collect_locks las. may_lock (ls l) t"
  from lol' have "lock_actions_ok' (ls l) t (las l)"
    by(auto simp add: lock_ok_las'_def)
  thus "lock_actions_ok (ls l) t (las l)"
  proof(rule lock_actions_ok'_must_acquire_lock_lock_actions_ok[OF _ impI])
    assume mal: "must_acquire_lock (las l)"
    with ml show "may_lock (ls l) t"
      by(auto dest!: bspec intro!: collect_locksI elim: must_acquire_lock_contains_lock)
  qed
qed


end
