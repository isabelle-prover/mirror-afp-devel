(*  Title:      JinjaThreads/Framework/FWThread.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of the thread actions for thread creation} *}

theory FWThread imports FWState begin

(* Abstractions for thread ids *)

inductive free_thread_id :: "('l,'t,'x) thread_info \<Rightarrow> 't \<Rightarrow> bool"
for ts :: "('l,'t,'x) thread_info" and t :: 't
where "ts t = None \<Longrightarrow> free_thread_id ts t"

declare free_thread_id.cases [elim]

lemma free_thread_id_iff: "free_thread_id ts t = (ts t = None)"
by(auto elim: free_thread_id.cases intro: free_thread_id.intros)

(* Update functions for the multithreaded state *)

fun redT_updT :: "('l,'t,'x) thread_info \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('l,'t,'x) thread_info"
where
  "redT_updT ts (NewThread t' x m) = ts(t' \<mapsto> (x, no_wait_locks))"
| "redT_updT ts _ = ts"

fun redT_updTs :: "('l,'t,'x) thread_info \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> ('l,'t,'x) thread_info"
where
  "redT_updTs ts [] = ts"
| "redT_updTs ts (ta#tas) = redT_updTs (redT_updT ts ta) tas"

lemma redT_updTs_append [simp]:
  "redT_updTs ts (tas @ tas') = redT_updTs (redT_updTs ts tas) tas'"
by(induct tas arbitrary: ts, auto)

lemma redT_updT_None: 
  "redT_updT ts ta t = None \<Longrightarrow> ts t = None"
by(cases ta, auto split: if_splits)

lemma redT_updTs_None: "redT_updTs ts tas t = None \<Longrightarrow> ts t = None"
by(induct tas arbitrary: ts, auto intro: redT_updT_None)

lemma redT_updT_Some1:
  "ts t = \<lfloor>xw\<rfloor> \<Longrightarrow> \<exists>xw. redT_updT ts ta t = \<lfloor>xw\<rfloor>"
by(cases ta, auto)

lemma redT_updTs_Some1:
  "ts t = \<lfloor>xw\<rfloor> \<Longrightarrow> \<exists>xw. redT_updTs ts tas t = \<lfloor>xw\<rfloor>"
proof(induct tas arbitrary: ts xw)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS XW)
  note IH = `\<And>ts xw. ts t = \<lfloor>xw\<rfloor> \<Longrightarrow> \<exists>xw. redT_updTs ts TAS t = \<lfloor>xw\<rfloor>`
  note TS = `TS t = \<lfloor>XW\<rfloor>`
  hence "\<exists>xw. redT_updT TS TA t = \<lfloor>xw\<rfloor>"
    by(rule redT_updT_Some1)
  then obtain xw where "redT_updT TS TA t = \<lfloor>xw\<rfloor>" by blast
  hence "\<exists>xw. redT_updTs (redT_updT TS TA) TAS t = \<lfloor>xw\<rfloor>"
    by(rule IH)
  thus ?case by(simp)
qed


(* Preconditions for thread creation actions *)

fun thread_ok :: "('l,'t,'x) thread_info \<Rightarrow> 'm \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> bool"
where
  "thread_ok ts m (NewThread t x m') = (free_thread_id ts t \<and> m = m')"
| "thread_ok ts m NewThreadFail = (\<not> (\<exists>t. free_thread_id ts t))"
| "thread_ok ts m (ThreadExists t) = (\<not> free_thread_id ts t)"

fun thread_oks :: "('l,'t,'x) thread_info \<Rightarrow> 'm \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> bool"
where
  "thread_oks ts m [] = True"
| "thread_oks ts m (ta#tas) = (thread_ok ts m ta \<and> thread_oks (redT_updT ts ta) m tas)"

lemma thread_oks_append [simp]:
  "thread_oks ts c (tas @ tas') = (thread_oks ts c tas \<and> thread_oks (redT_updTs ts tas) c tas')"
by(induct tas arbitrary: ts, auto)

lemma not_thread_oks_conv:
  "(\<not> thread_oks ts m tas) \<longleftrightarrow> (\<exists>xs ta ys. tas = xs @ ta # ys \<and> thread_oks ts m xs \<and> \<not> thread_ok (redT_updTs ts xs) m ta)"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS)
  note IH = `\<And>ts. (\<not> thread_oks ts m TAS) = (\<exists>xs ta ys. TAS = xs @ ta # ys \<and> thread_oks ts m xs \<and> \<not> thread_ok (redT_updTs ts xs) m ta)`
  show ?case
  proof(cases "thread_ok TS m TA")
    case True
    hence "(\<not> thread_oks TS m (TA # TAS)) = (\<not> thread_oks (redT_updT TS TA) m TAS)"
      by simp
    also note IH
    also have "(\<exists>xs ta ys. TAS = xs @ ta # ys \<and> thread_oks (redT_updT TS TA) m xs \<and> \<not> thread_ok (redT_updTs (redT_updT TS TA) xs) m ta) 
             = (\<exists>xs ta ys. TA # TAS = xs @ ta # ys \<and> thread_oks TS m xs \<and> \<not> thread_ok (redT_updTs TS xs) m ta)"
    proof(rule iffI)
      assume "\<exists>xs ta ys. TAS = xs @ ta # ys \<and> thread_oks (redT_updT TS TA) m xs \<and> \<not> thread_ok (redT_updTs (redT_updT TS TA) xs) m ta"
      then obtain xs ta ys
	where "TAS = xs @ ta # ys"
	and "thread_oks (redT_updT TS TA) m xs"
	and "\<not> thread_ok (redT_updTs (redT_updT TS TA) xs) m ta" by blast
      with True have "TA # TAS = (TA # xs) @ ta # ys"
	and "thread_oks TS m (TA # xs)"
	and "\<not> thread_ok (redT_updTs TS (TA # xs)) m ta"
	by(auto)
      thus "\<exists>xs ta ys. TA # TAS = xs @ ta # ys \<and> thread_oks TS m xs \<and> \<not> thread_ok (redT_updTs TS xs) m ta" by blast
    next
      assume "\<exists>xs ta ys. TA # TAS = xs @ ta # ys \<and> thread_oks TS m xs \<and> \<not> thread_ok (redT_updTs TS xs) m ta"
      then obtain xs ta ys
	where "TA # TAS = xs @ ta # ys"
	and "thread_oks TS m xs"
	and "\<not> thread_ok (redT_updTs TS xs) m ta" by blast
      moreover
      with True have "xs \<noteq> []" by(auto)
      then obtain la' xs' where "xs = la' # xs'" by(cases xs, auto)
      ultimately
      have "TAS = xs' @ ta # ys"
	and "thread_oks (redT_updT TS TA) m xs'"
	and "\<not> thread_ok (redT_updTs (redT_updT TS TA) xs') m ta"
	by(auto)
      thus "\<exists>xs ta ys. TAS = xs @ ta # ys \<and> thread_oks (redT_updT TS TA) m xs \<and> \<not> thread_ok (redT_updTs (redT_updT TS TA) xs) m ta" by blast
    qed
    finally show ?thesis .
  next
    case False
    thus ?thesis
      by(fastsimp)
  qed
qed


lemma redT_updT_Some:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_ok ts m ta \<rbrakk> \<Longrightarrow> redT_updT ts ta t = \<lfloor>xw\<rfloor>"
by(cases ta, auto)

lemma redT_updTs_Some:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_oks ts m tas \<rbrakk> \<Longrightarrow> redT_updTs ts tas t = \<lfloor>xw\<rfloor>"
apply(induct tas arbitrary: ts)
by(auto intro: redT_updT_Some)


lemma thread_ok_new_thread:
  "thread_ok ts m (NewThread t m' x) \<Longrightarrow> ts t = None"
by(auto)

lemma thread_oks_new_thread:
  "\<lbrakk> thread_oks ts m tas; NewThread t m' x \<in> set tas \<rbrakk> \<Longrightarrow> ts t = None"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS)
  note IH = `\<And>ts. \<lbrakk>thread_oks ts m TAS; NewThread t m' x \<in> set TAS\<rbrakk> \<Longrightarrow> ts t = None`
  note cct = `thread_oks TS m (TA # TAS)`
  note nt = `NewThread t m' x \<in> set (TA # TAS)`
  { assume "NewThread t m' x = TA"
    with cct have ?case
      by(auto intro: thread_ok_new_thread) }
  moreover
  { assume "NewThread t m' x \<in> set TAS"
    with cct have "redT_updT TS TA t = None"
      by(auto intro!: IH)
    with cct have ?case
      by(auto intro: redT_updT_None) }
  ultimately show ?case using nt by(auto)
qed


lemma redT_updT_new_thread_ts:
  "thread_ok ts c (NewThread t x m) \<Longrightarrow> redT_updT ts (NewThread t x m) t = \<lfloor>(x, no_wait_locks)\<rfloor>"
by(simp)

lemma redT_updTs_new_thread_ts:
  "\<lbrakk> thread_oks ts m tas; NewThread t x m' \<in> set tas \<rbrakk> \<Longrightarrow> redT_updTs ts tas t = \<lfloor>(x, no_wait_locks)\<rfloor>"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS)
  note IH = `\<And>ts. \<lbrakk>thread_oks ts m TAS; NewThread t x m' \<in> set TAS\<rbrakk> \<Longrightarrow> redT_updTs ts TAS t = \<lfloor>(x, no_wait_locks)\<rfloor>`
  note cct = `thread_oks TS m (TA # TAS)`
  note nt = `NewThread t x m' \<in> set (TA # TAS)`
  { assume "NewThread t x m' = TA"
    with cct have ?case 
      by(auto intro: redT_updTs_Some) }
  moreover
  { assume "NewThread t x m' \<in> set TAS"
    with cct have ?case
      by(auto intro: IH) }
  ultimately show ?case using nt by(auto)
qed


lemma redT_updT_new_thread:
  "\<lbrakk> redT_updT ts ta t = \<lfloor>(x, w)\<rfloor>; thread_ok ts m ta; ts t = None \<rbrakk> \<Longrightarrow> ta = NewThread t x m \<and> w = no_wait_locks"
by(cases ta, auto split: split_if_asm)

lemma redT_updTs_new_thread:
  "\<lbrakk> redT_updTs ts tas t = \<lfloor>(x, w)\<rfloor>; thread_oks ts m tas; ts t = None \<rbrakk> 
  \<Longrightarrow> NewThread t x m \<in> set tas \<and> w = no_wait_locks"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS)
  note IH = `\<And>ts. \<lbrakk>redT_updTs ts TAS t = \<lfloor>(x, w)\<rfloor>; thread_oks ts m TAS; ts t = None\<rbrakk> \<Longrightarrow> NewThread t x m \<in> set TAS \<and> w = no_wait_locks`
  note es't = `redT_updTs TS (TA # TAS) t = \<lfloor>(x, w)\<rfloor>`
  note cct = `thread_oks TS m (TA # TAS)`
  hence cctta: "thread_ok TS m TA" and ccts: "thread_oks (redT_updT TS TA) m TAS" by auto
  note est = `TS t = None`
  { fix X W
    assume rest: "redT_updT TS TA t = \<lfloor>(X, W)\<rfloor>"
    hence "TA = NewThread t X m \<and> W = no_wait_locks" using cctta est
      by -(rule redT_updT_new_thread)
    then obtain "TA = NewThread t X m" "W = no_wait_locks" ..
    moreover from rest ccts
    have "redT_updTs TS (TA # TAS) t = \<lfloor>(X, W)\<rfloor>" 
      by(auto intro:redT_updTs_Some)
    with es't have "X = x" "W = w" by auto
    ultimately have ?case by simp }
  moreover
  { assume rest: "redT_updT TS TA t = None"
    hence "TA \<noteq> NewThread t x m" using est cct
      by(clarsimp)
    with rest ccts es't have ?case by(simp)(erule IH) }
  ultimately show ?case by(cases "redT_updT TS TA t", auto)
qed

lemma redT_updT_upd:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_ok ts m ta \<rbrakk> \<Longrightarrow> redT_updT ts ta(t \<mapsto> xw') = redT_updT (ts(t \<mapsto> xw')) ta"
apply(cases ta)
by(fastsimp intro: fun_upd_twist)+

lemma redT_updTs_upd:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_oks ts m tas \<rbrakk> \<Longrightarrow> redT_updTs ts tas(t \<mapsto> xw') = redT_updTs (ts(t \<mapsto> xw')) tas"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS)
  note est = `TS t = \<lfloor>xw\<rfloor>`
  note cct = `thread_oks TS m (TA # TAS)`
  note IH = `\<And>ts. \<lbrakk>ts t = \<lfloor>xw\<rfloor>; thread_oks ts m TAS\<rbrakk> \<Longrightarrow> redT_updTs ts TAS(t \<mapsto> xw') = redT_updTs (ts(t \<mapsto> xw')) TAS`
  from cct have cctta: "thread_ok TS m TA"
    and ccts: "thread_oks (redT_updT TS TA) m TAS" by auto
  have "redT_updT TS TA t = \<lfloor>xw\<rfloor>" by(rule redT_updT_Some[OF est cctta])
  hence "redT_updTs (redT_updT TS TA) TAS(t \<mapsto> xw') = redT_updTs (redT_updT TS TA(t \<mapsto> xw')) TAS" by(rule IH[OF _ ccts])
  thus ?case by(simp del: fun_upd_apply add: redT_updT_upd[OF est cctta, THEN sym])
qed

lemma thread_oks_commonD:
 "\<lbrakk> thread_oks ts m tas; NewThread t x m' \<in> set tas \<rbrakk> \<Longrightarrow> m = m'"
by(induct tas arbitrary: ts, auto)

lemma thread_oks_newThread_unique:
  "\<lbrakk> thread_oks ts m tas; NewThread t x m' \<in> set tas \<rbrakk> \<Longrightarrow> \<exists>!n. n < length tas \<and> (\<exists>x' m'. tas ! n = NewThread t x' m')"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS)
  note IH = `\<And>ts. \<lbrakk>thread_oks ts m TAS; NewThread t x m' \<in> set TAS\<rbrakk> \<Longrightarrow> \<exists>!n. n < length TAS \<and> (\<exists>x' m'. TAS ! n = NewThread t x' m')`
  note cct = `thread_oks TS m (TA # TAS)`
  note nt = `NewThread t x m' \<in> set (TA # TAS)`
  show ?case
  proof(cases "TA = NewThread t x m'")
    case True
    show ?thesis
    proof(rule ex1I)
      show "0 < length (TA # TAS) \<and> (\<exists>x' m'. (TA # TAS) ! 0 = NewThread t x' m')"
	using True by(auto)
    next
      fix n
      assume "n < length (TA # TAS) \<and> (\<exists>x' m'. (TA # TAS) ! n = NewThread t x' m')"
      hence nlen: "n < length (TA # TAS)"
	and nnt: "\<exists>m' x'. (TA # TAS) ! n = NewThread t x' m'" by auto
      { assume n0: "0 < n"
	with nnt have "\<exists>x' m'. TAS ! (n - 1) = NewThread t x' m'"
	  by(cases n, auto)
	then obtain m' x'
	  where "TAS ! (n - 1) = NewThread t x' m'" by blast
	moreover
	from n0 nlen have "TAS ! (n - 1) \<in> set TAS"
	  by -(rule nth_mem, simp)
	ultimately have "NewThread t x' m' \<in> set TAS" by simp
	with cct have "redT_updT TS TA t = None"
	  by(auto intro: thread_oks_new_thread)
	with True cct have False by(simp) }
      thus "n = 0" by auto
    qed
  next
    case False
    hence "NewThread t x m' \<in> set TAS" using nt by simp
    with cct have "\<exists>!n. n < length TAS \<and> (\<exists>x' m'. TAS ! n = NewThread t x' m')"
      apply(clarsimp)
      by(rule IH)
    then obtain n
      where nl: "n < length TAS"
      and exe'x': "\<exists>x' m'. TAS ! n = NewThread t x' m'"
      and unique: "\<forall>n'. n' < length TAS \<and> (\<exists>x' m'. TAS ! n' = NewThread t x' m') \<longrightarrow> n' = n"
      by(blast elim: ex1E)
    then obtain m' x' where e'x': "TAS ! n = NewThread t x' m'" by blast
    moreover
    with nl have "TAS ! n \<in> set TAS" by -(rule nth_mem)
    ultimately have nset: "NewThread t x' m' \<in> set TAS" by simp
    with cct have es't: "redT_updT TS TA t = None"
      apply(clarsimp) 
      by(erule thread_oks_new_thread)
    show ?thesis
    proof(rule ex1I)
      show "Suc n < length (TA # TAS) \<and> (\<exists>x' m'. (TA # TAS) ! Suc n = NewThread t x' m')"
	using nl exe'x' by auto
    next
      fix n'
      assume "n' < length (TA # TAS) \<and> (\<exists>x' m'. (TA # TAS) ! n' = NewThread t x' m')"
      hence n'l: "n' < length (TA # TAS)"
	and ex'e'x': "\<exists>x' m'. (TA # TAS) ! n' = NewThread t x' m'" by auto
      from ex'e'x' obtain m'' x''
	where e''x'': "(TA # TAS) ! n' = NewThread t x'' m''" by blast
      { assume "n' = 0"
	with es't e''x'' cct have False by(auto simp add: free_thread_id_def) }
      hence n'0: "n' > 0" by auto
      hence "TAS ! (n' - 1) = NewThread t x'' m''" using e''x'' 
	by(cases n', auto)
      moreover
      from n'0 unique have un': "n' - 1 < length TAS \<and> (\<exists>x' m'. TAS ! (n' - 1) = NewThread t x' m') \<Longrightarrow> n' - 1 = n"
	by(auto intro: unique)
      ultimately have "n' - 1 = n" using n'l e''x'' n'0
	apply -
	apply(rule un')
	by(cases n', simp_all)
      thus "n' = Suc n" using n'0 by arith
    qed
  qed
qed



end
