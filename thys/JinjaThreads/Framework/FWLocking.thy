(*  Title:      JinjaThreads/Framework/FWLocking.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of the thread actions for locking} *}

theory FWLocking imports FWLock begin

definition redT_updLs :: "('l,'t) locks \<Rightarrow> 't \<Rightarrow> 'l lock_actions \<Rightarrow> ('l,'t) locks" where
  "redT_updLs ls t las \<equiv> (\<lambda>(l, la). upd_locks l t la) \<circ>\<^isub>f ((ls, las)\<^sup>f)"

lemma redT_updLs_iff [simp]: "(redT_updLs ls t las)\<^sub>f l = upd_locks (ls\<^sub>f l) t (las\<^sub>f l)"
by(simp add: redT_updLs_def)

lemma upd_locks_empty_conv [simp]: "(\<lambda>(l, las). upd_locks l t las) \<circ>\<^isub>f (ls, \<lambda>\<^isup>f [])\<^sup>f = ls"
by(auto intro: finfun_ext)

lemma redT_updLs_Some_thread_idD:
  "\<lbrakk> has_lock ((redT_updLs ls t las)\<^sub>f l) t'; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_lock (ls\<^sub>f l) t'"
by(auto simp add: redT_updLs_def intro: has_lock_upd_locks_implies_has_lock)

definition acquire_all :: "('l, 't) locks \<Rightarrow> 't \<Rightarrow> ('l \<Rightarrow>\<^isub>f nat) \<Rightarrow> ('l, 't) locks"
where "acquire_all ls t ln \<equiv> (\<lambda>(l, la). acquire_locks l t la) \<circ>\<^isub>f ((ls, ln)\<^sup>f)"

lemma acquire_all_iff [simp]: 
  "(acquire_all ls t ln)\<^sub>f l = acquire_locks (ls\<^sub>f l) t (ln\<^sub>f l)"
by(simp add: acquire_all_def)


definition lock_ok_las :: "('l,'t) locks \<Rightarrow> 't \<Rightarrow> 'l lock_actions \<Rightarrow> bool" where
  "lock_ok_las ls t las \<equiv> \<forall>l. lock_actions_ok (ls\<^sub>f l) t (las\<^sub>f l)"

lemma lock_ok_lasI [intro]:
  "(\<And>l. lock_actions_ok (ls\<^sub>f l) t (las\<^sub>f l)) \<Longrightarrow> lock_ok_las ls t las"
by(simp add: lock_ok_las_def)

lemma lock_ok_lasE:
  "\<lbrakk> lock_ok_las ls t las; (\<And>l. lock_actions_ok (ls\<^sub>f l) t (las\<^sub>f l)) \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(simp add: lock_ok_las_def)

lemma lock_ok_lasD:
  "lock_ok_las ls t las \<Longrightarrow> lock_actions_ok (ls\<^sub>f l) t (las\<^sub>f l)"
by(simp add: lock_ok_las_def)

lemma lock_ok_las_code [code]:
  "lock_ok_las ls t las = finfun_All ((\<lambda>(l, la). lock_actions_ok l t la) \<circ>\<^isub>f (ls, las)\<^sup>f)"
by(simp add: lock_ok_las_def finfun_All_All o_def)

lemma lock_ok_las_may_lock:
  "\<lbrakk> lock_ok_las ls t las; Lock \<in> set (las\<^sub>f l) \<rbrakk> \<Longrightarrow> may_lock (ls\<^sub>f l) t"
by(erule lock_ok_lasE)(rule lock_actions_ok_Lock_may_lock)

lemma redT_updLs_may_lock [simp]:
  "lock_ok_las ls t las \<Longrightarrow> may_lock ((redT_updLs ls t las)\<^sub>f l) t = may_lock (ls\<^sub>f l) t"
by(auto dest!: lock_ok_lasD[where l=l])

lemma redT_updLs_has_locks [simp]:
  "\<lbrakk> lock_ok_las ls t' las; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks ((redT_updLs ls t' las)\<^sub>f l) t = has_locks (ls\<^sub>f l) t"
by(auto dest!: lock_ok_lasD[where l=l])


definition may_acquire_all :: "('l, 't) locks \<Rightarrow> 't \<Rightarrow> ('l \<Rightarrow>\<^isub>f nat) \<Rightarrow> bool"
where "may_acquire_all ls t ln \<equiv> \<forall>l. ln\<^sub>f l > 0 \<longrightarrow> may_lock (ls\<^sub>f l) t"

lemma may_acquire_allI [intro]:
  "(\<And>l. ln\<^sub>f l > 0 \<Longrightarrow> may_lock (ls\<^sub>f l) t) \<Longrightarrow> may_acquire_all ls t ln"
by(simp add: may_acquire_all_def)

lemma may_acquire_allE:
  "\<lbrakk> may_acquire_all ls t ln; \<forall>l. ln\<^sub>f l > 0 \<longrightarrow> may_lock (ls\<^sub>f l) t \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto simp add: may_acquire_all_def)

lemma may_acquire_allD [dest]:
  "\<lbrakk> may_acquire_all ls t ln; ln\<^sub>f l > 0 \<rbrakk> \<Longrightarrow> may_lock (ls\<^sub>f l) t"
by(auto simp add: may_acquire_all_def)

lemma may_acquire_all_has_locks_acquire_locks [simp]:
  "\<lbrakk> may_acquire_all ls t ln; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks (acquire_locks (ls\<^sub>f l) t (ln\<^sub>f l)) t' = has_locks (ls\<^sub>f l) t'"
by(cases "ln\<^sub>f l > 0")(auto dest: may_acquire_allD)

lemma may_acquire_all_code [code]:
  "may_acquire_all ls t ln \<longleftrightarrow> finfun_All ((\<lambda>(lock, n). n > 0 \<longrightarrow> may_lock lock t) \<circ>\<^isub>f (ls, ln)\<^sup>f)"
by(auto simp add: may_acquire_all_def finfun_All_All o_def)

definition collect_locks :: "'l lock_actions \<Rightarrow> 'l set" where
  "collect_locks las = {l. Lock \<in> set (las\<^sub>f l)}"

lemma collect_locksI:
  "Lock \<in> set (las\<^sub>f l) \<Longrightarrow> l \<in> collect_locks las"
by(simp add: collect_locks_def)

lemma collect_locksE:
  "\<lbrakk> l \<in> collect_locks las; Lock \<in> set (las\<^sub>f l) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(simp add: collect_locks_def)

lemma collect_locksD:
  "l \<in> collect_locks las \<Longrightarrow> Lock \<in> set (las\<^sub>f l)"
by(simp add: collect_locks_def)


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

lemma must_acquire_lock_conv:
  "must_acquire_lock las = (case (filter (\<lambda>L. L = Lock \<or> L = Unlock) las) of [] \<Rightarrow> False | L#Ls \<Rightarrow> L = Lock)"
proof(induct las)
  case Nil thus ?case by simp
next
  case (Cons LA LAS) thus ?case
    by(cases LA, auto split: list.split_asm)
qed


definition collect_locks' :: "'l lock_actions \<Rightarrow> 'l set" where
  "collect_locks' las \<equiv> {l. must_acquire_lock (las\<^sub>f l)}"

lemma collect_locks'I:
  "must_acquire_lock (las\<^sub>f l) \<Longrightarrow> l \<in> collect_locks' las"
by(simp add: collect_locks'_def)

lemma collect_locks'E:
  "\<lbrakk> l \<in> collect_locks' las; must_acquire_lock (las\<^sub>f l) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(simp add: collect_locks'_def)

lemma collect_locks'_subset_collect_locks:
  "collect_locks' las \<subseteq> collect_locks las"
by(auto simp add: collect_locks'_def collect_locks_def intro: must_acquire_lock_contains_lock)

definition lock_ok_las' :: "('l,'t) locks \<Rightarrow> 't \<Rightarrow> 'l lock_actions \<Rightarrow> bool" where
  "lock_ok_las' ls t las \<equiv> \<forall>l. lock_actions_ok' (ls\<^sub>f l) t (las\<^sub>f l)"

lemma lock_ok_las'I: "(\<And>l. lock_actions_ok' (ls\<^sub>f l) t (las\<^sub>f l)) \<Longrightarrow> lock_ok_las' ls t las"
by(simp add: lock_ok_las'_def)

lemma lock_ok_las'D: "lock_ok_las' ls t las \<Longrightarrow> lock_actions_ok' (ls\<^sub>f l) t (las\<^sub>f l)"
by(simp add: lock_ok_las'_def)

lemma not_lock_ok_las'_conv:
  "\<not> lock_ok_las' ls t las \<longleftrightarrow> (\<exists>l. \<not> lock_actions_ok' (ls\<^sub>f l) t (las\<^sub>f l))"
by(simp add: lock_ok_las'_def)

lemma lock_ok_las'_code:
    "lock_ok_las' ls t las = finfun_All ((\<lambda>(l, la). lock_actions_ok' l t la) \<circ>\<^isub>f (ls, las)\<^sup>f)"
by(simp add: lock_ok_las'_def finfun_All_All o_def)


lemma lock_ok_las'_collect_locks'_may_lock:
  assumes lot': "lock_ok_las' ls t las"
  and mayl: "\<forall>l \<in> collect_locks' las. may_lock (ls\<^sub>f l) t"
  and l: "l \<in> collect_locks las"
  shows "may_lock (ls\<^sub>f l) t"
proof -
  show "may_lock (ls\<^sub>f l) t"
  proof(cases "l \<in> collect_locks' las")
    case True
    thus ?thesis using mayl by auto
  next
    case False
    hence nmal: "\<not> must_acquire_lock (las\<^sub>f l)"
      by(auto intro: collect_locks'I)
    from l have locklasl: "Lock \<in> set (las\<^sub>f l)"
      by(rule collect_locksD)
    then obtain ys zs
      where las: "las\<^sub>f l = ys @ Lock # zs"
      and notin: "Lock \<notin> set ys"
      by(auto dest: split_list_first)
    from lot' have "lock_actions_ok' (ls\<^sub>f l) t (las\<^sub>f l)"
      by(auto simp add: lock_ok_las'_def)
    thus ?thesis
    proof(induct rule: lock_actions_ok'E)
      case ok
      with locklasl show ?thesis
	by -(rule lock_actions_ok_Lock_may_lock)
    next
      case (Lock YS ZS)
      note LAS = `las\<^sub>f l = YS @ Lock # ZS`
      note lao = `lock_actions_ok (ls\<^sub>f l) t YS`
      note nml = `\<not> may_lock (upd_locks (ls\<^sub>f l) t YS) t`
      from LAS las nmal notin have "Unlock \<in> set YS"
	by -(erule contrapos_np, auto simp add: must_acquire_lock_append append_eq_append_conv2 append_eq_Cons_conv)
      then obtain ys' zs'
	where YS: "YS = ys' @ Unlock # zs'"
	and unlock: "Unlock \<notin> set ys'"
	by(auto dest: split_list_first)
      from YS las LAS lao have lao': "lock_actions_ok (ls\<^sub>f l) t (ys' @ [Unlock])" by(auto)
      hence "has_lock (upd_locks (ls\<^sub>f l) t ys') t" by simp
      hence "may_lock (upd_locks (ls\<^sub>f l) t ys') t"
	by(rule has_lock_may_lock)
      moreover from lao' have "lock_actions_ok (ls\<^sub>f l) t ys'" by simp
      ultimately show ?thesis by simp
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
    with mll have "may_lock (upd_lock l t L) t" by simp
    with laos' Lock mll have "lock_actions_ok (upd_lock l t L) t LS"
      by -(rule IH, auto simp add: lock_actions_ok'_iff Cons_eq_append_conv)
    ultimately show ?thesis by simp
  next
    case Unlock
    with laos' have hl: "has_lock l t"
      by(auto simp: lock_actions_ok'_iff Cons_eq_append_conv)
    with Unlock have lao: "lock_action_ok l t L" by simp
    moreover
    from hl have mll: "may_lock l t" by(rule has_lock_may_lock)
    with lao have "may_lock (upd_lock l t L) t" by simp
    with laos' Unlock mll have "lock_actions_ok (upd_lock l t L) t LS"
      by -(rule IH, auto simp add: lock_actions_ok'_iff Cons_eq_append_conv)
    ultimately show ?thesis by simp
  next
    case UnlockFail
    with laos' have nhl: "\<not> has_lock l t"
      by(auto simp add: lock_actions_ok'_iff Cons_eq_append_conv)
    from UnlockFail laos' have "lock_actions_ok' l t LS"
      by(auto simp add: lock_actions_ok'_iff Cons_eq_append_conv)
    moreover
    from malml UnlockFail
    have "must_acquire_lock LS \<longrightarrow> may_lock l t" by simp
    ultimately have "lock_actions_ok l t LS" by(rule IH)
    with UnlockFail nhl show ?thesis by(simp)
  next
    case ReleaseAcquire
    moreover with `lock_actions_ok' l t (L # LS)`
    have "lock_actions_ok' (release_all l t) t LS"
      by(auto simp add: lock_actions_ok'_iff Cons_eq_append_conv)
    moreover
    from ReleaseAcquire `must_acquire_lock (L # LS) \<longrightarrow> may_lock l t`
    have "must_acquire_lock LS \<longrightarrow> may_lock (release_all l t) t" by auto
    ultimately show ?thesis by(auto intro: IH)
  qed
qed

lemma lock_ok_las'_collect_locks_lock_ok_las:
  assumes lol': "lock_ok_las' ls t las"
  and clml: "\<And>l. l \<in> collect_locks las \<Longrightarrow> may_lock (ls\<^sub>f l) t"
  shows "lock_ok_las ls t las"
proof(rule lock_ok_lasI)
  fix l
  from lol' have "lock_actions_ok' (ls\<^sub>f l) t (las\<^sub>f l)" by(rule lock_ok_las'D)
  thus "lock_actions_ok (ls\<^sub>f l) t (las\<^sub>f l)"
  proof(rule lock_actions_ok'_must_acquire_lock_lock_actions_ok[OF _ impI])
    assume mal: "must_acquire_lock (las\<^sub>f l)"
    thus "may_lock (ls\<^sub>f l) t"
      by(auto intro!: clml collect_locksI elim: must_acquire_lock_contains_lock )
  qed
qed

lemma lock_ok_las'_into_lock_on_las:
  "\<lbrakk>lock_ok_las' ls t las; \<And>l. l \<in> collect_locks' las \<Longrightarrow> may_lock (ls\<^sub>f l) t\<rbrakk> \<Longrightarrow> lock_ok_las ls t las"
by (metis lock_ok_las'_collect_locks'_may_lock lock_ok_las'_collect_locks_lock_ok_las)

end
