(*  Title:      JinjaThreads/J/Threaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Multithreaded setup for small-step semantics} *}

theory Threaded imports SmallStep "../Framework/FWLiftingSem" WWellForm begin

abbreviation
  mred :: "J_prog \<Rightarrow> (((expr \<times> locals) \<times> heap) \<times> (addr,thread_id,expr \<times> locals,heap,addr) thread_action \<times> (expr \<times> locals) \<times> heap) set"
where
  "mred P \<equiv> {(((e, l), h), ta, (e', l'), h'). P \<turnstile> \<langle>e, (h, l)\<rangle> -ta\<rightarrow> \<langle>e', (h', l')\<rangle>}"


interpretation red_mthr: multithreaded["mred P"] .

abbreviation
  mredT :: "J_prog \<Rightarrow> ((addr,thread_id,expr \<times> locals,heap,addr) state \<times> (thread_id \<times> (addr,thread_id,expr \<times> locals,heap,addr) thread_action) \<times> (addr,thread_id,expr \<times> locals,heap,addr) state) set"
where
  "mredT P \<equiv> multithreaded.redT (mred P)"

abbreviation
  mredT_syntax1 :: "J_prog \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state
                  \<Rightarrow> thread_id \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) thread_action
                  \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -_\<triangleright>_\<rightarrow> _" [50,0,0,0,50] 80)
where
  "mredT_syntax1 P s t ta s' \<equiv> (s, (t, ta), s') \<in> mredT P"

abbreviation
  mredT_syntax2 :: "J_prog \<Rightarrow> (addr,thread_id) locks \<Rightarrow> (thread_id,expr \<times> locals) thread_info \<times> heap \<Rightarrow> (addr,thread_id) wait_sets
                  \<Rightarrow> thread_id \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) thread_action
                  \<Rightarrow> (addr,thread_id) locks \<Rightarrow> (thread_id,expr \<times> locals) thread_info \<times> heap \<Rightarrow> (addr,thread_id) wait_sets \<Rightarrow> bool"
                    ("_ \<turnstile> \<langle>_, _, _\<rangle> -_\<triangleright>_\<rightarrow> \<langle>_, _, _\<rangle>" [50,0,0,0,0,0,0,0,0] 80)
where
  "P \<turnstile> \<langle>ls, tsm, ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', tsm', ws'\<rangle> \<equiv> P \<turnstile> (ls, tsm, ws) -t\<triangleright>ta\<rightarrow> (ls', tsm', ws')"


abbreviation
  mRedT_syntax1 :: "J_prog \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state
                  \<Rightarrow> (thread_id \<times> (addr,thread_id,expr \<times> locals,heap,addr) thread_action) list
                  \<Rightarrow> (addr,thread_id,expr \<times> locals,heap,addr) state \<Rightarrow> bool"
                    ("_ \<turnstile> _ -\<triangleright>_\<rightarrow>* _" [50,0,0,50] 80)
where
  "P \<turnstile> s -\<triangleright>ttas\<rightarrow>* s' \<equiv> (s, ttas, s') \<in> multithreaded.RedT (mred P)"

abbreviation
  mRedT_syntax2 :: "J_prog \<Rightarrow> (addr,thread_id) locks \<Rightarrow> (thread_id,expr \<times> locals) thread_info \<times> heap \<Rightarrow> (addr,thread_id) wait_sets
                  \<Rightarrow> (thread_id \<times> (addr,thread_id,expr \<times> locals,heap,addr) thread_action) list
                  \<Rightarrow> (addr,thread_id) locks \<Rightarrow> (thread_id,expr \<times> locals) thread_info \<times> heap \<Rightarrow> (addr,thread_id) wait_sets \<Rightarrow> bool"
                    ("_ \<turnstile> \<langle>_, _, _\<rangle> -\<triangleright>_\<rightarrow>* \<langle>_, _, _\<rangle>" [50,0,0,0,0,0,0,0] 80)
where
  "P \<turnstile> \<langle>ls, tsm, ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', tsm', ws'\<rangle> \<equiv> P \<turnstile> (ls, tsm, ws) -\<triangleright>ttas\<rightarrow>* (ls', tsm', ws')"



lemma redT_hext_incr:
  "P \<turnstile> \<langle>ls, (ts, m), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', m'), ws'\<rangle> \<Longrightarrow> hext m m'"
by(erule multithreaded.redT.cases, auto intro: red_hext_incr)



definition is_val :: "expr \<Rightarrow> bool" where
  "is_val e \<equiv> \<exists>v. e = Val v"

declare is_val_def[simp]

lemma red_no_val:
  "P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> \<not> is_val e"
by(clarsimp)


function addr_ok :: "expr \<Rightarrow> bool"
  and addr_oks :: "expr list \<Rightarrow> bool"
where
  "addr_ok (new C) = True"
| "addr_ok (newA T\<lfloor>i\<rceil>) = addr_ok i"
| "addr_ok (Cast T e) = addr_ok e"
| "addr_ok (Val v) = True"
| "addr_ok (Var v) = True"
| "addr_ok (e \<guillemotleft>bop\<guillemotright> e') = (addr_ok e \<and> addr_ok e' \<and> (contains_addr e' \<longrightarrow> is_val e))"
| "addr_ok (V := e) = addr_ok e"
| "addr_ok (a\<lfloor>i\<rceil>) = (addr_ok a \<and> addr_ok i \<and> (contains_addr i \<longrightarrow> is_val a))"
| "addr_ok (a\<lfloor>i\<rceil> := e) = (addr_ok a \<and> addr_ok i \<and> addr_ok e \<and> (contains_addr i \<longrightarrow> is_val a) \<and> (contains_addr e \<longrightarrow> is_val a \<and> is_val i))"
| "addr_ok (e\<bullet>F{D}) = addr_ok e"
| "addr_ok (e\<bullet>F{D} := e') = (addr_ok e \<and> addr_ok e' \<and> (contains_addr e' \<longrightarrow> is_val e))"
| "addr_ok (e\<bullet>m(pns)) = (addr_ok e \<and> addr_oks pns \<and> (contains_addrs pns \<longrightarrow> is_val e))"
| "addr_ok ({V : T; e}) = addr_ok e"
| "addr_ok (sync(o') e) = ((case o' of (e;;e') \<Rightarrow> contains_addr e' \<longrightarrow> lock_granted(o') | _ \<Rightarrow> True)
                         \<and> addr_ok o' \<and> addr_ok e \<and> (contains_addr e \<longrightarrow> lock_granted(o') \<or> (\<exists>a. o' = addr a)))"
| "addr_ok (e;;e') = (addr_ok e \<and> addr_ok e' \<and> (contains_addr e' \<longrightarrow> is_val e \<or> (\<exists>V v. e = V := Val v)))"
| "addr_ok (if (b) e else e') = (addr_ok b \<and> \<not> contains_addr e \<and> \<not> contains_addr e')"
| "addr_ok (while (b) e) = (\<not> contains_addr b \<and> \<not> contains_addr e)"
| "addr_ok (throw e) = addr_ok e"
| "addr_ok (try e catch(C v) e') = (addr_ok e \<and> \<not> contains_addr e')"
| "addr_oks [] = True"
| "addr_oks (x # xs) = (addr_ok x \<and> addr_oks xs \<and> (contains_addrs xs \<longrightarrow> is_val x))"
by pat_completeness auto
termination proof
  show "wf (measure (\<lambda>x. case x of Inl n \<Rightarrow> Suc (size n) | Inr n \<Rightarrow> Suc (listsum (map (Suc \<circ> size) n))))"
    by auto
next prefer 15
  fix e m pns
  show "(Inr pns, Inl (e\<bullet>m(pns))) \<in> measure (sum.sum_case (\<lambda>n. Suc (size n)) (\<lambda>n. Suc (listsum (map (Suc \<circ> size) n))))"
    by(induct pns, auto)
qed(auto)

lemma addr_oks_append [simp]: "addr_oks (es @ fs) = (addr_oks es \<and> addr_oks fs \<and> (contains_addrs fs \<longrightarrow> (\<exists>vs. es = map Val vs)))"
apply(induct es)
 apply(simp)
apply(rule iffI)
 apply(clarsimp)
 apply(rule_tac x="v # vs" in exI) 
 apply(simp)
by(auto)

lemma contains_addr_addr_ok: "\<not> contains_addr e \<Longrightarrow> addr_ok e"
  and contains_addrs_addr_oks: "\<not> contains_addrs es \<Longrightarrow> addr_oks es"
apply(induct e and es)
apply(auto)
apply(case_tac exp1)
apply(auto)
done

lemma addr_ok_blocks: "\<lbrakk> \<not> contains_addr e; length vs = length pns; length Ts = length pns \<rbrakk> \<Longrightarrow> addr_ok (blocks (pns, Ts, vs, e))"
apply(induct pns Ts vs e rule:blocks.induct)
apply(auto simp add: assigned_def intro: contains_addr_addr_ok)
done

lemma addr_ok_red_no_lock: 
  "\<lbrakk> P \<turnstile> \<langle>o', s\<rangle> -tas\<rightarrow> \<langle>o'', s'\<rangle>; addr_ok (sync(o') e) \<rbrakk> \<Longrightarrow> \<not> lock_granted o''"
apply(erule red.cases)
apply(fastsimp simp add: lock_granted_def)+
done

inductive_cases seq_cases: "P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow> \<langle>e';; e'', s'\<rangle>"
inductive_cases if_cases: "P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow> \<langle>if (b) e' else e'', s'\<rangle>"

lemma red_preserve_addr_ok:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -tas\<rightarrow> \<langle>e', s'\<rangle>; addr_ok e; wwf_J_prog P \<rbrakk> \<Longrightarrow> addr_ok e'"
proof(induct rule:red.induct)
  case RedCall thus ?case by(auto dest: sees_wf_mdecl simp add: wf_mdecl_def intro!: addr_ok_blocks)
next
  case (SynchronizedRed1 O' S TA O'' S' E) thus ?case
    by(cases O'')(fastsimp elim: seq_cases if_cases simp add: lock_granted_def)+
next
  case SeqRed thus ?case by(fastsimp elim: red_cases)
qed(fastsimp dest:contains_addr_addr_ok simp add: lock_granted_def)+

lemma red_new_thread_no_addr:
  "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; addr_ok e; NewThread t'' (e'', x'') h'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk> \<Longrightarrow> \<not> contains_addr e''"
apply(induct rule: red.induct)
apply(auto dest: expr_locks_contains_addr)
done

abbreviation
  addr_es_ok :: "(thread_id,expr\<times>locals) thread_info \<Rightarrow> heap \<Rightarrow> bool"
where
  "addr_es_ok \<equiv> ts_ok (\<lambda>(e, x) m. addr_ok e)"

lemma addr_es_ok_indep_c:
  "addr_es_ok es c = addr_es_ok es c'"
apply(auto intro!: ts_okI elim: ts_okE)
done

lemma lifting_wf_addr_ok: "wwf_J_prog P \<Longrightarrow> lifting_wf (mred P) (\<lambda>(e, x) m. addr_ok e)"
apply(unfold_locales)
by(auto intro: red_preserve_addr_ok red_new_thread_no_addr[THEN contains_addr_addr_ok])

lemma redT_preserve_addr_ok:
  assumes red: "P \<turnstile> \<langle>ls, (ts, h), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', h'), ws'\<rangle>"
  shows "\<lbrakk> wwf_J_prog P; addr_es_ok ts h \<rbrakk> \<Longrightarrow> addr_es_ok ts' h'"
by(rule lifting_wf.redT_preserves[OF lifting_wf_addr_ok red])

fun upd_expr_lock_delta :: "lock_action \<Rightarrow> int"
where
  "upd_expr_lock_delta Lock = 1"
| "upd_expr_lock_delta Unlock = -1"
| "upd_expr_lock_delta UnlockFail = 0"

definition upd_expr_locks_delta :: "lock_action list \<Rightarrow> int"
where
  "upd_expr_locks_delta LS \<equiv> listsum (map upd_expr_lock_delta LS)"

lemma upd_expr_locks_delta_Cons [simp]:
  "upd_expr_locks_delta (L # Ls) = upd_expr_lock_delta L + upd_expr_locks_delta Ls"
by(simp add: upd_expr_locks_delta_def)

lemma upd_expr_locks_delta_append [simp]:
  "upd_expr_locks_delta (Ls @ Ls') = upd_expr_locks_delta Ls + upd_expr_locks_delta Ls'"
apply(induct Ls)
apply(auto simp add: upd_expr_locks_delta_def)
done

definition upd_expr_lock :: "int \<Rightarrow> lock_action list \<Rightarrow> int" where
  "upd_expr_lock el Ls \<equiv> el + (upd_expr_locks_delta Ls)"

declare upd_expr_lock_def[simp]

definition upd_expr_locks :: "(addr \<Rightarrow> int) \<Rightarrow> addr lock_actions \<Rightarrow> addr \<Rightarrow> int"
where
  "upd_expr_locks els las \<equiv> \<lambda>l. upd_expr_lock (els l) (las l)"

lemma lock_actions_append_l [simp]: (* Move to FWState *)
  "(las @@ las') l = las l @ las' l"
by(simp add: lock_actions_append_def)

lemma upd_expr_locks_append [simp]:
  "upd_expr_locks els (las @@ las') = upd_expr_locks (upd_expr_locks els las) las'"
by(auto simp add: upd_expr_locks_def intro!: ext)


fun upd_expr_lockss :: "(addr \<Rightarrow> int) \<Rightarrow> addr lock_actions list \<Rightarrow> addr \<Rightarrow> int" where
  "upd_expr_lockss els [] = els"
| "upd_expr_lockss els (las#lass) = upd_expr_lockss (upd_expr_locks els las) lass"

lemma upd_expr_lockss_append [simp]:
  "upd_expr_lockss els (lass @ lass') = upd_expr_lockss (upd_expr_lockss els lass) lass'"
apply(induct lass arbitrary: els)
apply(auto)
done

lemma upd_expr_locks_cong:
  "els a = els' a \<Longrightarrow> upd_expr_locks els ta a = upd_expr_locks els' ta a"
by(auto simp add: upd_expr_locks_def)

lemma upd_expr_lockss_cong:
  "els a = els' a \<Longrightarrow> upd_expr_lockss els lass a = upd_expr_lockss els' lass a"
proof(induct lass arbitrary: els els')
  case Nil thus ?case by simp
next
  case (Cons LAS LASS ELS ELS')
  note IH = `\<And>els els'. els a = els' a \<Longrightarrow> upd_expr_lockss els LASS a = upd_expr_lockss els' LASS a`
  note a = `ELS a = ELS' a`
  hence "upd_expr_locks ELS LAS a = upd_expr_locks ELS' LAS a"
    by(rule upd_expr_locks_cong)
  hence "upd_expr_lockss (upd_expr_locks ELS LAS) LASS a = upd_expr_lockss (upd_expr_locks ELS' LAS) LASS a"
    by(rule IH)
  thus ?case by simp
qed

lemma upd_expr_locks_add:
  "upd_expr_locks (\<lambda>a. x a + els a) las = (\<lambda>a. x a + upd_expr_locks els las a)"
apply(auto intro: ext simp: upd_expr_locks_def)
done

lemma upd_expr_lockss_add:
  "upd_expr_lockss (\<lambda>a. x a + els a) lass = (\<lambda>a. x a + upd_expr_lockss els lass a)"
proof(induct lass arbitrary: els)
  case Nil thus ?case by simp
next
  case (Cons LAS LASS ELS)
  note IH = `\<And>els. upd_expr_lockss (\<lambda>a. x a + els a) LASS = (\<lambda>a. x a + upd_expr_lockss els LASS a)`
  show ?case
    apply(simp)
    apply(unfold upd_expr_locks_add)
    apply(unfold IH)
    apply(simp)
    done
qed

lemma red_update_expr_locks:
  assumes wwf: "wwf_J_prog P"
  shows "\<lbrakk> P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; addr_ok e \<rbrakk> \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"
proof(induct rule: red.induct)
  prefer 37
  case (RedCall s a C fs M Ts T pns body D vs)
  note vspns = `length vs = length pns`
  note Tspns = `length Ts = length pns`
  note sees = `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
  note sees_wf_mdecl[OF wwf sees]
  hence "\<not> contains_addr body"
    by(clarsimp simp add: wf_mdecl_def)
  thus ?case
    by(auto simp add: upd_expr_locks_def upd_expr_locks_delta_def intro!: ext expr_locks_blocks[OF _ vspns Tspns])
next prefer 51
  case (SynchronizedRed1 o' s ta o'' s' e)
  note red = `P \<turnstile> \<langle>o',s\<rangle> -ta\<rightarrow> \<langle>o'',s'\<rangle>`
  note IH = `addr_ok o' \<Longrightarrow> upd_expr_locks (int \<circ> expr_locks o') \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks o''`
  note nlg = `\<not> lock_granted o'`
  note aoe = `addr_ok (sync(o') e)`
  from red nlg aoe have "\<not> lock_granted o''"
    by - (rule addr_ok_red_no_lock)
  moreover
  from aoe IH have IH': "upd_expr_locks (int \<circ> expr_locks o') \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks o''" by simp
  from red have "\<not> is_val o'" by auto
  hence "\<not> contains_addr e" using aoe nlg by(auto)
  ultimately show ?case using nlg
    apply -
    apply(rule ext)
    apply(simp add: lock_granted_def del: o_apply)
    by(simp add: IH'[THEN sym] contains_addr_expr_locks del: o_apply)
next prefer 51
  case (SynchronizedNull e s)
  thus ?case
    by(auto intro: ext simp add: lock_granted_def contains_addr_expr_locks upd_expr_locks_def upd_expr_locks_delta_def)
next prefer 52
  case (SynchronizedRed2 e s ta e' s' a)
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `addr_ok e \<Longrightarrow> upd_expr_locks (int \<circ> expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'`
  note aoe = `addr_ok (sync(locked(a)) e)`
  from IH aoe have IH': "upd_expr_locks (int \<circ> expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'" by simp
  have "upd_expr_locks (\<lambda>b. int (if a = b then Suc (expr_locks e b) else expr_locks (locked(a)) b + expr_locks e b)) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a
        = upd_expr_locks (\<lambda>b. 1 + int (expr_locks e b)) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a"
    by(auto intro: upd_expr_locks_cong)
  also have "\<dots> = 1 + upd_expr_locks (\<lambda>b. int (expr_locks e b)) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a"
    by(simp add: upd_expr_locks_add)
  finally show ?case using IH'
    by(auto intro!: ext simp add: upd_expr_locks_def expand_fun_eq)
next prefer 52
  case (SynchronizedWait e s ta e' s' a was)
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note IH = `addr_ok e \<Longrightarrow> upd_expr_locks (int \<circ> expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'`
  note aoe = `addr_ok (sync(locked(a)) e)`
  from IH aoe have IH': "upd_expr_locks (int \<circ> expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'" by simp
  have "upd_expr_locks (\<lambda>b. int (if a = b then Suc (expr_locks e b) else expr_locks (locked(a)) b + expr_locks e b)) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a = 
        upd_expr_locks (\<lambda>b. 1 + int (expr_locks e b)) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a"
    by(auto intro: upd_expr_locks_cong)
  also have "\<dots> = 1 + upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> a"
    by(simp add: o_def upd_expr_locks_add)
  finally show ?case using IH'
    by(cases ta)(auto intro!: ext simp add: upd_expr_locks_def upd_expr_locks_delta_def expand_fun_eq)
next prefer 53
  case (SeqRed e s ta e' s' e2)
  note IH = `addr_ok e \<Longrightarrow> upd_expr_locks (int \<circ> expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'`
  note red = `P \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>`
  note aoe = `addr_ok (e;; e2)`
  with IH have IH': "\<And>x. upd_expr_locks (\<lambda>a. int (expr_locks e a)) (fst ta) x = int (expr_locks e' x)"
    by(simp add: o_def)
  have "upd_expr_locks (int \<circ> expr_locks (e;; e2)) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>
        = upd_expr_locks (\<lambda>a. int (expr_locks e a) + int (expr_locks e2 a)) (fst ta)"
    by(simp add: o_def)
  also have "\<dots> = upd_expr_locks (\<lambda>a. int (expr_locks e2 a) + int (expr_locks e a)) (fst ta)"
    by(unfold zadd_commute, simp)
  also have "\<dots> = (\<lambda>a. int (expr_locks e' a) + int (expr_locks e2 a))"
    by(auto simp add: upd_expr_locks_add intro!: ext IH')
  finally show ?case
    by(simp add: o_def)
next prefer 81
  case (SynchronizedThrow1 a e s)
  thus ?case
    by(auto simp add: upd_expr_locks_def upd_expr_locks_delta_def contains_addr_expr_locks lock_granted_def intro!: ext)
next prefer 81
  case (SynchronizedThrow2 a ad s)
  show ?case
    by(auto simp add: upd_expr_locks_def upd_expr_locks_delta_def intro!: ext)
qed(fastsimp simp add: upd_expr_locks_def upd_expr_locks_delta_def contains_addr_expr_locks contains_addrs_expr_lockss intro: ext wwf)+

definition lock_ok :: "(addr,thread_id) locks \<Rightarrow> (thread_id,expr \<times> locals) thread_info \<Rightarrow> bool" where
  "lock_ok ls ts \<equiv> \<forall>t. (case (ts t) of None    \<Rightarrow> (\<forall>l. has_locks (ls l) t 0)
                                     | \<lfloor>(e, x)\<rfloor> \<Rightarrow> (\<forall>l. has_locks (ls l) t (expr_locks e l)))"

lemma lock_okI:
  "\<lbrakk> \<And>t l. ts t = None \<Longrightarrow> has_locks (ls l) t 0; \<And>t e x l. ts t = \<lfloor>(e, x)\<rfloor> \<Longrightarrow> has_locks (ls l) t (expr_locks e l) \<rbrakk> \<Longrightarrow> lock_ok ls ts"
apply(auto simp add: lock_ok_def)
done

lemma lock_okE:
  "\<lbrakk> lock_ok ls ts;
     \<forall>t. ts t = None \<longrightarrow> (\<forall>l. has_locks (ls l) t 0) \<Longrightarrow> Q;
     \<forall>t e x. ts t = \<lfloor>(e, x)\<rfloor> \<longrightarrow> (\<forall>l. has_locks (ls l) t (expr_locks e l)) \<Longrightarrow> Q \<rbrakk>
  \<Longrightarrow> Q"
apply(auto simp add: lock_ok_def)
done

lemma lock_okD1:
  "\<lbrakk> lock_ok ls ts; ts t = None \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls l) t 0"
apply(simp add: lock_ok_def)
apply(erule_tac x="t" in allE)
apply(auto)
done

lemma lock_okD2:
  "\<lbrakk> lock_ok ls ts; ts t = \<lfloor>(e, x)\<rfloor> \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls l) t (expr_locks e l)"
apply(auto simp add: lock_ok_def)
done

lemma has_locks_unique: (* Move to: FWLocking *)
  "\<lbrakk> has_locks l t n; has_locks l t n' \<rbrakk> \<Longrightarrow> n = n'"
apply(auto elim: has_locksE)
done 

definition lock_expr_locks_ok :: "thread_id FWState.lock \<Rightarrow> thread_id \<Rightarrow> int \<Rightarrow> bool" where
  "lock_expr_locks_ok l t i \<equiv> (\<exists>n. has_locks l t n \<and> i = int n) \<and> i \<ge> 0"

lemma upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok:
  "\<lbrakk> lock_actions_ok l t Ls; lock_expr_locks_ok l t i \<rbrakk> \<Longrightarrow> lock_expr_locks_ok (upd_locks l t Ls) t (upd_expr_lock i Ls)"
proof(induct Ls arbitrary: l i)
  case Nil thus ?case
    by(simp add: upd_expr_locks_delta_def)
next
  case (Cons L LS l i)
  note IH = `\<And>l i. \<lbrakk>lock_actions_ok l t LS; lock_expr_locks_ok l t i\<rbrakk> \<Longrightarrow> lock_expr_locks_ok (upd_locks l t LS) t (upd_expr_lock i LS)`
  note lao = `lock_actions_ok l t (L # LS)`
  note lelo = `lock_expr_locks_ok l t i`
  hence i: "i \<ge> 0"
    and "\<exists>n. has_locks l t n \<and> i = int n"
    by(auto simp add: lock_expr_locks_ok_def)
  then obtain n
    where hl: "has_locks l t n"
    and ni: "i = int n" by blast
  from lao have laos: "lock_actions_ok (upd_lock l t L) t LS" by simp
  have lelos: "lock_expr_locks_ok (upd_lock l t L) t (i + upd_expr_lock_delta L)"
  proof(cases L)
    case Lock
    with lao have "may_lock l t" by(simp)
    with hl have "has_locks (lock_lock l t) t (Suc n)"
      by-(rule may_lock_has_locks_lock_lock_has_locks_Suc)
    with Lock i ni show ?thesis
      by(fastsimp simp add: lock_expr_locks_ok_def)
  next
    case Unlock
    with lao have "has_lock l t" by simp
    then obtain n' 
      where "has_locks l t (Suc n')"
      by(auto dest: has_lock_has_locks_Suc)
    with hl have nn': "n = Suc n'"
      by(auto intro: has_locks_unique)
    with hl have "has_locks (unlock_lock l) t n'"
      by-(rule has_locks_Suc_unlock_lock_has_locks)
    with Unlock i ni nn' show ?thesis
      by(fastsimp simp add: lock_expr_locks_ok_def)
  next
    case UnlockFail
    with lelo show ?thesis
      by(simp)
  qed
  from IH[OF laos lelos] show ?case
    by(simp add: zadd_assoc)
qed

definition ls_els_ok :: "(addr,thread_id) locks \<Rightarrow> thread_id \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> bool" where
  "ls_els_ok ls t els \<equiv> \<forall>l. lock_expr_locks_ok (ls l) t (els l)"

lemma ls_els_okI:
  "(\<And>l. lock_expr_locks_ok (ls l) t (els l)) \<Longrightarrow> ls_els_ok ls t els"
apply(auto simp add: ls_els_ok_def)
done

lemma ls_els_okE:
  "\<lbrakk> ls_els_ok ls t els; \<forall>l. lock_expr_locks_ok (ls l) t (els l) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(auto simp add: ls_els_ok_def)
done

lemma ls_els_okD:
  "ls_els_ok ls t els \<Longrightarrow> lock_expr_locks_ok (ls l) t (els l)"
apply(auto simp add: ls_els_ok_def)
done

lemma redT_updLs_upd_expr_locks_preserves_ls_els_ok:  
 "\<lbrakk> ls_els_ok ls t els; lock_ok_las ls t las \<rbrakk> \<Longrightarrow> ls_els_ok (redT_updLs ls t las) t (upd_expr_locks els las)"
apply(auto intro!: ls_els_okI  elim!: ls_els_okE simp add: redT_updLs_def lock_ok_las_def)
apply(unfold upd_expr_locks_def)
apply(blast intro: upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok)
done

lemma redT_preserves_lock_ok:
  assumes redT: "P \<turnstile> \<langle>ls, (ts, h), ws\<rangle> -t\<triangleright>ta\<rightarrow> \<langle>ls', (ts', h'), ws'\<rangle>" and
  loes: "lock_ok ls ts" and
  aoes: "addr_es_ok ts h" and
  wwf: "wwf_J_prog P"
  shows "lock_ok ls' ts'"
proof -
  from redT obtain e e' x x'
    where P: "P \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>"
    and est: "ts t = \<lfloor>(e, x)\<rfloor>"
    and lota: "lock_ok_las ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and cctta: "thread_oks ts h' \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
    and ls': "ls' = redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
    and es': "ts' = redT_updTs (ts(t \<mapsto> (e', x'))) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
    and ws': "ws' = redT_updWs ws t \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
    by(auto elim: multithreaded.redT.cases)
  from est aoes have aoe: "addr_ok e" by(auto dest: ts_okD)
  from aoe P wwf have aoe': "addr_ok e'" by -(erule red_preserve_addr_ok)
  from aoes cctta have aes': "\<forall>t e x h. NewThread t (e, x) h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<longrightarrow> addr_ok e \<Longrightarrow> addr_es_ok (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) h"
  proof(induct "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" arbitrary: ts)
    case Nil thus ?case by simp
  next
    case (Cons TA TAS TS)
    note IH = `\<And>ts. \<lbrakk>\<forall>t e x h. NewThread t (e, x) h \<in> set TAS \<longrightarrow> addr_ok e; addr_es_ok ts h; thread_oks ts h' TAS\<rbrakk> \<Longrightarrow> addr_es_ok (redT_updTs ts TAS) h`
    note aes = `addr_es_ok TS h`
    note cctta = `thread_oks TS h' (TA # TAS)`
    have nttas: "\<forall>t e x h. NewThread t (e, x) h \<in> set (TA # TAS) \<longrightarrow> addr_ok e" .
    hence nttas': "\<forall>t e x h. NewThread t (e, x) h \<in> set TAS \<longrightarrow> addr_ok e" by auto
    from aes cctta nttas
    show ?case
    proof(cases TA)
      case (NewThread T blubb M)
      obtain E X where EX: "blubb = (E, X)" by (cases blubb, auto)
      from NewThread EX nttas have "addr_ok E" by auto
      with aes have "addr_es_ok (TS(T \<mapsto> (E, X))) h"
	by(fastsimp split: if_splits intro!: ts_okI elim!: ts_okE)
      with cctta aes NewThread EX show ?thesis
	apply simp
	apply(rule IH[OF nttas'])
	by(auto)
    qed(auto intro: IH[OF nttas'])
  qed
  have "\<And>t e x h. NewThread t (e, x) h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<Longrightarrow> addr_ok e"
    by(rule red_new_thread_no_addr[THEN contains_addr_addr_ok, OF P aoe])
  hence "addr_es_ok (redT_updTs ts \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) h" by(blast intro!: aes')
  with aoe' have aoes': "addr_es_ok (redT_updTs (ts(t \<mapsto> (e', x'))) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>) h"
    apply(simp only: redT_updTs_upd[OF _ cctta, OF est, THEN sym, of "(e', x')"])
    by(fastsimp intro!: ts_okI elim!: ts_okE split: if_splits)
  { fix t'' e'' x'' l
    assume rtutes: "redT_updTs (ts(t \<mapsto> (e', x'))) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t'' = \<lfloor>(e'', x'')\<rfloor>"
    with aoes' have aoe'': "addr_ok e''" by(auto elim!: ts_okE)
    have "has_locks (ls' l) t'' (expr_locks e'' l)"
    proof(cases "t = t''")
      case True
      note tt'' = `t = t''`
      with est cctta have "redT_updTs (ts(t \<mapsto> (e', x'))) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t'' = \<lfloor>(e', x')\<rfloor>"
	apply -
	apply(rule redT_updTs_Some)
	by(simp_all add: thread_oks_upd)
      with rtutes have e'': "e'' = e'" and x'': "x'' = x'" by auto
      have "ls_els_ok ls t (int o expr_locks e)"
      proof(rule ls_els_okI)
	fix l
	note lock_okD2[OF loes, OF est]
	thus "lock_expr_locks_ok (ls l) t ((int \<circ> expr_locks e) l)"
	  by(simp add: lock_expr_locks_ok_def)
      qed
      hence "ls_els_ok (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) t (upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)"
	by(rule redT_updLs_upd_expr_locks_preserves_ls_els_ok[OF _ lota])
      hence "ls_els_ok (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) t (int o expr_locks e')"
	by(simp only: red_update_expr_locks[OF wwf P aoe])
      thus ?thesis using ls' e'' tt''
	by(auto elim!: ls_els_okE simp: lock_expr_locks_ok_def)
    next
      case False
      note tt'' = `t \<noteq> t''`
      from lota have lao: "lock_actions_ok (ls l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l)"
	by(simp add: lock_ok_las_def)
      show ?thesis
      proof(cases "ts t''")
	case None
	with est rtutes tt'' cctta have "NewThread t'' (e'', x'') h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
	  apply -
	  apply(erule redT_updTs_new_thread)
	  by(simp_all add: thread_oks_upd)
	with aoe P have "\<not> contains_addr e''"
	  by(fastsimp intro: red_new_thread_no_addr del: notI)
	hence ele''l'': "\<forall>l'. expr_locks e'' l' = 0" by(auto intro: contains_addr_expr_locks)
	hence elel: "expr_locks e'' l = 0" by simp
	from loes None  have "has_locks (ls l) t'' 0"
	  by(auto dest: lock_okD1)
	moreover note lock_actions_ok_has_locks_upd_locks_eq_has_locks[OF tt''[THEN not_sym], OF lao]
	ultimately have "has_locks (redT_updLs ls t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> l) t'' 0"
	  by(auto simp add: expand_fun_eq redT_updLs_def)
	with elel ls' show ?thesis by(auto)
      next
	case (Some a)
	then obtain E X where est'': "ts t'' = \<lfloor>(E, X)\<rfloor>" by(cases a, auto)
	with loes have IH: "has_locks (ls l) t'' (expr_locks E l)"
	  by(auto dest: lock_okD2)
	from est est'' es' tt'' cctta have "ts' t'' = \<lfloor>(E, X)\<rfloor>"
	  apply(simp)
	  apply(rule redT_updTs_Some)
	  by(simp_all add: thread_oks_upd)
	with rtutes es' have e'': "E = e''" and x'': "X = x''" by(simp_all)
	with lock_actions_ok_has_locks_upd_locks_eq_has_locks[OF tt''[THEN not_sym], OF lao] IH ls' show ?thesis
	  by(clarsimp simp add: redT_updLs_def expand_fun_eq)
      qed
    qed }
  moreover
  { fix t'' l
    assume rtutes: "redT_updTs (ts(t \<mapsto> (e', x'))) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> t'' = None"
    hence tst'': "ts t'' = None"
      by - (drule redT_updTs_None, simp split: if_splits)
    with est have tt'': "t \<noteq> t''" by auto
    from tst'' loes have "has_locks (ls l) t'' 0"
      by(auto dest: lock_okD1)
    hence "has_locks (ls' l) t'' 0"
      by(simp add: multithreaded.redT_has_locks_inv[OF redT tt'']) }
  ultimately show ?thesis using es'
    by(auto intro: lock_okI)
qed

lemmas RedT_preserves_addr_ok = lifting_wf.RedT_preserves[OF lifting_wf_addr_ok]

lemma RedT_preserves_lock_ok: (* Move To: Threaded *)
  assumes wf: "wwf_J_prog P"
  and Red: "P \<turnstile> \<langle>ls, (ts, m), ws\<rangle> -\<triangleright>ttas\<rightarrow>* \<langle>ls', (ts', m'), ws'\<rangle>"
  and ae: "addr_es_ok ts m"
  and loes: "lock_ok ls ts"
  shows "lock_ok ls' ts'"
using Red ae loes
proof(induct rule: multithreaded.RedT_induct4[where r="mred P", consumes 1, case_names refl step])
  case refl thus ?case by blast
next
  case (step ls ts m ws ttas ls' ts' m' ws' t ta ls'' ts'' m'' ws'')
  thus ?case
    apply -
    apply(erule redT_preserves_lock_ok[OF _ _ _ wf], assumption)
    by(erule RedT_preserves_addr_ok[OF wf])
qed


lemma lock_ok_not_has_lock_expr_locks:
  assumes lockok: "lock_ok ls ts"
  and tst: "ts t = \<lfloor>(e, x)\<rfloor>"
  and nhl: "\<not> has_lock (ls l) t"
  shows "expr_locks e l = 0"
proof(cases "expr_locks e l")
  case 0 thus ?thesis .
next
  case (Suc n)
  from lockok tst have "has_locks (ls l) t (expr_locks e l)"
    by(auto dest!: lock_okD2)
  with Suc have "has_lock (ls l) t"
    by(auto simp add: has_lock_has_locks_conv)
  with nhl show ?thesis by contradiction
qed

end
