(*  Title:      JinjaThreads/Framework/FWState.thy
    Author:     Andreas Lochbihler
*)

header {* 
  \chapter{The generic multithreaded semantics}
  \isaheader{State of the multithreaded semantics} *}

theory FWState imports 
  "../Common/Aux"
begin

datatype lock_action =
    Lock
  | Unlock
  | UnlockFail
  | ReleaseAcquire

datatype ('t,'x,'m) new_thread_action =
    NewThread 't 'x 'm
  | NewThreadFail
  | ThreadExists 't

datatype 't conditional_action = Join 't

datatype 'w wait_set_action =
    Suspend 'w
  | Notify 'w
  | NotifyAll 'w

types 'l lock_actions = "'l \<Rightarrow>\<^isub>f lock_action list"


translations
  "lock_actions l" <= (type) "l \<Rightarrow>\<^isub>f lock_action list"

types ('l,'t,'x,'m,'w,'o) thread_action =
  "'l lock_actions \<times> ('t,'x,'m) new_thread_action list \<times>
   't conditional_action list \<times> 'w wait_set_action list \<times> 'o"
(* pretty printing for thread_action type *)
print_translation {*
  let
    fun tr' [Const ("finfun", _) $ l $ (Const ("list", _) $ Const ("lock_action", _)),
             Const ("*",_) $ (Const ("list", _) $ (Const ("new_thread_action", _) $ t1 $ x $ m)) $
                             (Const ("*", _) $ (Const ("list", _) $ (Const ("conditional_action", _) $ t2)) $
                                               (Const ("*", _) $ (Const ("list", _) $ (Const ("wait_set_action", _) $ w)) $ o1))] =
      if t1 = t2 then Syntax.const "thread_action" $ l $ t1 $ x $ m $ w $ o1
      else raise Match;
  in [("*",tr')]
  end
*}
(* typ "('l,'t,'x,'m,'w,'o) thread_action" *)

definition locks_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'l lock_actions" ("\<lbrace>_\<rbrace>\<^bsub>l\<^esub>" [0] 1000) where
  "locks_a \<equiv> fst"

definition thr_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action list" ("\<lbrace>_\<rbrace>\<^bsub>t\<^esub>" [0] 1000) where
  "thr_a \<equiv> fst o snd"

definition cond_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't conditional_action list" ("\<lbrace>_\<rbrace>\<^bsub>c\<^esub>" [0] 1000) where
  "cond_a = fst o snd o snd"

definition wset_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'w wait_set_action list" ("\<lbrace>_\<rbrace>\<^bsub>w\<^esub>" [0] 1000)where
  "wset_a \<equiv> fst o snd o snd o snd" 

definition obs_a :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'o" ("\<lbrace>_\<rbrace>\<^bsub>o\<^esub>" [0] 1000) where
  "obs_a \<equiv> snd o snd o snd o snd" 

lemma locks_a_conv [simp]: "locks_a (ls, ntsjswss) = ls"
by(simp add:locks_a_def)

lemma thr_a_conv [simp]: "thr_a (ls, nts, jswss) = nts"
by(simp add: thr_a_def)

lemma cond_a_conv [simp]: "cond_a (ls, nts, js, wws) = js"
by(simp add: cond_a_def)

lemma wset_a_conv [simp]: "wset_a (ls, nts, js, wss, obs) = wss"
by(simp add: wset_a_def)

lemma obs_a_conv [simp]: "obs_a (ls, nts, js, wss, obs) = obs"
by(simp add: obs_a_def)

fun ta_update_locks :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> lock_action \<Rightarrow> 'l \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_locks (ls, nts, js, wss, obs) lta l = (ls(\<^sup>f l := ls\<^sub>f l @ [lta]), nts, js, wss, obs)"

fun ta_update_NewThread :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_NewThread (ls, nts, js, wss, obs) nt = (ls, nts @ [nt], js, wss, obs)"

fun ta_update_Conditional :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't conditional_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action"
where
  "ta_update_Conditional (ls, nts, js, wss, obs) j = (ls, nts, js @ [j], wss, obs)"

fun ta_update_wait_set :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'w wait_set_action \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action" where
  "ta_update_wait_set (ls, nts, js, wss, obs) ws = (ls, nts, js, wss @ [ws], obs)"

fun ta_update_obs :: "('l,'t,'x,'m,'w,'o option) thread_action \<Rightarrow> 'o \<Rightarrow> ('l,'t,'x,'m,'w,'o option) thread_action" ("_\<lbrace>\<^bsub>o\<^esub>_\<rbrace>" [1000,0] 1000)
where
  "ta_update_obs (ls, nts, js, wss, obs) ob = (ls, nts, js, wss, Some ob)"

abbreviation empty_ta :: "('l,'t,'x,'m,'w,'o option) thread_action" ("\<epsilon>") where
  "empty_ta \<equiv> (\<lambda>\<^isup>f [], [], [], [], None)"


nonterminals
  locklets locklet
syntax
  "_locklet"  :: "lock_action \<Rightarrow> 'l \<Rightarrow> locklet"             ("(2_/\<rightarrow>_)")
  ""         :: "locklet \<Rightarrow> locklets"             ("_")
  "_locklets" :: "locklet \<Rightarrow> locklets \<Rightarrow> locklets" ("_,/ _")
  "_lockUpdate" :: "'a \<Rightarrow> locklets \<Rightarrow> 'a"            ("_\<lbrace>\<^bsub>l\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_lockUpdate ta (_locklets b bs)"  == "_lockUpdate (_lockUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>l\<^esub>x\<rightarrow>y\<rbrace>"                         == "(CONST ta_update_locks) ta x y"


nonterminals
  ntlets ntlet
syntax
  "_ntlet"  :: "('t,'m,'x) new_thread_action \<Rightarrow> ntlet"             ("(_)")
  ""         :: "ntlet \<Rightarrow> ntlets"             ("_")
  "_ntlets" :: "ntlet \<Rightarrow> ntlets \<Rightarrow> ntlets" ("_,/ _")
  "_ntUpdate" :: "'a \<Rightarrow> ntlets \<Rightarrow> 'a"            ("_\<lbrace>\<^bsub>t\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_ntUpdate ta (_ntlets b bs)"  == "_ntUpdate (_ntUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>t\<^esub>nt\<rbrace>"                         == "(CONST ta_update_NewThread) ta nt"


nonterminals
  jlets jlet
syntax
  "_jlet"  :: "'t conditional_action \<Rightarrow> jlet"             ("(_)")
  ""         :: "jlet \<Rightarrow> jlets"             ("_")
  "_jlets" :: "jlet \<Rightarrow> jlets \<Rightarrow> jlets" ("_,/ _")
  "_jUpdate" :: "'a \<Rightarrow> jlets \<Rightarrow> 'a"            ("_\<lbrace>\<^bsub>c\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_jUpdate ta (_jlets b bs)"  == "_jUpdate (_jUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>c\<^esub>nt\<rbrace>"                         == "(CONST ta_update_Conditional) ta nt"


nonterminals
  wslets wslet
syntax
  "_wslet"  :: "'w wait_set_action \<Rightarrow> wslet"             ("(_)")
  ""         :: "wslet \<Rightarrow> wslets"             ("_")
  "_wslets" :: "wslet \<Rightarrow> wslets \<Rightarrow> wslets" ("_,/ _")
  "_wsUpdate" :: "'a \<Rightarrow> wslets \<Rightarrow> 'a"            ("_\<lbrace>\<^bsub>w\<^esub>/(_)\<rbrace>" [1000,0] 1000)

translations
  "_wsUpdate ta (_wslets b bs)"  == "_wsUpdate (_wsUpdate ta b) bs"
  "ta\<lbrace>\<^bsub>w\<^esub>ws\<rbrace>"                         == "(CONST ta_update_wait_set) ta ws"


types
  't lock = "('t \<times> nat) option"
  ('l,'t) locks = "'l \<Rightarrow>\<^isub>f 't lock"
  'l released_locks = "'l \<Rightarrow>\<^isub>f nat"
  ('l,'t,'x) thread_info = "'t \<rightharpoonup> ('x \<times> 'l released_locks)"
  ('w,'t) wait_sets = "'t \<rightharpoonup> 'w"
  ('l,'t,'x,'m,'w) state = "('l,'t) locks \<times> (('l,'t,'x) thread_info \<times> 'm) \<times> ('w,'t) wait_sets"
translations
  "locks l t" <= (type) "l \<Rightarrow>\<^isub>f (t \<times> nat) option"
  "thread_info l t x" <= (type) "t \<rightharpoonup> (x \<times> (l \<Rightarrow>\<^isub>f nat))"
(* pretty printing for state type *)
print_translation {*
  let
    fun tr' [Const ("finfun", _) $ l1 $ (Const ("option", _) $ (Const ("*", _) $ t1 $ Const ("nat", _))),
             Const ("*", _) $
               (Const ("*", _) $ (Const ("fun", _) $ t2 $
                                   (Const ("option", _) $ (Const ("*", _) $ x $
                                                            (Const ("finfun", _) $ l2 $ Const ("nat", _))))) $ m) $
               (Const ("fun", _) $ t3 $ (Const ("option", _) $ w))] =
      if t1 = t2 andalso t1 = t3 andalso l1 = l2
      then Syntax.const "state" $ l1 $ t1 $ x $ m $ w
      else raise Match;
  in [("*",tr')]
  end
*}
(* typ "('l,'t,'x,'m,'w) state" *)

abbreviation no_wait_locks :: "'l \<Rightarrow>\<^isub>f nat"
where "no_wait_locks \<equiv> (\<lambda>\<^isup>f 0)"

lemma neq_no_wait_locks_conv:
  "ln \<noteq> no_wait_locks \<longleftrightarrow> (\<exists>l. ln\<^sub>f l > 0)"
by(auto simp add: expand_finfun_eq expand_fun_eq)

lemma neq_no_wait_locksE:
  assumes "ln \<noteq> no_wait_locks" obtains l where "ln\<^sub>f l > 0"
using assms
by(auto simp add: neq_no_wait_locks_conv)


definition locks :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t) locks" where
  "locks lstsmws \<equiv> fst lstsmws"

definition thr :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,'x) thread_info" where
  "thr lstsmws \<equiv> fst (fst (snd lstsmws))"

definition shr :: "('l,'t,'x,'m,'w) state \<Rightarrow> 'm" where
  "shr lstsmws \<equiv> snd (fst (snd lstsmws))"

definition wset :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('w,'t) wait_sets" where
  "wset lstsmws \<equiv> snd (snd lstsmws)"

lemma locks_conv [simp]: "locks (ls, tsmws) = ls"
by(simp add: locks_def)

lemma thr_conv [simp]: "thr (ls, (ts, m), ws) = ts"
by(simp add: thr_def)

lemma shr_conv [simp]: "shr (ls, (ts, m), ws) = m"
by(simp add: shr_def)

lemma wset_conv [simp]: "wset (ls, (ts, m), ws) = ws"
by(simp add: wset_def)

primrec convert_new_thread_action :: "('x \<Rightarrow> 'x') \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('t,'x','m) new_thread_action"
where
  "convert_new_thread_action f (NewThread t x m) = NewThread t (f x) m"
| "convert_new_thread_action f (ThreadExists t) = ThreadExists t"
| "convert_new_thread_action f NewThreadFail = NewThreadFail"

lemma convert_new_thread_action_inv [simp]:
  "NewThread t x h = convert_new_thread_action f nta \<longleftrightarrow> (\<exists>x'. nta = NewThread t x' h \<and> x = f x')"
  "ThreadExists t = convert_new_thread_action f nta \<longleftrightarrow> nta = ThreadExists t"
  "NewThreadFail = convert_new_thread_action f nta \<longleftrightarrow> nta = NewThreadFail"
  "convert_new_thread_action f nta = NewThread t x h \<longleftrightarrow> (\<exists>x'. nta = NewThread t x' h \<and> x = f x')"
  "convert_new_thread_action f nta = ThreadExists t \<longleftrightarrow> nta = ThreadExists t"
  "convert_new_thread_action f nta = NewThreadFail \<longleftrightarrow> nta = NewThreadFail"
by(cases nta, auto)+

lemma convert_new_thread_action_eqI: 
  "\<lbrakk> \<And>t x m. nta = NewThread t x m \<Longrightarrow> nta' = NewThread t (f x) m;
     \<And>t. nta = ThreadExists t \<Longrightarrow> nta' = ThreadExists t;
     nta = NewThreadFail \<Longrightarrow> nta' = NewThreadFail \<rbrakk>
  \<Longrightarrow> convert_new_thread_action f nta = nta'"
apply(cases nta)
apply auto
done

lemma convert_new_thread_action_compose [simp]:
  "convert_new_thread_action f (convert_new_thread_action g ta) = convert_new_thread_action (f o g) ta"
apply(cases ta)
apply(simp_all add: convert_new_thread_action_def)
done


definition convert_extTA :: "('x \<Rightarrow> 'x') \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l,'t,'x','m,'w,'o) thread_action"
where "convert_extTA f ta = (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub>, map (convert_new_thread_action f) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>, snd (snd ta))"

lemma convert_extTA_simps [simp]:
  "convert_extTA f \<epsilon> = \<epsilon>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>t\<^esub> = map (convert_new_thread_action f) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>"
  "\<lbrace>convert_extTA f ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
  "convert_extTA f (las, tas, was, cas) = (las, map (convert_new_thread_action f) tas, was, cas)"
apply(simp_all add: convert_extTA_def)
apply(cases ta, simp)+
done

lemma convert_extTA_eq_conv:
  "convert_extTA f ta = ta' \<longleftrightarrow>
   \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = length \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> 
   (\<forall>n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>. convert_new_thread_action f (\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n) = \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> ! n)"
apply(cases ta, cases ta')
apply(auto simp add: convert_extTA_def map_eq_all_nth_conv)
done

lemma convert_extTA_compose [simp]:
  "convert_extTA f (convert_extTA g ta) = convert_extTA (f o g) ta"
by(simp add: convert_extTA_def)

lemma obs_a_convert_extTA [simp]: "obs_a (convert_extTA f ta) = obs_a ta"
by(cases ta) simp



types
  ('l,'t,'x,'m,'w,'o) semantics =
    "'x \<times> 'm \<Rightarrow> ('l,'t,'x,'m,'w,'o option) thread_action \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool"

(* pretty printing for semantics *)
print_translation {*
  let
    fun tr' [Const ("*", _) $ x1 $ m1,
             Const ("fun", _) $
               (Const ("*", _) $ 
                 (Const ("finfun", _) $ l $ (Const ("list", _) $ Const ("lock_action", _))) $
                 (Const ("*",_) $ (Const ("list", _) $ (Const ("new_thread_action", _) $ t1 $ x2 $ m2)) $
                                  (Const ("*", _) $ (Const ("list", _) $ (Const ("conditional_action", _) $ t2)) $
                                         (Const ("*", _) $ (Const ("list", _) $ (Const ("wait_set_action", _) $ w)) $
                                                           (Const ("option", _) $ o1))))) $
               (Const ("fun", _) $ (Const ("*", _) $ x3 $ m3) $ Const ("bool", _))] =
      if x1 = x2 andalso x1 = x3 andalso m1 = m2 andalso m1 = m3 andalso t1 = t2
      then Syntax.const "semantics" $ l $ t1 $ x1 $ m1 $ w $ o1
      else raise Match;
  in [("fun",tr')]
  end
*}
(* typ "('l,'t,'x,'m,'w,'o) semantics" *)

types ('a, 'b) trsys = "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
types ('a, 'b) bisim = "'a \<Rightarrow> 'b \<Rightarrow> bool"

locale trsys = 
  fixes trsys :: "('s, 'tl) trsys" ("_/ -_\<rightarrow>/ _" [50, 0, 50] 60)
begin

abbreviation Trsys :: "('s, 'tl list) trsys" ("_/ -_\<rightarrow>*/ _" [50,0,50] 60)
where "\<And>tl. s -tl\<rightarrow>* s' \<equiv> rtrancl3p trsys s tl s'"

end

end
