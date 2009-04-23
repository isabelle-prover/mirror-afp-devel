(*  Title:      JinjaThreads/Framework/FWState.thy
    Author:     Andreas Lochbihler
*)

header {* 
  \chapter{The generic multithreaded semantics}
  \isaheader{State of the multithreaded semantics} *}

theory FWState imports "../Common/Aux" begin

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

types ('l,'t,'x,'m,'w) thread_action = "'l lock_actions \<times> ('t,'x,'m) new_thread_action list \<times> 't conditional_action list \<times> 'w wait_set_action list"

definition locks_a :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'l lock_actions" ("\<lbrace>_\<rbrace>\<^bsub>l\<^esub>" [0] 1000) where
  "locks_a \<equiv> fst"

definition thr_a :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action list" ("\<lbrace>_\<rbrace>\<^bsub>t\<^esub>" [0] 1000) where
  "thr_a \<equiv> fst o snd"

definition cond_a :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 't conditional_action list" ("\<lbrace>_\<rbrace>\<^bsub>c\<^esub>" [0] 1000) where
  "cond_a = fst o snd o snd"

definition wset_a :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'w wait_set_action list" ("\<lbrace>_\<rbrace>\<^bsub>w\<^esub>" [0] 1000)where
  "wset_a \<equiv> snd o snd o snd" 

lemma locks_a_conv [simp]: "locks_a (ls, ntsjswss) = ls"
by(simp add:locks_a_def)

lemma thr_a_conv [simp]: "thr_a (ls, nts, jswss) = nts"
by(simp add: thr_a_def)

lemma cond_a_conv [simp]: "cond_a (ls, nts, js, wws) = js"
by(simp add: cond_a_def)

lemma wset_a_conv [simp]: "wset_a (ls, nts, js, wss) = wss"
by(simp add: wset_a_def)

fun ta_update_locks :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> lock_action \<Rightarrow> 'l \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_locks (ls, nts, js, wss) lta l = (ls(\<^sup>f l := ls\<^sub>f l @ [lta]), nts, js, wss)"

fun ta_update_NewThread :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_NewThread (ls, nts, js, wss) nt = (ls, nts @ [nt], js, wss)"

fun ta_update_Conditional :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 't conditional_action \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_Conditional (ls, nts, js, wss) j = (ls, nts, js @ [j], wss)"

fun ta_update_wait_set :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'w wait_set_action \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_wait_set (ls, nts, js, wss) ws = (ls, nts, js, wss @ [ws])"

abbreviation empty_ta :: "('l,'t,'x,'m,'w) thread_action" ("\<epsilon>") where
  "empty_ta \<equiv> (\<lambda>\<^isup>f [], [], [], [])"


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
  ('l,'t,'x) thread_info = "'t \<rightharpoonup> ('x \<times> ('l \<Rightarrow>\<^isub>f nat))"
  ('w,'t) wait_sets = "'t \<rightharpoonup> 'w"
  ('l,'t,'x,'m,'w) state = "('l,'t) locks \<times> (('l,'t,'x) thread_info \<times> 'm) \<times> ('w,'t) wait_sets"

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


definition convert_extTA :: "('x \<Rightarrow> 'x') \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('l,'t,'x','m,'w) thread_action"
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
   \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and> \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> = \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> \<and> length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> = length \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> \<and> 
   (\<forall>n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>. convert_new_thread_action f (\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n) = \<lbrace>ta'\<rbrace>\<^bsub>t\<^esub> ! n)"
apply(cases ta, cases ta')
apply(auto simp add: convert_extTA_def map_eq_all_nth_conv)
done

lemma convert_extTA_compose [simp]:
  "convert_extTA f (convert_extTA g ta) = convert_extTA (f o g) ta"
by(simp add: convert_extTA_def map_compose[symmetric])


inductive
  converse3p :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
where
  converse3pI: "r a b c \<Longrightarrow> converse3p r c b a"

lemma converse3p_converse3p: "converse3p (converse3p r) = r"
by(auto intro: converse3pI intro!: ext elim: converse3p.cases)

lemma converse3pD: "converse3p r c b a \<Longrightarrow> r a b c"
by(auto elim: converse3p.cases)


inductive rtrancl3p :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where 
  rtrancl3p_refl: "rtrancl3p r a [] a"
| rtrancl3p_step: "\<lbrakk> rtrancl3p r a bs a'; r a' b a'' \<rbrakk> \<Longrightarrow> rtrancl3p r a (bs @ [b]) a''"

lemmas rtrancl3p_induct3 =
  rtrancl3p.induct[of _ "(ax,ay,az)" _ "(cx,cy,cz)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas rtrancl3p_induct4 = 
  rtrancl3p.induct[of _ "(ax,ay,az,aw)" _ "(cx,cy,cz,cw)", split_format (complete),
                 consumes 1, case_names refl step]

lemma rtrancl3p_induct4' [consumes 1, case_names refl step]:
  assumes stepify: "rtrancl3p r (ax, (ay, az), aw) bs (cx, (cy, cz), cw)"
  and refl: "\<And>a aa b ba. P a aa b ba [] a aa b ba"
  and step: "\<And>a aa b ba bs ab ac bb bc bd ad ae be bf.
       \<lbrakk> rtrancl3p r (a, (aa, b), ba) bs (ab, (ac, bb), bc);
         P a aa b ba bs ab ac bb bc; r (ab, (ac, bb), bc) bd (ad, (ae, be), bf) \<rbrakk>
       \<Longrightarrow> P a aa b ba (bs @ [bd]) ad ae be bf"
  shows "P ax ay az aw bs cx cy cz cw"
using stepify
apply -
apply(drule_tac P="\<lambda>(a, (aa, b), ba) bs (cx, (cy, cz), cw). P a aa b ba bs cx cy cz cw" in rtrancl3p.induct)
by(auto intro: refl step)

lemma rtrancl3p_induct1:
  "\<lbrakk> rtrancl3p r a bs c; P a; \<And>bs c b d. \<lbrakk> rtrancl3p r a bs c; r c b d; P c \<rbrakk> \<Longrightarrow> P d \<rbrakk> \<Longrightarrow> P c"
apply(induct rule: rtrancl3p.induct)
apply(auto)
done

lemma rtrancl3p_trans [trans]:
  assumes one: "rtrancl3p r a bs a'"
  and two: "rtrancl3p r a' bs' a''"
  shows "rtrancl3p r a (bs @ bs') a''"
using two one
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by simp
next
  case rtrancl3p_step thus ?case
    by(auto simp only: append_assoc[symmetric] intro: rtrancl3p.rtrancl3p_step)
qed

lemma rtrancl3p_step_converse:
  assumes step: "r a b a'"
  and stepify: "rtrancl3p r a' bs a''"
  shows "rtrancl3p r a (b # bs) a''"
using stepify step
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl 
  with rtrancl3p.rtrancl3p_refl[where r=r and a=a] show ?case 
    by(auto dest: rtrancl3p.rtrancl3p_step)
next
  case rtrancl3p_step thus ?case
    unfolding append_Cons[symmetric]
    by -(rule rtrancl3p.rtrancl3p_step)
qed

lemma converse_rtrancl3p_step:
  "rtrancl3p r a (b # bs) a'' \<Longrightarrow> \<exists>a'. r a b a' \<and> rtrancl3p r a' bs a''"
apply(induct bs arbitrary: a'' rule: rev_induct)
 apply(erule rtrancl3p.cases)
  apply(clarsimp)+
 apply(erule rtrancl3p.cases)
  apply(clarsimp)
  apply(rule_tac x="a''a" in exI)
  apply(clarsimp)
  apply(rule rtrancl3p_refl)
 apply(clarsimp)
apply(erule rtrancl3p.cases)
 apply(clarsimp)
apply(clarsimp)
by(fastsimp intro: rtrancl3p_step)


lemma converse_rtrancl3pD:
  "rtrancl3p (converse3p r) a' bs a \<Longrightarrow> rtrancl3p r a (rev bs) a'"
apply(induct rule: rtrancl3p.induct)
 apply(fastsimp intro: rtrancl3p.intros)
apply(auto dest: converse3pD intro: rtrancl3p_step_converse)
done

lemma rtrancl3p_converseD:
  "rtrancl3p r a bs a' \<Longrightarrow> rtrancl3p (converse3p r) a' (rev bs) a"
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case
    by(auto intro: rtrancl3p.intros)
next
  case rtrancl3p_step thus ?case
    by(auto intro: rtrancl3p_step_converse converse3p.intros)
qed

lemma rtrancl3p_converse_induct [consumes 1, case_names refl step]:
  assumes ih: "rtrancl3p r a bs a''"
  and refl: "\<And>a. P a [] a"
  and step: "\<And>a b a' bs a''. \<lbrakk> rtrancl3p r a' bs a''; r a b a'; P a' bs a'' \<rbrakk> \<Longrightarrow> P a (b # bs) a''"
  shows "P a bs a''"
  using ih
proof(induct bs arbitrary: a a'')
  case Nil thus ?case
    by(auto elim: rtrancl3p.cases intro: refl)
next
  case Cons thus ?case
    by(auto dest!: converse_rtrancl3p_step intro: step)
qed  


lemma rtrancl3p_converseE[consumes 1, case_names refl step]:
  "\<lbrakk> rtrancl3p r a bs a'';
     \<lbrakk> a = a''; bs = [] \<rbrakk> \<Longrightarrow> thesis;
     \<And>bs' b a'. \<lbrakk> bs = b # bs'; r a b a'; rtrancl3p r a' bs' a'' \<rbrakk> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
apply(induct rule: rtrancl3p_converse_induct)
by(auto)


lemma rtrancl3p_induct' [consumes 1, case_names refl step]:
  assumes major: "rtrancl3p r a bs c"
  and refl: "P a [] a"
  and step: "\<And>bs a' b a''. \<lbrakk> rtrancl3p r a bs a'; P a bs a'; r a' b a'' \<rbrakk>
             \<Longrightarrow> P a (bs @ [b]) a''"
  shows "P a bs c"
proof -
  from major have "(P a [] a \<and> (\<forall>bs a' b a''. rtrancl3p r a bs a' \<and> P a bs a' \<and> r a' b a'' \<longrightarrow> P a (bs @ [b]) a'')) \<longrightarrow> P a bs c"
    by-(erule rtrancl3p.induct, blast+)
  with refl step show ?thesis by blast
qed

types
  ('l,'t,'x,'m,'w) semantics =
    "'x \<times> 'm \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool"

end
