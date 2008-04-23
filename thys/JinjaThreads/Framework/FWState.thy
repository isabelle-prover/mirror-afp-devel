(*  Title:      JinjaThreads/Framework/FWState.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{State of the multithreaded semantics} *}

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

types 'l lock_actions = "'l \<Rightarrow> lock_action list"

definition lock_actions_append :: "'l lock_actions \<Rightarrow> 'l lock_actions \<Rightarrow> 'l lock_actions" (infixr "@@" 65) where
  "las @@ las' \<equiv> \<lambda>l. las l @ las' l"

lemma lock_actions_append_l [simp]: 
  "(las @@ las') l = las l @ las' l"
by(simp add: lock_actions_append_def)

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
  "ta_update_locks (ls, nts, js, wss) lta l = (ls(l := ls l @ [lta]), nts, js, wss)"

fun ta_update_NewThread :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_NewThread (ls, nts, js, wss) nt = (ls, nts @ [nt], js, wss)"

fun ta_update_Conditional :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 't conditional_action \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_Conditional (ls, nts, js, wss) j = (ls, nts, js @ [j], wss)"

fun ta_update_wait_set :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'w wait_set_action \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_wait_set (ls, nts, js, wss) ws = (ls, nts, js, wss @ [ws])"

abbreviation empty_ta :: "('l,'t,'x,'m,'w) thread_action" ("\<epsilon>") where
  "empty_ta \<equiv> (\<lambda>l. [], [], [], [])"


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
  ('l,'t) locks = "'l \<Rightarrow> 't lock"
  ('l,'t,'x) thread_info = "'t \<rightharpoonup> ('x \<times> ('l \<Rightarrow> nat))"
  ('w,'t) wait_sets = "'t \<rightharpoonup> 'w"
  ('l,'t,'x,'m,'w) state = "('l,'t) locks \<times> (('l,'t,'x) thread_info \<times> 'm) \<times> ('w,'t) wait_sets"

abbreviation no_wait_locks :: "'l \<Rightarrow> nat"
where "no_wait_locks \<equiv> \<lambda>l. 0"

lemma neq_no_wait_locks_conv:
  "ln \<noteq> no_wait_locks \<longleftrightarrow> (\<exists>l. ln l > 0)"
by(auto simp add: expand_fun_eq)

lemma neq_no_wait_locksE:
  assumes "ln \<noteq> no_wait_locks" obtains l where "ln l > 0"
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


inductive
  converse3p :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"
where
  converse3pI: "r a b c \<Longrightarrow> converse3p r c b a"

lemma converse3p_converse3p: "converse3p (converse3p r) = r"
by(auto intro: converse3pI intro!: ext elim: converse3p.cases)

lemma converse3pD: "converse3p r c b a \<Longrightarrow> r a b c"
by(auto elim: converse3p.cases)


inductive stepify_pred :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where 
  stepify_pred_refl: "stepify_pred r a [] a"
| stepify_pred_step: "\<lbrakk> stepify_pred r a bs a'; r a' b a'' \<rbrakk> \<Longrightarrow> stepify_pred r a (bs @ [b]) a''"

lemmas stepify_pred_induct3 =
  stepify_pred.induct[of _ "(ax,ay,az)" _ "(cx,cy,cz)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas stepify_pred_induct4 = 
  stepify_pred.induct[of _ "(ax,ay,az,aw)" _ "(cx,cy,cz,cw)", split_format (complete),
                 consumes 1, case_names refl step]

lemma stepify_pred_induct4' [consumes 1, case_names refl step]:
  assumes stepify: "stepify_pred r (ax, (ay, az), aw) bs (cx, (cy, cz), cw)"
  and refl: "\<And>a aa b ba. P a aa b ba [] a aa b ba"
  and step: "\<And>a aa b ba bs ab ac bb bc bd ad ae be bf.
       \<lbrakk> stepify_pred r (a, (aa, b), ba) bs (ab, (ac, bb), bc);
         P a aa b ba bs ab ac bb bc; r (ab, (ac, bb), bc) bd (ad, (ae, be), bf) \<rbrakk>
       \<Longrightarrow> P a aa b ba (bs @ [bd]) ad ae be bf"
  shows "P ax ay az aw bs cx cy cz cw"
using stepify
apply -
apply(drule_tac P="\<lambda>(a, (aa, b), ba) bs (cx, (cy, cz), cw). P a aa b ba bs cx cy cz cw" in stepify_pred.induct)
by(auto intro: refl step)

lemma stepify_pred_induct1:
  "\<lbrakk> stepify_pred r a bs c; P a; \<And>bs c b d. \<lbrakk> stepify_pred r a bs c; r c b d; P c \<rbrakk> \<Longrightarrow> P d \<rbrakk> \<Longrightarrow> P c"
apply(induct rule: stepify_pred.induct)
apply(auto)
done

lemma stepify_pred_trans [trans]:
  assumes one: "stepify_pred r a bs a'"
  and two: "stepify_pred r a' bs' a''"
  shows "stepify_pred r a (bs @ bs') a''"
using two one
proof(induct rule: stepify_pred.induct)
  case stepify_pred_refl thus ?case by simp
next
  case stepify_pred_step thus ?case
    by(auto simp only: append_assoc[symmetric] intro: stepify_pred.stepify_pred_step)
qed

lemma stepify_pred_step_converse:
  assumes step: "r a b a'"
  and stepify: "stepify_pred r a' bs a''"
  shows "stepify_pred r a (b # bs) a''"
using stepify step
proof(induct rule: stepify_pred.induct)
  case stepify_pred_refl 
  with stepify_pred.stepify_pred_refl[where r=r and a=a] show ?case 
    by(auto dest: stepify_pred.stepify_pred_step)
next
  case stepify_pred_step thus ?case
    unfolding append_Cons[symmetric]
    by -(rule stepify_pred.stepify_pred_step)
qed

lemma converse_stepify_pred_step:
  "stepify_pred r a (b # bs) a'' \<Longrightarrow> \<exists>a'. r a b a' \<and> stepify_pred r a' bs a''"
apply(induct bs arbitrary: a'' rule: rev_induct)
 apply(erule stepify_pred.cases)
  apply(clarsimp)+
 apply(erule stepify_pred.cases)
  apply(clarsimp)
  apply(rule_tac x="a''a" in exI)
  apply(clarsimp)
  apply(rule stepify_pred_refl)
 apply(clarsimp)
apply(erule stepify_pred.cases)
 apply(clarsimp)
apply(clarsimp)
by(fastsimp intro: stepify_pred_step)


lemma converse_stepify_predD:
  "stepify_pred (converse3p r) a' bs a \<Longrightarrow> stepify_pred r a (rev bs) a'"
apply(induct rule: stepify_pred.induct)
 apply(fastsimp intro: stepify_pred.intros)
apply(auto dest: converse3pD intro: stepify_pred_step_converse)
done

lemma stepify_pred_converseD:
  "stepify_pred r a bs a' \<Longrightarrow> stepify_pred (converse3p r) a' (rev bs) a"
proof(induct rule: stepify_pred.induct)
  case stepify_pred_refl thus ?case
    by(auto intro: stepify_pred.intros)
next
  case stepify_pred_step thus ?case
    by(auto intro: stepify_pred_step_converse converse3p.intros)
qed

lemma stepify_pred_converse_induct [consumes 1, case_names refl step]:
  assumes ih: "stepify_pred r a bs a''"
  and refl: "\<And>a. P a [] a"
  and step: "\<And>a b a' bs a''. \<lbrakk> stepify_pred r a' bs a''; r a b a'; P a' bs a'' \<rbrakk> \<Longrightarrow> P a (b # bs) a''"
  shows "P a bs a''"
  using ih
proof(induct bs arbitrary: a a'')
  case Nil thus ?case
    by(auto elim: stepify_pred.cases intro: refl)
next
  case Cons thus ?case
    by(auto dest!: converse_stepify_pred_step intro: step)
qed  


lemma stepify_pred_converseE[consumes 1, case_names refl step]:
  "\<lbrakk> stepify_pred r a bs a'';
     \<lbrakk> a = a''; bs = [] \<rbrakk> \<Longrightarrow> thesis;
     \<And>bs' b a'. \<lbrakk> bs = b # bs'; r a b a'; stepify_pred r a' bs' a'' \<rbrakk> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
apply(induct rule: stepify_pred_converse_induct)
by(auto)


lemma stepify_pred_induct' [consumes 1, case_names refl step]:
  assumes major: "stepify_pred r a bs c"
  and refl: "P a [] a"
  and step: "\<And>bs a' b a''. \<lbrakk> stepify_pred r a bs a'; P a bs a'; r a' b a'' \<rbrakk>
             \<Longrightarrow> P a (bs @ [b]) a''"
  shows "P a bs c"
proof -
  from major have "(P a [] a \<and> (\<forall>bs a' b a''. stepify_pred r a bs a' \<and> P a bs a' \<and> r a' b a'' \<longrightarrow> P a (bs @ [b]) a'')) \<longrightarrow> P a bs c"
    by-(erule stepify_pred.induct, blast+)
  with refl step show ?thesis by blast
qed

types
  ('l,'t,'x,'m,'w) semantics =
    "'x \<times> 'm \<Rightarrow> ('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool"

end
