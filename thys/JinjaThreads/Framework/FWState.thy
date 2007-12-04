(*  Title:      JinjaThreads/Framework/FWState.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{State of the multithreaded semantics} *}

theory FWState imports "../Common/Aux" begin

datatype lock_action =
    Lock
  | Unlock
  | UnlockFail

datatype ('t,'x,'m) new_thread_action =
    NewThread 't 'x 'm
  | NewThreadFail

datatype 'w wait_set_action =
    Suspend 'w
  | Notify 'w
  | NotifyAll 'w

types 'l lock_actions = "'l \<Rightarrow> lock_action list"

definition lock_actions_append :: "'l lock_actions \<Rightarrow> 'l lock_actions \<Rightarrow> 'l lock_actions" (infixr "@@" 65) where
  "las @@ las' \<equiv> \<lambda>l. las l @ las' l"


types ('l,'t,'x,'m,'w) thread_action = "'l lock_actions \<times> ('t,'x,'m) new_thread_action list \<times> 'w wait_set_action list"

definition locks_a :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'l lock_actions" ("\<lbrace>_\<rbrace>\<^bsub>l\<^esub>" [0] 1000) where
  "locks_a \<equiv> fst"

definition thr_a :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action list" ("\<lbrace>_\<rbrace>\<^bsub>t\<^esub>" [0] 1000) where
  "thr_a \<equiv> fst o snd"

definition wset_a :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'w wait_set_action list" ("\<lbrace>_\<rbrace>\<^bsub>w\<^esub>" [0] 1000)where
  "wset_a \<equiv> snd o snd" 

declare locks_a_def[simp] thr_a_def[simp] wset_a_def[simp]

fun ta_update_locks :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> lock_action \<Rightarrow> 'l \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_locks (ls, nts, wss) lta l = (ls(l := ls l @ [lta]), nts, wss)"

fun ta_update_NewThread :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_NewThread (ls, nts, wss) nt = (ls, nts @ [nt], wss)"

fun ta_update_wait_set :: "('l,'t,'x,'m,'w) thread_action \<Rightarrow> 'w wait_set_action \<Rightarrow> ('l,'t,'x,'m,'w) thread_action" where
  "ta_update_wait_set (ls, nts, wss) ws = (ls, nts, wss @ [ws])"


abbreviation empty_ta :: "('l,'t,'x,'m,'w) thread_action" ("\<epsilon>") where
  "empty_ta \<equiv> (\<lambda>l. [], [], [])"


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
  ('t,'x) thread_info = "'t \<rightharpoonup> 'x"
  ('w,'t) wait_sets = "'t \<rightharpoonup> 'w"
  ('l,'t,'x,'m,'w) state = "('l,'t) locks \<times> (('t,'x) thread_info \<times> 'm) \<times> ('w,'t) wait_sets"

definition locks :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t) locks" where
  "locks lstsmws \<equiv> fst lstsmws"

definition thr :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t,'x) thread_info" where
  "thr lstsmws \<equiv> fst (fst (snd lstsmws))"

definition shr :: "('l,'t,'x,'m,'w) state \<Rightarrow> 'm" where
  "shr lstsmws \<equiv> snd (fst (snd lstsmws))"

definition wset :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('w,'t) wait_sets" where
  "wset lstsmws \<equiv> snd (snd lstsmws)"

declare locks_def[simp] thr_def[simp] shr_def[simp] wset_def[simp]

inductive_set stepify :: "('a \<times> 'b \<times> 'a) set \<Rightarrow> ('a \<times> 'b list \<times> 'a) set"
  for r :: "('a \<times> 'b \<times> 'a) set"
  where 
  stepify_refl: "(a, [], a) \<in> stepify r"
| stepify_trans: "\<lbrakk> (a, bs, a') \<in> stepify r; (a', b, a'') \<in> r \<rbrakk> \<Longrightarrow> (a, bs @ [b], a'') \<in> stepify r"

lemmas stepify_induct2 = 
  stepify.induct[of "(ax,ay)" _ "(cx,cy)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas stepify_induct3 =
  stepify.induct[of "(ax,ay,az)" _ "(cx,cy,cz)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas stepify_induct4 = 
  stepify.induct[of "(ax,ay,az,aw)" _ "(cx,cy,cz,cw)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas stepify_induct4' = 
  stepify.induct[of "(ax,(ay,az),aw)" _ "(cx,(cy,cz),cw)", split_format (complete),
                 consumes 1, case_names refl step]

inductive_set stepify_pred :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b list \<times> 'a) set"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where 
  stepify_pred_refl: "(a, [], a) \<in> stepify_pred r"
| stepify_pred_trans: "\<lbrakk> (a, bs, a') \<in> stepify_pred r; r a' b a'' \<rbrakk> \<Longrightarrow> (a, bs @ [b], a'') \<in> stepify_pred r"

lemmas stepify_pred_induct2 = 
  stepify_pred.induct[of "(ax,ay)" _ "(cx,cy)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas stepify_pred_induct3 =
  stepify_pred.induct[of "(ax,ay,az)" _ "(cx,cy,cz)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas stepify_pred_induct4 = 
  stepify_pred.induct[of "(ax,ay,az,aw)" _ "(cx,cy,cz,cw)", split_format (complete),
                 consumes 1, case_names refl step]

lemmas stepify_pred_induct4' = 
  stepify_pred.induct[of "(ax,(ay,az),aw)" _ "(cx,(cy,cz),cw)", split_format (complete),
                 consumes 1, case_names refl step]


types
  ('l,'t,'x,'m,'w) semantics = "(('x \<times> 'm) \<times> ('l,'t,'x,'m,'w) thread_action \<times> ('x \<times> 'm)) set"

end
