(*  Title:      JinjaThreads/Framework/FWWait.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of the thread actions for wait and notify} *}

theory FWWait imports FWState begin

text {* Update functions for the wait sets in the multithreaded state *}

fun redT_updW :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> 'w wait_set_action \<Rightarrow> ('w,'t) wait_sets"
where
  "redT_updW ws t (Notify w) = (if (\<exists>t. ws t = \<lfloor>w\<rfloor>) then ws((SOME t. ws t = \<lfloor>w\<rfloor>) := None) else ws)"
| "redT_updW ws t (NotifyAll w) = (\<lambda>t. if ws t = \<lfloor>w\<rfloor> then None else ws t)"
| "redT_updW ws t (Suspend w) = ws(t \<mapsto> w)"

fun redT_updWs :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> 'w wait_set_action list \<Rightarrow> ('w,'t) wait_sets"
where
  "redT_updWs ws t [] = ws"
| "redT_updWs ws t (wa#was) = redT_updWs (redT_updW ws t wa) t was"

lemma redT_updWs_append [simp]:
  "redT_updWs ws t (was @ was') = redT_updWs (redT_updWs ws t was) t was'"
by(induct was arbitrary: ws, auto)

lemma redT_updW_None_implies_None:
  "\<lbrakk> t \<noteq> t'; ws t = None \<rbrakk> \<Longrightarrow> redT_updW ws t' wa t = None"
by(cases wa, auto)

lemma redT_updWs_None_implies_None:
  assumes "t \<noteq> t'"
  shows "ws t = None \<Longrightarrow> redT_updWs ws t' was t = None"
proof(induct was arbitrary: ws)
  case Nil thus ?case by simp
next
  case (Cons WA WAS WS)
  from `t \<noteq> t'` `WS t = None`
  have "redT_updW WS t' WA t = None"
    by(rule redT_updW_None_implies_None)
  with `\<And>ws. ws t = None \<Longrightarrow> redT_updWs ws t' WAS t = None`
  show ?case by(auto)
qed
  
lemma redT_updW_Some_Some_eq:
  "\<lbrakk> t \<noteq> t'; ws t = \<lfloor>w\<rfloor>; redT_updW ws t' wa t = \<lfloor>w'\<rfloor> \<rbrakk> \<Longrightarrow> w = w'"
by(cases wa, auto split: split_if_asm)

lemma redT_updWs_Some_Some_eq:
  assumes "t \<noteq> t'"
  shows "\<lbrakk> ws t = \<lfloor>w\<rfloor>; redT_updWs ws t' was t = \<lfloor>w'\<rfloor> \<rbrakk> \<Longrightarrow> w = w'"
proof(induct was arbitrary: ws)
  case Nil thus ?case using `t \<noteq> t'` by auto
next
  case (Cons WA WAS WS)
  from `redT_updWs WS t' (WA # WAS) t = \<lfloor>w'\<rfloor>`
  have "redT_updWs (redT_updW WS t' WA) t' WAS t = \<lfloor>w'\<rfloor>" by simp
  moreover from `t \<noteq> t'` `WS t = \<lfloor>w\<rfloor>`
  show ?case
  proof(cases "redT_updW WS t' WA t")
    case None
    with `t \<noteq> t'` have "redT_updWs (redT_updW WS t' WA) t' WAS t = None"
      by(rule redT_updWs_None_implies_None)
    with `redT_updWs (redT_updW WS t' WA) t' WAS t = \<lfloor>w'\<rfloor>` have False by simp
    thus ?thesis ..
  next
    case (Some W)
    with `t \<noteq> t'` `WS t = \<lfloor>w\<rfloor>` have "W = w"
      by(rule redT_updW_Some_Some_eq[THEN sym])
    with `\<And>ws. \<lbrakk>ws t = \<lfloor>w\<rfloor>; redT_updWs ws t' WAS t = \<lfloor>w'\<rfloor>\<rbrakk> \<Longrightarrow> w = w'`
      `redT_updWs (redT_updW WS t' WA) t' WAS t = \<lfloor>w'\<rfloor>` Some
    show ?thesis by(simp)
  qed
qed

lemma redT_updW_neq_Some_SomeD:
  "\<lbrakk> redT_updW ws t' wa t = \<lfloor>w\<rfloor>; ws t \<noteq> \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> wa = Suspend w"
by(cases wa, auto split: split_if_asm)

lemma redT_updWs_neq_Some_SomeD:
  "\<lbrakk> redT_updWs ws t' was t = \<lfloor>w\<rfloor>; ws t \<noteq> \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> Suspend w \<in> set was"
proof(induct was arbitrary: ws)
  case Nil thus ?case by simp
next
  case (Cons WA WAS WS)
  show ?case
  proof(cases "redT_updW WS t' WA t = \<lfloor>w\<rfloor>")
    case False
    with `\<lbrakk> redT_updWs (redT_updW WS t' WA) t' WAS t = \<lfloor>w\<rfloor>; redT_updW WS t' WA t \<noteq> \<lfloor>w\<rfloor> \<rbrakk>
          \<Longrightarrow> t = t' \<and> Suspend w \<in> set WAS` `redT_updWs WS t' (WA # WAS) t = \<lfloor>w\<rfloor>`
    show ?thesis by(auto)
  next
    case True
    with `WS t \<noteq> \<lfloor>w\<rfloor>` show ?thesis
      by(auto dest: redT_updW_neq_Some_SomeD)
  qed
qed

end
