(*  Title:      JinjaThreads/Framework/FWWait.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics of the thread actions for wait, notify and interrupt} *}

theory FWWait imports FWState begin

text {* Update functions for the wait sets in the multithreaded state *}

primrec redT_updW :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> ('t,'w) wait_set_action \<Rightarrow> ('w,'t) wait_sets"
where
  "redT_updW ws t (Notify w) = (if (\<exists>t. ws t = \<lfloor>InWS w\<rfloor>) then ws((SOME t. ws t = \<lfloor>InWS w\<rfloor>) \<mapsto> WokenUp WSNotified) else ws)"
| "redT_updW ws t (NotifyAll w) = (\<lambda>t. if ws t = \<lfloor>InWS w\<rfloor> then \<lfloor>WokenUp WSNotified\<rfloor> else ws t)"
| "redT_updW ws t (Suspend w) = ws(t \<mapsto> InWS w)"
| "redT_updW ws t (Interrupt T) = (if \<exists>w. (ws t = \<lfloor>InWS w\<rfloor>) then ws(t \<mapsto> WokenUp WSInterrupted) else ws)"
| "redT_updW ws t Notified = ws(t := None)"
| "redT_updW ws t Interrupted = ws(t := None)"

fun redT_updWs :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> ('w,'t) wait_sets"
where
  "redT_updWs ws t [] = ws"
| "redT_updWs ws t (wa#was) = redT_updWs (redT_updW ws t wa) t was"

lemma redT_updWs_append [simp]:
  "redT_updWs ws t (was @ was') = redT_updWs (redT_updWs ws t was) t was'"
by(induct was arbitrary: ws, auto)

lemma redT_updW_None_implies_None:
  "\<lbrakk> t \<noteq> t'; ws t = None \<rbrakk> \<Longrightarrow> redT_updW ws t' wa t = None"
by(cases wa)(auto dest: someI[where P="\<lambda>t. ws t = \<lfloor>InWS w\<rfloor>", standard])

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

lemma redT_updW_WokenUp_imp_WokenUp:
  "\<lbrakk> t'' \<noteq> t; ws t'' = \<lfloor>WokenUp w\<rfloor> \<rbrakk> \<Longrightarrow> redT_updW ws t wa t'' = \<lfloor>WokenUp w\<rfloor>"
by(cases wa)(auto dest: someI[where P = "\<lambda>t. ws t = \<lfloor>InWS w'\<rfloor>", standard])

lemma redT_updWs_WokenUp_imp_WokenUp:
  "\<lbrakk> t'' \<noteq> t; ws t'' = \<lfloor>WokenUp w\<rfloor> \<rbrakk> \<Longrightarrow> redT_updWs ws t was t'' = \<lfloor>WokenUp w\<rfloor>"
by(induct was arbitrary: ws)(simp_all add: redT_updW_WokenUp_imp_WokenUp)

lemma redT_updW_Some_otherD:
  "\<lbrakk> t \<noteq> t'; redT_updW ws t' wa t = \<lfloor>w\<rfloor> \<rbrakk>
  \<Longrightarrow> (case w of InWS w' \<Rightarrow> ws t = \<lfloor>InWS w'\<rfloor> | _ \<Rightarrow> ws t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. ws t = \<lfloor>InWS w'\<rfloor>))"
apply(cases wa)
apply(auto split: split_if_asm wait_set_status.split dest: someI[where P = "\<lambda>t. ws t = \<lfloor>InWS w'\<rfloor>", standard])
done

lemma redT_updWs_Some_otherD:
  "\<lbrakk> t \<noteq> t'; redT_updWs ws t' was t = \<lfloor>w\<rfloor> \<rbrakk>
  \<Longrightarrow> (case w of InWS w' \<Rightarrow> ws t = \<lfloor>InWS w'\<rfloor> | _ \<Rightarrow> ws t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. ws t = \<lfloor>InWS w'\<rfloor>))"
proof(induct was arbitrary: ws)
  case Nil thus ?case by(simp split: wait_set_status.split)
next
  case (Cons wa was)
  from `redT_updWs ws t' (wa # was) t = \<lfloor>w\<rfloor>`
  have "redT_updWs (redT_updW ws t' wa) t' was t = \<lfloor>w\<rfloor>" by simp
  with `t \<noteq> t'`
  have "case w of InWS w' \<Rightarrow> redT_updW ws t' wa t = \<lfloor>InWS w'\<rfloor>
                | _       \<Rightarrow> redT_updW ws t' wa t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. redT_updW ws t' wa t = \<lfloor>InWS w'\<rfloor>)"
    by(rule Cons)
  thus ?case by(auto dest: redT_updW_Some_otherD[OF `t \<noteq> t'`] split: wait_set_status.split_asm)
qed

lemma redT_updW_None_SomeD:
  "\<lbrakk> redT_updW ws t wa t' = \<lfloor>w\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> t = t' \<and> (\<exists>w'. w = InWS w' \<and> wa = Suspend w')"
by(cases wa)(auto split: split_if_asm dest: someI[where P="\<lambda>t. ws t = \<lfloor>InWS w'\<rfloor>", standard])

lemma redT_updWs_None_SomeD:
  "\<lbrakk> redT_updWs ws t was t' = \<lfloor>w\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> t = t' \<and> (\<exists>w'. Suspend w' \<in> set was)"
proof(induct was arbitrary: ws w)
  case Nil thus ?case by simp
next
  case (Cons wa was)
  show ?case
  proof(cases "redT_updW ws t wa t'")
    case None
    from `redT_updWs ws t (wa # was) t' = \<lfloor>w\<rfloor>`
    have "redT_updWs (redT_updW ws t wa) t was t' = \<lfloor>w\<rfloor>" by simp
    hence "t = t' \<and> (\<exists>w'. Suspend w' \<in> set was)" using None by(rule Cons)
    thus ?thesis by auto
  next
    case (Some w')
    with `ws t' = None` show ?thesis
      by(auto dest: redT_updW_None_SomeD)
  qed
qed
  
lemma redT_updW_neq_Some_SomeD:
  "\<lbrakk> redT_updW ws t' wa t = \<lfloor>InWS w\<rfloor>; ws t \<noteq> \<lfloor>InWS w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> wa = Suspend w"
by(cases wa)(auto split: split_if_asm)

lemma redT_updWs_neq_Some_SomeD:
  "\<lbrakk> redT_updWs ws t was t' = \<lfloor>InWS w\<rfloor>; ws t' \<noteq> \<lfloor>InWS w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> Suspend w \<in> set was"
proof(induct was arbitrary: ws)
  case Nil thus ?case by simp
next
  case (Cons wa was)
  show ?case
  proof(cases "redT_updW ws t wa t' = \<lfloor>InWS w\<rfloor>")
    case False
    from `redT_updWs ws t (wa # was) t' = \<lfloor>InWS w\<rfloor>`
    have "redT_updWs (redT_updW ws t wa) t was t' = \<lfloor>InWS w\<rfloor>" by simp
    hence "t = t' \<and> Suspend w \<in> set was" using False by(rule Cons)
    thus ?thesis by auto
  next
    case True
    hence "t' = t \<and> wa = Suspend w" using `ws t' \<noteq> \<lfloor>InWS w\<rfloor>`
      by(rule redT_updW_neq_Some_SomeD)
    thus ?thesis by simp
  qed
qed

lemma redT_updW_not_Suspend_Some:
  "\<lbrakk> redT_updW ws t wa t = \<lfloor>w'\<rfloor>; ws t = \<lfloor>w\<rfloor>; \<And>w. wa \<noteq> Suspend w \<rbrakk>
  \<Longrightarrow> w' = w \<or> (\<exists>w'' w'''. w = InWS w'' \<and> w' = WokenUp w''')"
apply(cases wa)
apply(auto split: split_if_asm)
apply(drule someI[where P="\<lambda>t. ws t = \<lfloor>InWS w''\<rfloor>", standard]) back
apply fastsimp
done

lemma redT_updWs_not_Suspend_Some:
  "\<lbrakk> redT_updWs ws t was t = \<lfloor>w'\<rfloor>; ws t = \<lfloor>w\<rfloor>; \<And>w. Suspend w \<notin> set was \<rbrakk>
  \<Longrightarrow> w' = w \<or> (\<exists>w'' w'''. w = InWS w'' \<and> w' = WokenUp w''')"
proof(induct was arbitrary: ws w)
  case Nil thus ?case by simp
next
  case (Cons wa was)
  from `redT_updWs ws t (wa # was) t = \<lfloor>w'\<rfloor>`
  have "redT_updWs (redT_updW ws t wa) t was t = \<lfloor>w'\<rfloor>" by simp
  moreover
  have "redT_updW ws t wa t \<noteq> None"
  proof
    assume "redT_updW ws t wa t = None"
    from redT_updWs_None_SomeD[OF `redT_updWs (redT_updW ws t wa) t was t = \<lfloor>w'\<rfloor>`, OF this]
    obtain w' where "Suspend w' \<in> set was" by auto
    with `Suspend w' \<notin> set (wa # was)` show False by simp
  qed
  then obtain w'' where "redT_updW ws t wa t = \<lfloor>w''\<rfloor>" by auto
  moreover {
    fix w
    from `Suspend w \<notin> set (wa # was)` have "Suspend w \<notin> set was" by simp }
  ultimately have "w' = w'' \<or> (\<exists>w''' w''''. w'' = InWS w''' \<and> w' = WokenUp w'''')" by(rule Cons)
  moreover { fix w
    from `Suspend w \<notin> set (wa # was)` have "wa \<noteq> Suspend w" by auto }
  note redT_updW_not_Suspend_Some[OF `redT_updW ws t wa t = \<lfloor>w''\<rfloor>`, OF `ws t = \<lfloor>w\<rfloor>` this]
  ultimately show ?case by auto
qed

lemma redT_updWs_WokenUp_SuspendD:
  "\<lbrakk> Notified \<in> set was \<or> Interrupted \<in> set was; redT_updWs ws t was t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>w. Suspend w \<in> set was"
by(induct was arbitrary: ws)(auto dest: redT_updWs_None_SomeD)

lemma redT_updW_Woken_Up_same_no_Notified_Interrupted:
  "\<lbrakk> redT_updW ws t wa t = \<lfloor>WokenUp w\<rfloor>; ws t = \<lfloor>WokenUp w\<rfloor>; \<And>w. wa \<noteq> Suspend w \<rbrakk>
  \<Longrightarrow> wa \<noteq> Notified \<and> wa \<noteq> Interrupted"
by(cases wa) simp_all

lemma redT_updWs_Woken_Up_same_no_Notified_Interrupted:
  "\<lbrakk> redT_updWs ws t was t = \<lfloor>WokenUp w\<rfloor>; ws t = \<lfloor>WokenUp w\<rfloor>; \<And>w. Suspend w \<notin> set was \<rbrakk>
  \<Longrightarrow> Notified \<notin> set was \<and> Interrupted \<notin> set was"
proof(induct was arbitrary: ws)
  case Nil thus ?case by simp
next
  case (Cons wa was)
  note Suspend = `\<And>w. Suspend w \<notin> set (wa # was)`
  from `redT_updWs ws t (wa # was) t = \<lfloor>WokenUp w\<rfloor>`
  have was: "redT_updWs (redT_updW ws t wa) t was t = \<lfloor>WokenUp w\<rfloor>" by simp
  moreover have "redT_updW ws t wa t = \<lfloor>WokenUp w\<rfloor>"
  proof(cases "redT_updW ws t wa t")
    case None
    from redT_updWs_None_SomeD[OF was, OF this]
    obtain w where "Suspend w \<in> set was" by auto
    with Suspend[of w] have False by simp
    thus ?thesis ..
  next
    case (Some w')
    thus ?thesis using `ws t = \<lfloor>WokenUp w\<rfloor>` Some Suspend
      by(cases wa)(auto split: split_if_asm dest: someI[where P="\<lambda>t. ws t = \<lfloor>InWS w''\<rfloor>", standard])
  qed
  moreover
  { fix w from Suspend[of w] have "Suspend w \<notin> set was" by simp }
  ultimately have "Notified \<notin> set was \<and> Interrupted \<notin> set was" by(rule Cons)
  moreover 
  { fix w from Suspend[of w] have "wa \<noteq> Suspend w" by auto }
  with `redT_updW ws t wa t = \<lfloor>WokenUp w\<rfloor>` `ws t = \<lfloor>WokenUp w\<rfloor>`
  have "wa \<noteq> Notified \<and> wa \<noteq> Interrupted" by(rule redT_updW_Woken_Up_same_no_Notified_Interrupted)
  ultimately show ?case by auto
qed

text {* Preconditions for wait set actions *}

definition wset_actions_ok :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> bool"
where
  "wset_actions_ok ws t was \<longleftrightarrow>
  (if Notified \<in> set was then ws t = \<lfloor>WokenUp WSNotified\<rfloor>
   else if Interrupted \<in> set was then ws t = \<lfloor>WokenUp WSInterrupted\<rfloor>
   else ws t = None)"

lemma wset_actions_ok_Nil [simp]:
  "wset_actions_ok ws t [] \<longleftrightarrow> ws t = None"
by(simp add: wset_actions_ok_def)

definition waiting :: "'w wait_set_status option \<Rightarrow> bool"
where "waiting w \<longleftrightarrow> (\<exists>w'. w = \<lfloor>InWS w'\<rfloor>)"

lemma not_waiting_iff:
  "\<not> waiting w \<longleftrightarrow> w = None \<or> (\<exists>w'. w = \<lfloor>WokenUp w'\<rfloor>)"
apply(cases "w")
apply(case_tac [2] a)
apply(auto simp add: waiting_def)
done

end
