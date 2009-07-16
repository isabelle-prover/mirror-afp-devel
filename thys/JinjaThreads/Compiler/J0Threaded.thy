(*  Title:      JinjaThreads/Compiler/J0Threaded.thy
    Author:     Andreas Lochbihler
*)

header {* Lifting the bisimulation to the multithreaded setting: Jinja smallstep with and without call stacks *}

theory J0Threaded imports J0Bisim begin

lemma red0_mthr: "multithreaded (mred0 P)"
apply(unfold_locales)
apply(auto elim!: red0.cases)
by(auto dest: red_new_thread_heap)

abbreviation final_expr0 :: "(expr \<times> locals) \<times> (expr \<times> locals) list \<Rightarrow> bool" where
  "final_expr0 \<equiv> \<lambda>(ex, exs). final (fst ex) \<and> exs = []"

interpretation red0_mthr: multithreaded final_expr0 "mred0 P"
by(rule red0_mthr)

lemma fold_exs_eq_finalD:
  "\<lbrakk> fold_exs P h (E, X) exs = (e, x); is_call_list h (map fst exs); final e \<rbrakk>
  \<Longrightarrow> E = e \<and> exs = []"
proof(induct exs arbitrary: E X)
  case Nil thus ?case by simp
next
  case (Cons ex exs E X)
  note IH = `\<And>E X. \<lbrakk>fold_exs P h (E, X) exs = (e, x); is_call_list h (map fst exs); final e\<rbrakk> \<Longrightarrow> E = e \<and> exs = []`
  from `is_call_list h (map fst (ex # exs))`
  obtain a M vs arrobj 
    where ha: "h a = \<lfloor>arrobj\<rfloor>"
    and call: "call (fst ex) = \<lfloor>(a, M, vs)\<rfloor>"
    and icl: "is_call_list h (map fst exs)" by auto
  let ?T = "Class (fst (method P (case arrobj of Obj C fs \<Rightarrow> C | _ \<Rightarrow> arbitrary) M))"
  from ha call `fold_exs P h (E, X) (ex # exs) = (e, x)`
  have "fold_exs P h (inline_call {this:?T=X this; E}\<^bsub>True\<^esub> (fst ex), snd ex) exs = (e, x)" by simp
  from IH[OF this icl `final e`] have "inline_call {this:?T=X this; E}\<^bsub>True\<^esub> (fst ex) = e" by auto
  with `final e` call have False by(auto elim!: final.cases)
  thus ?case ..
qed

lemma fold_exs_hext:
  assumes hext: "hext h h'"
  shows "is_call_list h (map fst exs) \<Longrightarrow> fold_exs P h ex exs = fold_exs P h' ex exs"
proof(induct exs arbitrary: ex)
  case Nil thus ?case by simp
next
  case (Cons ex' exs ex)
  note IH = `\<And>ex. is_call_list h (map fst exs) \<Longrightarrow> fold_exs P h ex exs = fold_exs P h' ex exs`
  from `is_call_list h (map fst (ex' # exs))`
  obtain a M vs arrobj
    where ha: "h a = \<lfloor>arrobj\<rfloor>"
    and call: "call (fst ex') = \<lfloor>(a, M, vs)\<rfloor>"
    and icl: "is_call_list h (map fst exs)"
    by(auto)
  from hext ha
  obtain arrobj' where h'a: "h' a = \<lfloor>arrobj'\<rfloor>" by(auto dest: hext_objarrD)
  with ha call
  have "(case arrobj of Obj C fs \<Rightarrow> C | _ \<Rightarrow> arbitrary) = (case arrobj' of Obj C fs \<Rightarrow> C | _ \<Rightarrow> arbitrary)"
    by(cases arrobj, auto dest!: hext_objD[OF hext] hext_arrD[OF hext])
  with IH[OF icl] call ha h'a
  show ?case by(auto simp add: split_beta)
qed


lemma bisim_red_red0_hext_mono:
  "\<lbrakk> bisim_red_red0 P (x, m2) (x', m2); hext m2 m2' \<rbrakk> \<Longrightarrow> bisim_red_red0 P (x, m2') (x', m2')"
by(auto simp add: fold_exs_hext intro: is_call_list_hext_mono intro!: bisim_red_red0.intros elim!: bisim_red_red0.cases)

lemma red_red0_FWbase:
  "FWbisimulation_base (mred P) (mred0 P)"
..

interpretation red_red0_FWbase: FWbisimulation_base f1 "mred P" f2 "mred0 P" "bisim_red_red0 P"
  for f1 f2
by(rule red_red0_FWbase)

lemma red_red0_FWbisim:
  assumes wf: "wf_J_prog P"
  shows "FWbisimulation final_expr (mred P) final_expr0 (mred0 P) (bisim_red_red0 P)"
proof -
  interpret bisimulation "mred P" "mred0 P" "bisim_red_red0 P" "ta_bisim (bisim_red_red0 P)"
    by(rule bisimulation_red_red0[OF wf])
  show ?thesis
  proof
    fix x1 m1 x2 m2 assume "bisim_red_red0 P (x1, m1) (x2, m2)"
    thus "final_expr x1 = final_expr0 x2"
      by(auto elim!: bisim_red_red0.cases dest: fold_exs_eq_finalD)
  next
    fix x m1 x' m2 x1 x2 ta1 x1' m1' ta2 x2' m2'
    assume b: "bisim_red_red0 P (x, m1) (x', m2)"
      and bo: "bisim_red_red0 P (x1, m1) (x2, m2)"
      and red1: "mred P (x1, m1) ta1 (x1', m1')"
      and red2: "mred0 P (x2, m2) ta2 (x2', m2')"
      and bo': "bisim_red_red0 P (x1', m1') (x2', m2')"
      and tb: "ta_bisim (bisim_red_red0 P) ta1 ta2"
    from b have "m1 = m2" by(auto elim: bisim_red_red0.cases)
    moreover from bo' have "m1' = m2'" by(auto elim: bisim_red_red0.cases)
    moreover from red1 have "hext m1 m1'" by(auto simp add: split_beta dest: red_hext_incr)
    ultimately show "bisim_red_red0 P (x, m1') (x', m2')" using b
      by(auto intro: bisim_red_red0_hext_mono)
  qed
qed


end