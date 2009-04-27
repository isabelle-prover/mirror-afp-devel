(*  Title:      JinjaThreads/Compiler/Correctness.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of both stages} *}

theory Correctness imports Correctness2Threaded Correctness1Threaded begin

abbreviation \<tau>MOVE0 :: "(((expr \<times> locals) \<times> (expr \<times> locals) list) \<times> heap,
                       (addr,addr,(expr \<times> locals) \<times> (expr \<times> locals) list,heap,addr) thread_action) trsys"
where "\<tau>MOVE0 \<equiv> \<lambda>(exexs, h) ta s. \<tau>Move1 exexs \<and> ta = \<epsilon>"

abbreviation \<tau>MOVE :: "((expr \<times> locals) \<times> heap,
                       (addr,addr,expr \<times> locals,heap,addr) thread_action) trsys"
where "\<tau>MOVE \<equiv> \<lambda>((e, x), h) ta s'. \<tau>move1 e \<and> ta = \<epsilon>"

definition bisimJ2JVM :: "J_prog \<Rightarrow> ((addr,addr,expr\<times>locals,heap,addr) state,
                                  (addr,addr,addr option \<times> frame list,heap,addr) state) bisim"
where "bisimJ2JVM P = (red_red0_FWbase.mbisim P) \<circ>\<^isub>B mbisim_red0_Red1 \<circ>\<^isub>B (Red1_exec1_FWbase.mbisim (compP1 P))"

definition tlsimJ2JVM :: "J_prog \<Rightarrow> (addr \<times> (addr,addr,expr\<times>locals,heap,addr) thread_action,
                                  addr \<times> (addr,addr,addr option \<times> frame list,heap,addr) thread_action) bisim"
where "tlsimJ2JVM P = red_red0_FWbase.mta_bisim P \<circ>\<^isub>B red0_Red1_FWbase.mta_bisim \<circ>\<^isub>B (Red1_exec1_FWbase.mta_bisim (compP1 P))"

definition J2JVM :: "J_prog \<Rightarrow> jvm_prog"
where "J2JVM \<equiv> compP2 \<circ> compP1"


lemma compP2_has_method [simp]: "compP2 P \<turnstile> C has M \<longleftrightarrow> P \<turnstile> C has M"
by(auto simp add: compP2_def)

lemma conf_compP [simp]: "compP f P,h \<turnstile> v :\<le> T \<longleftrightarrow> P,h \<turnstile> v :\<le> T"
by(auto simp add: conf_def)

lemma conf_compP_raw: "conf (compP f P) = conf P"
by(simp add: expand_fun_eq)

lemma confs_compP [simp]: "compP f P,h \<turnstile> vs [:\<le>] Ts \<longleftrightarrow> P,h \<turnstile> vs [:\<le>] Ts"
unfolding conf_compP_raw ..

lemma has_field_compP [simp]: "compP f P \<turnstile> C has F:T in D \<longleftrightarrow> P \<turnstile> C has F:T in D"
by(simp add: has_field_def)

lemma oconf_compP [simp]: "oconf (compP f P) h obj \<longleftrightarrow> P,h \<turnstile> obj \<surd>"
by(auto simp add: oconf_def split: heapobj.split)

lemma hconf_compP [simp]: "compP f P \<turnstile> h \<surd> \<longleftrightarrow> P \<turnstile> h \<surd>"
by(auto simp add: hconf_def)


lemma max_stack_blocks1 [simp]: "max_stack (blocks1 n Ts e) = max_stack e"
by(induct Ts arbitrary: n) simp_all

lemma match_ex_table_max_stack: "match_ex_table P a pc (compxE2 e pc' d') = \<lfloor>(pc'', d'')\<rfloor> \<Longrightarrow> Suc (d'' - d') \<le> max_stack e"
  and match_ex_table_max_stacks: "match_ex_table P a pc (compxEs2 es pc' d') = \<lfloor>(pc'', d'')\<rfloor> \<Longrightarrow> Suc (d'' - d') \<le> max_stacks es"
proof(induct e and es arbitrary: pc' d' and pc' d')
  case Synchronized thus ?case using max_stack1
    by(fastsimp simp add: match_ex_table_append matches_ex_entry_def max_def split: split_if_asm)
next
  case TryCatch thus ?case using max_stack1
    by(fastsimp simp add: match_ex_table_append matches_ex_entry_def max_def split: split_if_asm)
qed(fastsimp simp add: match_ex_table_append)+

lemma bisim1_list1_max_stack:
  assumes bisim: "bisim1_list1 P h ex exs xcp ((stk, loc, C, M, pc) # frs')"
  and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
  shows "length stk \<le> max_stack body"
using bisim
proof(cases)
  case bl1_Normal thus ?thesis using sees
    by(cases ex)(fastsimp dest: sees_method_fun bisim1_max_stack)
qed(simp_all)


lemma match_ex_table_compxE2_pc': 
  "match_ex_table P a pc (compxE2 e pc' d') = \<lfloor>(pc'', d'')\<rfloor> \<Longrightarrow> pc'' < pc' + length (compE2 e)"
  and match_ex_table_compxEs2_pc':
  "match_ex_table P a pc (compxEs2 es pc' d') = \<lfloor>(pc'', d'')\<rfloor> \<Longrightarrow> pc'' < pc' + length (compEs2 es)"
proof(induct e and es arbitrary: pc' d' and pc' d')
  case Synchronized thus ?case
    by(fastsimp simp add: match_ex_table_append matches_ex_entry_def split: split_if_asm)
next
  case TryCatch thus ?case
    by(fastsimp simp add: match_ex_table_append matches_ex_entry_def split: split_if_asm)
qed(fastsimp simp add: match_ex_table_append)+


lemma \<tau>moves1_map_Val_ThrowD [simp]: "\<tau>moves1 (map Val vs @ Throw a # es) = False"
by(induct vs) (fastsimp elim: \<tau>moves1.cases)+


lemma no_reds_map_Val_Throw [simp]:
  "extTA,P \<turnstile> \<langle>map Val vs @ Throw a # es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> = False"
by(induct vs arbitrary: es')(auto elim: reds.cases)

lemma red_\<tau>move1_heap_unchanged: "\<lbrakk> extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move1 e \<rbrakk> \<Longrightarrow> hp s' = hp s"
  and red_\<tau>moves1_heap_unchanged: "\<lbrakk> extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves1 es \<rbrakk> \<Longrightarrow> hp s' = hp s"
apply(induct rule: red_reds.inducts)
apply(fastsimp simp add: map_eq_append_conv)+
done

lemma red_changes: "extTA,P \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e, s\<rangle> \<Longrightarrow> False"
  and reds_changes: "extTA,P \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es, s\<rangle> \<Longrightarrow> False"
proof(induct e'\<equiv>e s ta e s and es'\<equiv>es s ta es s rule: red_reds.inducts)
  case (RedCallExternal s a T M vs ta va h' ta' e' s')
  thus ?case by(cases va) auto
qed(auto)

lemma bisim_\<tau>move1_inv: "bisim Vs e e' xs \<Longrightarrow> \<tau>move1 e = \<tau>move1 e'"
  and bisims_\<tau>moves1_inv: "bisims Vs es es' xs \<Longrightarrow> \<tau>moves1 es = \<tau>moves1 es'"
proof(induct rule: bisim_bisims.inducts)
  case bisimCallParams thus ?case
    by(fastsimp intro: \<tau>move1_\<tau>moves1.intros simp add: bisims_map_Val_Throw bisims_map_Val_Throw2)
qed(fastsimp intro: \<tau>move1_\<tau>moves1.intros)+

lemma bisim_red0_Red1_\<tau>Move1_inv:
  "bisim_red0_Red1 ((ex, exs), h) ((ex', exs'), h') \<Longrightarrow> \<tau>Move1 (ex, exs) = \<tau>Move1 (ex', exs')"
by(auto simp add: bisim_red0_Red1_def dest: bisim_\<tau>move1_inv elim: bisim_list.cases)

lemma inline_call_\<tau>move1_inv: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>move1 (inline_call {V:T=vo; e'}\<^bsub>cr\<^esub> e) = \<tau>move1 {V:T=vo; e'}\<^bsub>cr\<^esub>"
  and inline_calls_\<tau>moves1_inv: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>moves1 (inline_calls {V:T=vo; e'}\<^bsub>cr\<^esub> es) = \<tau>move1 {V:T=vo; e'}\<^bsub>cr\<^esub>"
proof(induct e and es)
  case BinOp thus ?case by(auto intro: \<tau>move1_\<tau>moves1.intros) fastsimp+
next
  case AAcc thus ?case by(auto intro: \<tau>move1_\<tau>moves1.intros) fastsimp+
next
  case AAss thus ?case by(auto intro: \<tau>move1_\<tau>moves1.intros) fastsimp+
next
  case FAss thus ?case by(auto intro: \<tau>move1_\<tau>moves1.intros) fastsimp+
next
  case Call thus ?case by(auto intro: \<tau>move1_\<tau>moves1.intros) fastsimp+
next
  case Cons_exp thus ?case by(auto intro: \<tau>move1_\<tau>moves1.intros) fastsimp+ 
qed(fastsimp intro: \<tau>move1_\<tau>moves1.intros)+

lemma fold_exs_\<tau>move1_inv:
  "\<lbrakk> fold_exs P h (e', xs') exs = (e, xs); is_call_list h (map fst exs); noRetBlocks (map fst exs) \<rbrakk> \<Longrightarrow> \<tau>Move1 ((e', xs'), exs) = \<tau>move1 e"
proof(induct exs arbitrary: e' xs' e xs)
  case Nil thus ?case by clarsimp
next
  case (Cons ex exs e' xs' e xs)
  note IH = `\<And>e' xs' e xs. \<lbrakk>fold_exs P h (e', xs') exs = (e, xs); is_call_list h (map fst exs); noRetBlocks (map fst exs) \<rbrakk>
             \<Longrightarrow> \<tau>Move1 ((e', xs'), exs) = \<tau>move1 e`
  from `is_call_list h (map fst (ex # exs))` obtain aMvs
    where call: "call (fst ex) = \<lfloor>aMvs\<rfloor>" and calls: "is_call_list h (map fst exs)" by auto
  from `noRetBlocks (map fst (ex # exs))`
  have nrb: "noRetBlock (fst ex)" and nrbs: "noRetBlocks (map fst exs)" by auto
  let ?e'' = "{this:Class (fst (method P (case the (h (fst (the (call (fst ex))))) of Obj C fs \<Rightarrow> C | Arr ty el \<Rightarrow> arbitrary) (fst (snd (the (call (fst ex)))))))=xs' this; e'}\<^bsub>True\<^esub>"
  let ?e' = "inline_call ?e'' (fst ex)"
  from `fold_exs P h (e', xs') (ex # exs) = (e, xs)`
  have "fold_exs P h (?e', snd ex) exs = (e, xs)" by simp
  hence "\<tau>Move1 ((?e', snd ex), exs) = \<tau>move1 e" using calls nrbs by(rule IH)
  with call have "\<tau>move1 e = \<tau>move1 ?e'" by auto
  also from call have "\<tau>move1 ?e' = \<tau>move1 ?e''" by(rule inline_call_\<tau>move1_inv)
  also from nrb have "\<tau>move1 ?e'' = \<tau>move1 e'" by(auto intro: \<tau>move1Block)
  finally show ?case by simp
qed  

lemma bisim_red_red0_\<tau>Move_inv:
  "bisim_red_red0 P ((e, x), h) (exs, h') \<Longrightarrow> \<tau>Move1 exs = \<tau>move1 e"
apply(erule bisim_red_red0.cases)
apply clarify
apply(drule (1) fold_exs_\<tau>move1_inv)
apply auto
done

lemma red0_final_wf:
  "final_thread_wf final_expr0 (mred0 P)"
by(unfold_locales)(auto elim!: red0.cases)

interpretation red0_final_wf: final_thread_wf final_expr0 "mred0 P"
by(rule red0_final_wf)

interpretation red_\<tau>mthr: \<tau>multithreaded final_expr "mred P" \<tau>MOVE
by(unfold_locales)

interpretation red0_\<tau>mthr: \<tau>multithreaded final_expr0 "mred0 P" \<tau>MOVE0
by(unfold_locales)

lemma red_\<tau>mthr_wf: "\<tau>multithreaded_wf (mred P) \<tau>MOVE wfs"
proof
  fix x1 m1 ta1 x1' m1'
  assume "mred P (x1, m1) ta1 (x1', m1')" "\<tau>MOVE (x1, m1) ta1 (x1', m1')"
  thus "m1 = m1'" by(auto dest: red_\<tau>move1_heap_unchanged)
next
  fix s assume "mred P s \<epsilon> s"
  thus "\<tau>MOVE s \<epsilon> s" by(auto dest: red_changes)
qed simp

interpretation red_\<tau>mthr_wf: \<tau>multithreaded_wf final_expr "mred P" \<tau>MOVE wfs
by(rule red_\<tau>mthr_wf)

lemma red0_\<tau>mthr_wf: "\<tau>multithreaded_wf (mred0 P) \<tau>MOVE0 wfs"
proof
  fix x1 m1 ta1 x1' m1'
  assume "mred0 P (x1, m1) ta1 (x1', m1')" "\<tau>MOVE0 (x1, m1) ta1 (x1', m1')"
  thus "m1 = m1'" by(cases x1)(fastsimp elim!: red0.cases dest: red_\<tau>move1_heap_unchanged)
next
  fix s
  assume "mred0 P s \<epsilon> s" hence False
    by(cases s)(auto elim!: red0.cases intro: red_changes)
  thus "\<tau>MOVE0 s \<epsilon> s" ..
qed simp

interpretation red0_\<tau>mthr_wf: \<tau>multithreaded_wf final_expr0 "mred0 P" \<tau>MOVE0 wfs
by(rule red0_\<tau>mthr_wf)

interpretation red_red0_FWwbase:
  FWweak_bisimulation_base final_expr "mred P" final_expr0 "mred0 P" "bisim_red_red0 P" \<tau>MOVE \<tau>MOVE0
by(unfold_locales)

interpretation red0_Red1_FWwbase:
  FWweak_bisimulation_base final_expr0 "mred0 P" final_expr1 "mred1 (compP1 P)" "bisim_red0_Red1" \<tau>MOVE0 \<tau>MOVE1
by(unfold_locales)

lemma red0_Red1_\<tau>inv: "\<tau>inv (mred0 P) (mred1 (compP1 P)) bisim_red0_Red1 (ta_bisim bisim_red0_Red1) \<tau>MOVE0 \<tau>MOVE1"
proof
  fix s1 s2 ta1 s1' ta2 s2'
  assume bisim: "bisim_red0_Red1 s1 s2"
    and "mred0 P s1 ta1 s1'" "mred1 (compP1 P) s2 ta2 s2'"
    and tasim: "ta_bisim bisim_red0_Red1 ta1 ta2"
    obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1) auto
    obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2) auto
    from bisim s1 s2 tasim show "\<tau>MOVE0 s1 ta1 s1' = \<tau>MOVE1 s2 ta2 s2'" by(auto dest: bisim_red0_Red1_\<tau>Move1_inv)
qed

interpretation red0_Red1_\<tau>inv:
  \<tau>inv "mred0 P" "mred1 (compP1 P)" bisim_red0_Red1 "ta_bisim bisim_red0_Red1" \<tau>MOVE0 \<tau>MOVE1
by(intro red0_Red1_\<tau>inv)+

lemma red0_Red1_FWlift:
  "FWweak_bisimulation_lift (mred0 P) (mred1 (compP1 P)) bisim_red0_Red1 \<tau>MOVE0 \<tau>MOVE1"
by(unfold_locales)

interpretation red0_Red1_FWlift:
  FWweak_bisimulation_lift final_expr0 "mred0 P" final_expr1 "mred1 (compP1 P)" bisim_red0_Red1 \<tau>MOVE0 \<tau>MOVE1
by(intro red0_Red1_FWlift)

interpretation red0_Red1_m\<tau>inv:
  \<tau>inv "red0_mthr.redT P" "Red1_mthr.redT (compP1 P)" red0_Red1_FWbase.mbisim
       red0_Red1_FWbase.mta_bisim red0_Red1_FWwbase.m\<tau>move1 red0_Red1_FWwbase.m\<tau>move2
by(intro red0_Red1_FWlift.\<tau>inv_lift)

lemma red0_Red1_m\<tau>inv':
  "\<tau>inv (red0_mthr.redT P) (Red1_mthr.redT (compP1 P)) mbisim_red0_Red1
        red0_Red1_FWbase.mta_bisim red0_Red1_FWwbase.m\<tau>move1 red0_Red1_FWwbase.m\<tau>move2"
proof
  fix s1 s2 ta1 s1' ta2 s2'
  assume bisim: "mbisim_red0_Red1 s1 s2" and r1: "red0_mthr.redT P s1 ta1 s1'"
    and r2: "Red1_mthr.redT (compP1 P) s2 ta2 s2'" and bisim': "mbisim_red0_Red1 s1' s2'"
    and tasim: "red0_Red1_FWbase.mta_bisim ta1 ta2"
  from bisim bisim' have "red0_Red1_FWbase.mbisim s1 s2" "red0_Red1_FWbase.mbisim s1' s2'" by blast+
  with r1 r2 tasim show "red0_Red1_FWwbase.m\<tau>move1 s1 ta1 s1' = red0_Red1_FWwbase.m\<tau>move2 s2 ta2 s2'"
    by -(rule red0_Red1_FWlift.mthr.\<tau>inv)
qed

interpretation red0_Red1_m\<tau>inv':
  \<tau>inv "red0_mthr.redT P" "Red1_mthr.redT (compP1 P)" mbisim_red0_Red1
       red0_Red1_FWbase.mta_bisim red0_Red1_FWwbase.m\<tau>move1 red0_Red1_FWwbase.m\<tau>move2
by(intro red0_Red1_m\<tau>inv')

lemma red0_Red1_bisim_into_weak:
  assumes wf: "wf_J_prog P"
  shows "bisimulation_into_weak (red0_mthr.redT P) (Red1_mthr.redT (compP1 P)) mbisim_red0_Red1
                                red0_Red1_FWbase.mta_bisim red0_Red1_FWwbase.m\<tau>move1 red0_Red1_FWwbase.m\<tau>move2"
proof -
  interpret bisimulation "red0_mthr.redT P" "Red1_mthr.redT (compP1 P)" mbisim_red0_Red1 "red0_Red1_FWbase.mta_bisim" 
    by(rule red0_Red1_FWbisim[OF wf])
  show ?thesis by(unfold_locales)
qed


lemma red_red0_\<tau>inv:
  "\<tau>inv (mred P) (mred0 P) (bisim_red_red0 P) (ta_bisim (bisim_red_red0 P)) \<tau>MOVE \<tau>MOVE0"
proof
  fix s1 s2 tl1 s1' tl2 s2'
  assume "bisim_red_red0 P s1 s2" "ta_bisim (bisim_red_red0 P) tl1 tl2"
    and "mred P s1 tl1 s1'"
  thus "\<tau>MOVE s1 tl1 s1' = \<tau>MOVE0 s2 tl2 s2'"
    by(cases s1, cases s2)(auto dest: bisim_red_red0_\<tau>Move_inv)
qed

interpretation red_red0_\<tau>inv:
  \<tau>inv "mred P" "mred0 P" "bisim_red_red0 P" "ta_bisim (bisim_red_red0 P)" \<tau>MOVE \<tau>MOVE0
by(intro red_red0_\<tau>inv)

lemma red_red0_FWlift:
  "FWweak_bisimulation_lift (mred P) (mred0 P) (bisim_red_red0 P) \<tau>MOVE \<tau>MOVE0"
by(unfold_locales)

interpretation red_red0_FWlift:
  FWweak_bisimulation_lift final_expr "mred P" final_expr0 "mred0 P" "bisim_red_red0 P" \<tau>MOVE \<tau>MOVE0
by(intro red_red0_FWlift)

interpretation red_red0_m\<tau>inv:
  \<tau>inv "red_mthr.redT P" "red0_mthr.redT P" "red_red0_FWbase.mbisim P"
       "red_red0_FWbase.mta_bisim P" red_red0_FWwbase.m\<tau>move1 red_red0_FWwbase.m\<tau>move2
by(intro red_red0_FWlift.\<tau>inv_lift)

lemma red_red0_bisim_into_weak:
  assumes wf: "wf_J_prog P"
  shows "bisimulation_into_weak (red_mthr.redT P) (red0_mthr.redT P) (red_red0_FWbase.mbisim P)
                                (red_red0_FWbase.mta_bisim P) red_red0_FWwbase.m\<tau>move1 red_red0_FWwbase.m\<tau>move2"
proof -
  interpret fwb: FWbisimulation "final_expr" "mred P" "final_expr0" "mred0 P" "bisim_red_red0 P"
    by(rule red_red0_FWbisim[OF wf])
  interpret bisimulation "red_mthr.redT P" "red0_mthr.redT P" "red_red0_FWbase.mbisim P" "red_red0_FWbase.mta_bisim P"
    by(rule fwb.mbisim_bisimulation)
  show ?thesis by(unfold_locales)
qed

lemma mexecd_final_wf: "final_thread_wf JVM_final (mexecd P)"
by(unfold_locales)(auto elim: jvmd_NormalE)

interpretation mexecd_final_wf: final_thread_wf JVM_final "mexecd P"
by(rule mexecd_final_wf)

lemma Red1_mexecd_FWbase:
  "FWbisimulation_base (mred1 P) (mexecd (compP2 P))"
by unfold_locales

interpretation Red1_mexecd_FWbase:
  FWbisimulation_base final_expr1 "mred1 P" JVM_final "mexecd (compP2 P)" "wbisim1 P"
by(rule Red1_mexecd_FWbase)

lemma mexecd_exec_1': "P \<turnstile> Normal s -ta-jvmd\<rightarrow> Normal s' \<Longrightarrow> exec_1' P s ta s'"
apply(cases s')
apply(erule jvmd_NormalE)
apply(case_tac xcp)
apply(auto simp add: check_def intro: exec_1'.intros simp del: exception_step.simps)
done

interpretation mexecd_\<tau>mthr: \<tau>multithreaded JVM_final "mexecd (compP2 P)" "\<tau>MOVE2 P"
by(unfold_locales)

lemma mexecd_\<tau>mthr_wf: "\<tau>multithreaded_wf (mexecd (compP2 P)) (\<tau>MOVE2 P) (\<lambda>s2. \<exists>s1. wbisim1 P s1 s2)"
proof
  fix x2 m2 ta2 x2' m2'
  assume "\<exists>s1. wbisim1 P s1 (x2, m2)" "mexecd (compP2 P) (x2, m2) ta2 (x2', m2')" 
    and "\<tau>MOVE2 P (x2, m2) ta2 (x2', m2')"
  thus "m2 = m2'" by(cases x2, cases x2')(fastsimp dest: \<tau>exec_1_heap_unchanged mexecd_exec_1')
next
  fix s assume "mexecd (compP2 P) s \<epsilon> s" and "\<exists>s1. wbisim1 P s1 s"
  thus "\<tau>MOVE2 P s \<epsilon> s" by(cases s)(fastsimp dest: exec_1_changes mexecd_exec_1')
qed simp

interpretation mexecd_\<tau>mthr_wf:
  \<tau>multithreaded_wf JVM_final "mexecd (compP2 P)" "\<tau>MOVE2 P" "\<lambda>s2. \<exists>s1. wbisim1 P s1 s2"
by(rule mexecd_\<tau>mthr_wf)


lemma bisim_exec_1'_mexecd:
  assumes wbisim: "wbisim1 P ((ex, exs), h) ((xcp, frs), h)"
  and exec: "exec_1' (compP2 P) (xcp, h, frs) ta (xcp', h', frs')"
  shows "compP2 P \<turnstile> Normal (xcp, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs')"
proof -
  from wbisim exec obtain stk loc C M pc frs'' where frs: "frs = (stk, loc, C, M, pc) # frs''"
    by(cases frs) (fastsimp elim: exec_1'.cases bisim1_list1.cases)+
  with wbisim have bisim: "bisim1_list1 P h ex exs xcp ((stk, loc, C, M, pc) # frs'')" by simp 
  hence "P \<turnstile> C has M" by(auto intro: bisim1_list1_has_methodD)
  moreover then obtain Ts T body D where sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=body in D" by(auto simp add: has_method_def)
  from sees_method_compP[OF this, where f=compMb2]
  have sees2: "compP2 P \<turnstile> C sees M:Ts\<rightarrow>T=(max_stack body, max_vars body, compE2 body @ [Return], compxE2 body 0 0) in D"
    by(simp add: compMb2_def compP2_def)
  moreover from bisim sees have "length stk \<le> max_stack body" unfolding frs
    by(rule bisim1_list1_max_stack)
  moreover {
    assume "pc < length (compE2 body)" "xcp = None"
    with exec sees2 have "check_instr (compE2 body ! pc) (compP2 P) h stk loc C M pc frs''"
      unfolding frs by(auto elim!: exec_1'.cases) }
  moreover from bisim have "pc \<le> length (compE2 body)"
  proof cases
    case bl1_Normal with sees show ?thesis
      by(cases ex)(fastsimp dest: bisim1_pc_length_compE2 sees_method_fun)
  qed(simp_all)
  moreover { assume pc: "pc = length (compE2 body)"
    from bisim have "stk \<noteq> [] \<and> (frs'' \<noteq> [] \<longrightarrow> compP2 P,h \<turnstile> hd stk :\<le> T)"
    proof cases
      case (bl1_Normal Ca Ma Ts exsa frs T' body' D exa stka loca pca XCP)
      hence bisim1: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (fst ex, snd ex) \<leftrightarrow> (stk, loca, length (compE2 (blocks1 (Suc 0) Ts body)), xcp)"
	and [simp]: "stka = stk" "loca = loc" "Ca = C" "Ma = M" "pca = pc" "frs = frs''" "body = body'" "XCP = xcp"
	and bl: "bisim1_list P h C M (length Ts) exs frs''"
	and exs: "exsconf P h T ex"
	using pc sees by(auto dest: sees_method_fun)
      then obtain v where stk: "stk = [v]" by(cases ex)(clarify, drule bisim1_pc_length_compE2D, auto)
      show ?thesis
      proof(cases xcp)
	case None
	with bisim1 exs stk have "P,h \<turnstile> v :\<le> T"
	  by(cases ex, clarify)(erule exsconf.cases, drule bisim1_length_compE2_WTrt_eq, auto simp add: conf_def)
	thus ?thesis using stk by(auto simp add: neq_Nil_conv compP2_def)
      next
	case Some
	with bisim1_pc_length_compE2D[OF bisim1] have False by simp
	thus ?thesis ..
      qed
    qed simp_all }
  ultimately have "check (compP2 P) (xcp, h, frs)" unfolding frs
    by(simp add: check_def split: list.split)
  moreover from exec have "(ta, xcp', h', frs') \<in> set (exec (compP2 P) (xcp, h, frs))"
    by(force elim!: exec_1'.cases)
  ultimately show ?thesis by(auto intro: exec_1_d_NormalI simp add: exec_d_def)
qed

lemma exec_1'_\<tau>moves_into_mexecd:
  assumes wf: "wf_J1_prog P"
  and bisim: "wbisim1 P s1 s2"
  and exec: "(\<lambda>s2 s2'. \<exists>tl2. mexec_1' (compP2 P) s2 tl2 s2' \<and> \<tau>MOVE2 P s2 tl2 s2')\<^sup>*\<^sup>* s2 s2'"
  shows "(\<lambda>s2 s2'. \<exists>tl2. mexecd (compP2 P) s2 tl2 s2' \<and> \<tau>MOVE2 P s2 tl2 s2')\<^sup>*\<^sup>* s2 s2'"
proof -
  interpret FWweak_bisimulation final_expr1 "mred1 P" JVM_final "mexec_1' (compP2 P)" "wbisim1 P" \<tau>MOVE1 "\<tau>MOVE2 P"
    using wf by(simp_all add: Red1_exec1_FWwbisim)
  from exec bisim show ?thesis
  proof(induct arbitrary: s1 rule: converse_rtranclp_induct[case_names base step])
    case base thus ?case by blast
  next
    case (step s2 s2'')
    from `\<exists>tl2. mexec_1' (compP2 P) s2 tl2 s2'' \<and> \<tau>MOVE2 P s2 tl2 s2''`
    obtain tl2 where exec: "mexec_1' (compP2 P) s2 tl2 s2''"
      and \<tau>: "\<tau>MOVE2 P s2 tl2 s2''" by blast
    from exec `wbisim1 P s1 s2` have red: "mexecd (compP2 P) s2 tl2 s2''"
      by(cases s1, cases s2, cases s2'')(auto intro: bisim_exec_1'_mexecd)
    from `wbisim1 P s1 s2` exec obtain s1' where "wbisim1 P s1' s2''" by(rule bisim_inv2)
    from `wbisim1 P s1' s2'' \<Longrightarrow> (\<lambda>s2 s2'. \<exists>tl2. mexecd (compP2 P) s2 tl2 s2' \<and> \<tau>MOVE2 P s2 tl2 s2')\<^sup>*\<^sup>* s2'' s2'`[OF this] red \<tau>
    show ?case by(blast intro: converse_rtranclp_into_rtranclp)
  qed
qed

lemma mexecd_\<tau>moves_into_exec_1':
  assumes wf: "wf_J1_prog P"
  and exec: "(\<lambda>s2 s2'. \<exists>tl2. mexecd (compP2 P) s2 tl2 s2' \<and> \<tau>MOVE2 P s2 tl2 s2')\<^sup>*\<^sup>* s2 s2'"
  shows "(\<lambda>s2 s2'. \<exists>tl2. mexec_1' (compP2 P) s2 tl2 s2' \<and> \<tau>MOVE2 P s2 tl2 s2')\<^sup>*\<^sup>* s2 s2'"
using exec
proof(induct arbitrary: s1 rule: converse_rtranclp_induct[case_names base step])
  case base thus ?case by blast
next
  case (step s2 s2'') 
  from `\<exists>tl2. mexecd (compP2 P) s2 tl2 s2'' \<and> \<tau>MOVE2 P s2 tl2 s2''`
  obtain tl2 where exec: "mexecd (compP2 P) s2 tl2 s2''"
    and \<tau>: "\<tau>MOVE2 P s2 tl2 s2''" by blast
  from exec have exec': "mexec_1' (compP2 P) s2 tl2 s2''" by(auto intro: mexecd_exec_1')
  with `(\<lambda>s2 s2'. \<exists>tl2. mexec_1' (compP2 P) s2 tl2 s2' \<and> \<tau>MOVE2 P s2 tl2 s2')\<^sup>*\<^sup>* s2'' s2'` exec' \<tau>
  show ?case by(blast intro: converse_rtranclp_into_rtranclp)
qed

lemma Red1_mexecd_weak_bisim: 
  assumes wf: "wf_J1_prog P"
  shows "weak_bisimulation (mred1 P) (mexecd (compP2 P)) (wbisim1 P) (ta_bisim (wbisim1 P)) \<tau>MOVE1 (\<tau>MOVE2 P)"
proof -
  let ?\<tau>exec' = "(\<lambda>s2 s2'. \<exists>tl2. mexec_1' (compP2 P) s2 tl2 s2' \<and> \<tau>MOVE2 P s2 tl2 s2')\<^sup>*\<^sup>*"
  let ?\<tau>exec = "(\<lambda>s2 s2'. \<exists>tl2. mexecd (compP2 P) s2 tl2 s2' \<and> \<tau>MOVE2 P s2 tl2 s2')\<^sup>*\<^sup>*"
  let ?\<tau>red = "(\<lambda>s1 s1'. \<exists>tl1. mred1 P s1 tl1 s1' \<and> \<tau>MOVE1 s1 tl1 s1')\<^sup>*\<^sup>*"
  interpret weak_bisimulation "mred1 P" "mexec_1' (compP2 P)" "wbisim1 P" "ta_bisim (wbisim1 P)" \<tau>MOVE1 "\<tau>MOVE2 P"
    by(intro Red1_exec1_weak_bisim[OF wf])
  interpret FWweak_bisimulation final_expr1 "mred1 P" JVM_final "mexec_1' (compP2 P)" "wbisim1 P" \<tau>MOVE1 "\<tau>MOVE2 P"
    using wf by(simp_all add: Red1_exec1_FWwbisim)
  show ?thesis
  proof
    fix s1 s2 tl1 s1'
    assume wbisim: "wbisim1 P s1 s2" and red: "mred1 P s1 tl1 s1'" and \<tau>: "\<tau>MOVE1 s1 tl1 s1'"
    from simulation_silent1[OF this] obtain s2'
      where exec: "?\<tau>exec' s2 s2'" and wbisim': "wbisim1 P s1' s2'"
      unfolding Red1_exec1_wbase.trsys2.\<tau>moves_def by blast
    from exec_1'_\<tau>moves_into_mexecd[OF wf wbisim exec] wbisim'
    show "\<exists>s2'. \<tau>trsys.\<tau>moves (mexecd (compP2 P)) (\<tau>MOVE2 P) s2 s2' \<and> wbisim1 P s1' s2'"
      unfolding mexecd_\<tau>mthr.\<tau>moves_def by blast
  next
    fix s1 s2 tl2 s2'
    assume wbisim: "wbisim1 P s1 s2" and mexec: "mexecd (compP2 P) s2 tl2 s2'" and \<tau>: "\<tau>MOVE2 P s2 tl2 s2'"
    from mexec have "mexec_1' (compP2 P) s2 tl2 s2'" by(auto intro: mexecd_exec_1')
    with wbisim show "\<exists>s1'. \<tau>trsys.\<tau>moves (mred1 P) \<tau>MOVE1 s1 s1' \<and> wbisim1 P s1' s2'"
      using \<tau> by(rule simulation_silent2)
  next
    fix s1 s2 tl1 s1'
    assume bisim: "wbisim1 P s1 s2" and "mred1 P s1 tl1 s1'" and "\<not> \<tau>MOVE1 s1 tl1 s1'"
    from simulation1[OF this] obtain s2' s2'' tl2
      where \<tau>exec: "?\<tau>exec' s2 s2'" and exec: "mexec_1' (compP2 P) s2' tl2 s2''" and \<tau>: "\<not> \<tau>MOVE2 P s2' tl2 s2''"
      and bisim': "wbisim1 P s1' s2''" "ta_bisim (wbisim1 P) tl1 tl2"
      unfolding Red1_exec1_wbase.trsys2.\<tau>moves_def by blast
    from bisim_inv_\<tau>s2[OF bisim] \<tau>exec obtain s1''
      where bisim'': "wbisim1 P s1'' s2'" by(simp del: split_beta) blast
    with exec have "mexecd (compP2 P) s2' tl2 s2''"
      by(cases s1'', cases s2')(auto intro: bisim_exec_1'_mexecd)
    with exec_1'_\<tau>moves_into_mexecd[OF wf bisim \<tau>exec] \<tau> bisim'
    show " \<exists>s2' s2'' tl2. \<tau>trsys.\<tau>moves (mexecd (compP2 P)) (\<tau>MOVE2 P) s2 s2' \<and>
                          mexecd (compP2 P) s2' tl2 s2'' \<and> \<not> \<tau>MOVE2 P s2' tl2 s2'' \<and>
                          wbisim1 P s1' s2'' \<and> ta_bisim (wbisim1 P) tl1 tl2"
      unfolding mexecd_\<tau>mthr.\<tau>moves_def by blast
  next
    fix s1 s2 tl2 s2'
    assume "wbisim1 P s1 s2" "mexecd (compP2 P) s2 tl2 s2'" "\<not> \<tau>MOVE2 P s2 tl2 s2'"
    thus "\<exists>s1' s1'' tl1. \<tau>trsys.\<tau>moves (mred1 P) \<tau>MOVE1 s1 s1' \<and> mred1 P s1' tl1 s1'' \<and>
                        \<not> \<tau>MOVE1 s1' tl1 s1'' \<and> wbisim1 P s1'' s2' \<and> ta_bisim (wbisim1 P) tl1 tl2"
      by -(erule simulation2, auto intro: mexecd_exec_1')
  qed
qed

theorem Red1_mexecd_FWweak_bisim:
  assumes wf: "wf_J1_prog P"
  shows "FWweak_bisimulation final_expr1 (mred1 P) JVM_final (mexecd (compP2 P)) (wbisim1 P) \<tau>MOVE1 (\<tau>MOVE2 P)"
proof -
  interpret weak_bisimulation "mred1 P" "mexecd (compP2 P)" "wbisim1 P" "ta_bisim (wbisim1 P)" \<tau>MOVE1 "\<tau>MOVE2 P"
    by(intro Red1_mexecd_weak_bisim[OF wf])
  interpret fwb': FWweak_bisimulation final_expr1 "mred1 P" JVM_final "mexec_1' (compP2 P)" "wbisim1 P" \<tau>MOVE1 "\<tau>MOVE2 P"
    by(intro Red1_exec1_FWwbisim[OF wf])
  let ?\<tau>exec' = "(\<lambda>s2 s2'. mexec_1' (compP2 P) s2 \<epsilon> s2' \<and> \<tau>MOVE2 P s2 \<epsilon> s2')\<^sup>*\<^sup>*"
  let ?\<tau>exec = "(\<lambda>s2 s2'. mexecd (compP2 P) s2 \<epsilon> s2' \<and> \<tau>MOVE2 P s2 \<epsilon> s2')\<^sup>*\<^sup>*"
  let ?\<tau>red = "(\<lambda>s1 s1'. mred1 P s1 \<epsilon> s1' \<and> \<tau>MOVE1 s1 \<epsilon> s1')\<^sup>*\<^sup>*"
  show ?thesis
  proof
    fix x1 m1 x2 m2
    assume bisim: "wbisim1 P (x1, m1) (x2, m2)" 
    thus "final_expr1 x1 = JVM_final x2" by(rule fwb'.bisim_final)
  next
    fix x m1 xx m2 x1 x2 x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume bisim1: "wbisim1 P (x, m1) (xx, m2)" and bisim2: "wbisim1 P (x1, m1) (x2, m2)"
      and red1: "?\<tau>red (x1, m1) (x1', m1)"
      and red2: "mred1 P (x1', m1) ta1 (x1'', m1')"
      and \<tau>1: "\<not> \<tau>MOVE1 (x1', m1) ta1 (x1'', m1')"
      and exec1: "?\<tau>exec (x2, m2) (x2', m2)"
      and exec2: "mexecd (compP2 P) (x2', m2) ta2 (x2'', m2')"
      and \<tau>2: "\<not> \<tau>MOVE2 P (x2', m2) ta2 (x2'', m2')"
      and bisim': "wbisim1 P (x1'', m1') (x2'', m2')" "ta_bisim (wbisim1 P) ta1 ta2"
    from exec2 have "mexec_1' (compP2 P) (x2', m2) ta2 (x2'', m2')" by(auto intro: mexecd_exec_1')
    moreover from exec1 mexecd_\<tau>moves_into_exec_1'[OF wf]
    have "?\<tau>exec' (x2, m2) (x2', m2)" by(simp del: split_beta)
    ultimately show "wbisim1 P (x, m1') (xx, m2')"
      using bisim1 bisim2 red1 red2 \<tau>1 \<tau>2 bisim' by-(rule fwb'.bisim_inv_red_other, simp_all)
  qed
qed

theorem bisimJ2JVM_weak_bisim:
  assumes wf: "wf_J_prog P"
  shows "weak_bisimulation (mredT P) (execd_mthr.redT (J2JVM P)) (bisimJ2JVM P) (tlsimJ2JVM P) 
                           red_red0_FWwbase.m\<tau>move1 (Red1_exec1_FWwbase.m\<tau>move2 (compP1 P))"
proof -
  interpret b0: bisimulation_into_weak "red_mthr.redT P" "red0_mthr.redT P" "red_red0_FWbase.mbisim P"
                                    "red_red0_FWbase.mta_bisim P" red_red0_FWwbase.m\<tau>move1 red_red0_FWwbase.m\<tau>move2
    by(intro red_red0_bisim_into_weak[OF wf])
  interpret b01: bisimulation_into_weak "red0_mthr.redT P" "Red1_mthr.redT (compP1 P)" mbisim_red0_Red1
                                      red0_Red1_FWbase.mta_bisim red0_Red1_FWwbase.m\<tau>move1 red0_Red1_FWwbase.m\<tau>move2
    by(intro red0_Red1_bisim_into_weak[OF wf])
  interpret b12: FWweak_bisimulation final_expr1 "mred1 (compP1 P)" JVM_final "mexecd (compP2 (compP1 P))"
                                   "wbisim1 (compP1 P)" \<tau>MOVE1 "\<tau>MOVE2 (compP1 P)"
    using compP1_pres_wf[OF wf] by(intro Red1_mexecd_FWweak_bisim)

  show ?thesis unfolding bisimJ2JVM_def tlsimJ2JVM_def J2JVM_def o_def
    by(blast intro: weak_bisimulation_compose b0.weak_bisimulation b01.weak_bisimulation b12.mbisim_weak_bisimulation)
qed

lemma bisimJ2JVM_start:
  assumes wf: "wf_J_prog P"
  and sees': "P \<turnstile> D sees M:Ts\<rightarrow>T=(pns,body) in C"
  and vs: "length vs = length pns" and conf: "P,h \<turnstile> vs [:\<le>] Ts" and hconf: "P \<turnstile> h \<surd>"
  and rest: "length rest = max_vars body"
  and ha: "h a = \<lfloor>Obj D fs\<rfloor>"
  shows "bisimJ2JVM P (\<lambda>\<^isup>f None, ([0 \<mapsto> (({this:Class C=\<lfloor>Addr a\<rfloor>; blocks (pns, Ts, vs, body)}\<^bsub>True\<^esub>, empty), no_wait_locks)], h), empty)
                      (\<lambda>\<^isup>f None, ([0 \<mapsto> ((None, [([], Addr a # vs @ rest, C, M, 0)]), no_wait_locks)], h), empty)"
  (is "bisimJ2JVM _ ?s1 ?s4")
unfolding bisimJ2JVM_def
proof(rule bisim_composeI)
  from sees' have sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=(pns,body) in C" by(rule sees_method_idemp)
  from sees_wf_mdecl[OF wf_prog_wwf_prog[OF wf] sees] have wwfCM: "wwf_J_mdecl P C (M, Ts, T, pns, body)"
    and len: "length pns = length Ts" by(auto simp add: wf_mdecl_def)
  from sees_wf_mdecl[OF wf sees] have wfCM: "wf_J_mdecl P C (M, Ts, T, pns, body)" by(auto simp add: wf_mdecl_def)
  let ?s2 = "(\<lambda>\<^isup>f None, ([0 \<mapsto> (((blocks (pns, Ts, vs, body), [this \<mapsto> Addr a]), [(addr a\<bullet>M(map Val vs), empty)]), no_wait_locks)], h), empty)"
  from wwfCM have fvbody: "fv body \<subseteq> {this} \<union> set pns" and pns: "length pns = length Ts" by simp_all
  with vs len have fv: "fv (blocks (pns, Ts, vs, body)) \<subseteq> {this}" by auto
  from wfCM obtain T' where T'subT: "P \<turnstile> T' \<le> T" and wtbody: "P,[this # pns [\<mapsto>] Class C # Ts] \<turnstile> body :: T'" by auto
  from wtbody have nrb: "noRetBlock body" by(rule WT_noRetBlock)
  from wtbody have elbody: "expr_locks body = (\<lambda>l. 0)" by(rule WT_expr_locks)
  hence cisbody: "\<not> contains_insync body" by(auto simp add: contains_insync_conv)
  from wfCM len vs have dabody: "\<D> (blocks (pns, Ts, vs, body)) \<lfloor>{this}\<rfloor>" by auto
  from sees have sees1: "compP1 P \<turnstile> C sees M:Ts\<rightarrow>T = compE1 (this # pns) body in C"
    by(auto dest: sees_method_compP[where f="(\<lambda>(pns, body). compE1 (this # pns) body)"])
  from nrb len vs fv ha sees' show "red_red0_FWbase.mbisim P ?s1 ?s2"
    by(fastsimp split: split_if_asm intro!: bisim_red_red0.intros red_red0_FWbase.mbisimI simp add: noRetBlock_blocks)
  show "(mbisim_red0_Red1 \<circ>\<^isub>B (Red1_exec1_FWbase.mbisim (compP1 P))) ?s2 ?s4"
  proof(rule bisim_composeI)
    let ?e = "blocks1 (Suc 0) Ts (compE1 (this # pns) body)"
    let ?xs = "Addr a # vs @ rest"
    let ?s3 = "(\<lambda>\<^isup>f None, ([0 \<mapsto> (((?e, ?xs), [(addr a\<bullet>M(map Val vs), [])]), no_wait_locks)], h), empty)"
    from fvbody cisbody len vs
    have "bisim [this] (blocks (pns, Ts, vs, body)) (blocks1 (length [this]) Ts (compE1 (this # pns) body)) ?xs"
      by -(rule blocks_bisim, fastsimp+)
    with fv dabody len vs elbody rest show "mbisim_red0_Red1 ?s2 ?s3"
      apply(auto intro!: red0_Red1_FWbase.mbisimI split: split_if_asm)
      apply(auto simp add: bisim_red0_Red1_def blocks1_max_vars lock_oks_def expr_locks_blocks intro!: bisim_list.intros)
      done
    from len vs have "\<B> ?e (Suc 0)" by(auto intro!: B_blocks1 \<B>)
    with elbody nrb have "compP1 P,?e,Suc 0,h \<turnstile> (?e, ?xs) \<leftrightarrow> ([], ?xs, 0, None)"
      by -(rule bisim1_refl, auto simp add: bsok_def)
    moreover from len vs conf sees1 ha rest sees_method_decl_above[OF sees']
    have "exsconf (compP1 P) h T (?e, ?xs)"
      by -(rule exsconf_Call[OF compP1_pres_wf[OF wf]], simp_all add: conf_def)
    ultimately show "Red1_exec1_FWbase.mbisim (compP1 P) ?s3 ?s4" using sees1 hconf sees ha vs pns
      by -(rule Red1_exec1_FWbase.mbisimI, auto split: split_if_asm intro!: bl1_Normal bl1_Nil)
  qed
qed

end