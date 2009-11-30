(*  Title:      JinjaThreads/Compiler/J0Threaded.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Lifting the bisimulation to the multithreaded setting: Jinja smallstep with and without call stacks} *}

theory J0Threaded imports J0Bisim begin

lemma fold_es_eq_finalD:
  "\<lbrakk> fold_es E es = e; list_all is_call es; list_all (-final) (butlast (E # es))\<rbrakk>
  \<Longrightarrow> final_expr0 (E, es) = final e"
proof(induct es arbitrary: E)
  case Nil thus ?case by simp
next
  case Cons thus ?case
    by(simp (no_asm_use) split: split_if_asm)(fastsimp simp add: fun_Compl_def bool_Compl_def is_call_def)+
qed

lemma bisim_red_red0_hext_mono:
  "\<lbrakk> bisim_red_red0 (x, m2) (x', m2); hext m2 m2' \<rbrakk> \<Longrightarrow> bisim_red_red0 (x, m2') (x', m2')"
by(auto elim!: bisim_red_red0.cases del: wf_state.cases wf_state.intros)

lemma bisim_red_red0_final0D:
  "\<lbrakk> bisim_red_red0 (x1, m1) (x2, m2); final_expr0 x2 \<rbrakk> \<Longrightarrow> final_expr x1"
by(erule bisim_red_red0.cases) auto

lemma final_inline_callD: "\<lbrakk> final (inline_call E e); is_call e \<rbrakk> \<Longrightarrow> final E"
by(induct e)(auto simp add: is_call_def split: split_if_asm)


lemma fold_es_finalD: "\<lbrakk> final (fold_es e es); list_all is_call es \<rbrakk> \<Longrightarrow> final e"
by(induct es arbitrary: e)(auto dest: final_inline_callD)

lemma bisim_red_red0_finalD:
  assumes bisim: "bisim_red_red0 (x1, m1) (x2, m2)"
  and "final_expr x1"
  shows "\<exists>x2'. red0_\<tau>mthr.silent_moves P (x2, m2) (x2', m2) \<and> bisim_red_red0 (x1, m1) (x2', m2) \<and> final_expr0 x2'"
using bisim
proof(cases rule: bisim_red_red0.cases)
  fix e' e es h
  assume "(x1, m1) = ((e', empty), h)" "(x2, m2) = ((e, es), h)" "e' = fold_es e es" and wf_state: "wf_state e es"
  hence [simp]: "x1 = (e', empty)" "m1 = h" "x2 = (e, es)" "e' = fold_es e es" "m2 = h" by simp_all
  from `final_expr x1` have "final (fold_es e es)" by simp
  moreover from wf_state have "list_all is_call es" by auto
  ultimately have "red0_\<tau>mthr.silent_moves P ((e, es), h) ((fold_es e es, []), h)"
  proof(induct es arbitrary: e)
    case Nil thus ?case by simp
  next
    case (Cons e' es)
    from `final (fold_es e (e' # es))` have "final (fold_es (inline_call e e') es)" by simp
    moreover from `list_all is_call (e' # es)` have "list_all is_call es" by simp
    ultimately have "red0_\<tau>mthr.silent_moves P ((inline_call e e', es), h) ((fold_es (inline_call e e') es, []), h)"
      by(rule Cons)
    moreover from `final (fold_es e (e' # es))` `list_all is_call (e' # es)`
    have "final e" by(rule fold_es_finalD)
    hence "P \<turnstile>0 \<langle>e/e'#es, h\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e e'/es, h\<rangle>" by(rule red0Return)
    with `final e` have "red0_\<tau>mthr.silent_move P ((e, e'#es), h) ((inline_call e e', es), h)" by auto
    ultimately show ?case by -(erule converse_rtranclp_into_rtranclp, simp)
  qed
  moreover have "bisim_red_red0 ((fold_es e es, empty), h) ((fold_es e es, []), h)"
    using `final (fold_es e es)` by(auto intro!: bisim_red_red0.intros)
  ultimately show ?thesis using `final (fold_es e es)` by auto
qed

lemma red_red0_FWbisim:
  assumes wf: "wwf_J_prog P"
  shows "FWdelay_bisimulation_measure final_expr (mred P) final_expr0 (mred0 P) bisim_red_red0 (\<tau>MOVE P) (\<tau>MOVE0 P) (\<lambda>e e'. False) (\<lambda>((e, es), h) ((e, es'), h). length es < length es')"
proof -
  interpret delay_bisimulation_measure "mred P" "mred0 P" "bisim_red_red0" "ta_bisim0" "\<tau>MOVE P" "\<tau>MOVE0 P"
    "\<lambda>e e'. False" "\<lambda>((e, es), h) ((e, es'), h). length es < length es'"
    by(rule weak_bisimulation_measure_red_red0[OF wf])
  show ?thesis
  proof
    fix s1 s2
    assume "bisim_red_red0 s1 s2" "(\<lambda>(x1, m). final_expr x1) s1"
    moreover obtain x1 m1 where [simp]: "s1 = (x1, m1)" by(cases s1)
    moreover obtain x2 m2 where [simp]: "s2 = (x2, m2)" by(cases s2)
    ultimately have "bisim_red_red0 (x1, m1) (x2, m2)" "final_expr x1" by simp_all
    from bisim_red_red0_finalD[OF this, of P]
    show "\<exists>s2'. red0_\<tau>mthr.silent_moves P s2 s2' \<and> bisim_red_red0 s1 s2' \<and> (\<lambda>(x2, m). final_expr0 x2) s2'" by auto
  next
    fix s1 s2
    assume "bisim_red_red0 s1 s2" "(\<lambda>(x2, m). final_expr0 x2) s2"
    moreover obtain x1 m1 where [simp]: "s1 = (x1, m1)" by(cases s1)
    moreover obtain x2 m2 where [simp]: "s2 = (x2, m2)" by(cases s2)
    ultimately have "bisim_red_red0 (x1, m1) (x2, m2)" "final_expr0 x2" by simp_all
    moreover hence "final_expr x1" by(rule bisim_red_red0_final0D)
    ultimately show "\<exists>s1'. red_\<tau>mthr.silent_moves P s1 s1' \<and> bisim_red_red0 s1' s2 \<and> (\<lambda>(x1, m). final_expr x1) s1'" by auto
  next
    fix x m1 xx m2 x1 x2 x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume b: "bisim_red_red0 (x, m1) (xx, m2)" and bo: "bisim_red_red0 (x1, m1) (x2, m2)"
      and "red_\<tau>mthr.silent_moves P (x1, m1) (x1', m1)"
      and red1: "mred P (x1', m1) ta1 (x1'', m1')" and "\<not> \<tau>MOVE P (x1', m1) ta1 (x1'', m1')"
      and "red0_\<tau>mthr.silent_moves P (x2, m2) (x2', m2)"
      and red2: "mred0 P (x2', m2) ta2 (x2'', m2')" and "\<not> \<tau>MOVE0 P (x2', m2) ta2 (x2'', m2')"
      and bo': "bisim_red_red0 (x1'', m1') (x2'', m2')"
      and tb: "ta_bisim0 ta1 ta2"
    from b have "m1 = m2" by(auto elim: bisim_red_red0.cases)
    moreover from bo' have "m1' = m2'" by(auto elim: bisim_red_red0.cases)
    moreover from red1 have "hext m1 m1'" by(auto simp add: split_beta dest: red_hext_incr)
    ultimately show "bisim_red_red0 (x, m1') (xx, m2')" using b
      by(auto intro: bisim_red_red0_hext_mono)
  qed
qed


end