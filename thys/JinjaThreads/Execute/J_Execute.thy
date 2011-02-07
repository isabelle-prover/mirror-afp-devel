(*  Title:      JinjaThreads/Execute/J_Execute.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Executable semantics for J} *}

theory J_Execute imports
  Round_Robin
  Random_Scheduler
  "../J/Threaded"
  "../MM/SC" 
  "../../Collections/RBTMapImpl"
  "../../Collections/Fifo"
  "../../Collections/ListSetImpl_Invar"
begin

interpretation sc!: 
  J_heap_base
    "sc_empty"
    "sc_new_obj P"
    "sc_new_arr" 
    "sc_typeof_addr"
    "sc_array_length"
    "sc_heap_read"
    "sc_heap_write"
  for P .

abbreviation sc_red :: 
  "(heap external_thread_action \<Rightarrow> ('o, heap) Jinja_thread_action) \<Rightarrow> J_prog \<Rightarrow> thread_id \<Rightarrow> expr \<Rightarrow> heap \<times> locals
                  \<Rightarrow> ('o, heap) Jinja_thread_action \<Rightarrow> expr \<Rightarrow> heap \<times> locals \<Rightarrow> bool"
  ("_,_,_ \<turnstile>sc ((1\<langle>_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,51,0,0,0,0,0,0] 81)
where
  "sc_red extTA P \<equiv> sc.red (TYPE(J_mb)) P extTA P"

fun sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o
where
  "sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P t ((e, xs), h) =
  red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o 
    sc_empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_read_i_i_i_o sc_heap_write_i_i_i_i_o
    (extTA2J P) P t e (h, xs)
  \<guillemotright>= (\<lambda>(ta, e, h, xs). Predicate.single (ta, (e, xs), h))"

abbreviation sc_start_state_refine :: "'m_t \<Rightarrow> (thread_id \<Rightarrow> ('x \<times> addr released_locks) \<Rightarrow> 'm_t \<Rightarrow> 'm_t) \<Rightarrow> 'm_w \<Rightarrow> (cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'md \<Rightarrow> val list \<Rightarrow> 'x) \<Rightarrow> 'md prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> (addr, thread_id, heap, 'm_t, 'm_w) state_refine"
where
  "sc_start_state_refine thr_empty thr_update ws_empty f P \<equiv>
   heap_base.start_state_refine sc_empty (sc_new_obj P) thr_empty thr_update ws_empty f P"

abbreviation sc_J_start_state_refine :: 
  "J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> 
  (addr, thread_id, heap, (thread_id, (expr \<times> locals) \<times> addr released_locks) rbt, (thread_id, addr wait_set_status) rbt) state_refine"
where
  "sc_J_start_state_refine \<equiv> 
   sc_start_state_refine rm_empty rm_update rm_empty (\<lambda>C M Ts T (pns, body) vs. (blocks (this # pns) (Class C # Ts) (Null # vs) body, empty))"

lemma eval_sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o:
  "(\<lambda>t xm ta x'm'. Predicate.eval (sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P t xm) (ta, x'm')) = 
  (\<lambda>t ((e, xs), h) ta ((e', xs'), h'). extTA2J P,P,t \<turnstile>sc \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>)"
by(fastsimp elim!: red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_oE intro!: red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_oI ext SUP1_I simp add: eval_sc_heap_write_i_i_i_i_o eval_sc_heap_read_i_i_i_o)

subsection {* Round-robin scheduler *}

interpretation J_rr!: 
  round_robin_base
    final_expr "sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update 
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_delete rm_iterate rm_sel'
    fifo_\<alpha> fifo_invar fifo_empty fifo_isEmpty fifo_enqueue fifo_dequeue fifo_push
  for P
.

definition sc_rr_J_start_state :: "nat \<Rightarrow> 'm prog \<Rightarrow> thread_id fifo round_robin"
where "sc_rr_J_start_state n0 P = J_rr.round_robin_start n0 (sc_start_tid P)"

definition exec_J_rr ::
  "nat \<Rightarrow> J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> 
  (obs_event list, ((addr, thread_id) locks \<times> ((thread_id, (expr \<times> locals) \<times> addr released_locks) RBT.rbt \<times> heap) \<times>
                    (thread_id, addr wait_set_status) RBT.rbt) diverge) tllist"
where "exec_J_rr n0 P C M vs = J_rr.exec P n0 (sc_rr_J_start_state n0 P) (sc_J_start_state_refine P C M vs)"

interpretation J_rr!:
  round_robin 
    final_expr "sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update 
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_delete rm_iterate rm_sel'
    fifo_\<alpha> fifo_invar fifo_empty fifo_isEmpty fifo_enqueue fifo_dequeue fifo_push
  for P
by(unfold_locales)

interpretation J_rr!: 
  scheduler
    final_expr "sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA
    "J_rr.round_robin P n0" Jinja_output "pick_wakeup_via_sel rm_sel'" J_rr.round_robin_invar
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_delete rm_iterate
  for P n0
apply(rule J_rr.round_robin_scheduler)
apply(unfold eval_sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o)
apply(rule sc.red_mthr_deterministic[OF sc_deterministic_heap_ops])
done

subsection {* Random scheduler *}

interpretation J_rnd!: 
  random_scheduler_base
    final_expr "sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_iterate 
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_delete rm_iterate rm_sel'
    lsi_\<alpha> lsi_invar lsi_empty lsi_ins_dj lsi_to_list
  for P
.

definition sc_rnd_J_start_state :: "Random.seed \<Rightarrow> random_scheduler"
where "sc_rnd_J_start_state seed = seed"

definition exec_J_rnd ::
  "Random.seed \<Rightarrow> J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> 
  (obs_event list, ((addr, thread_id) locks \<times> ((thread_id, (expr \<times> locals) \<times> addr released_locks) RBT.rbt \<times> heap) \<times>
                    (thread_id, addr wait_set_status) RBT.rbt) diverge) tllist"
where "exec_J_rnd seed P C M vs = J_rnd.exec P (sc_rnd_J_start_state seed) (sc_J_start_state_refine P C M vs)"

interpretation J_rnd!:
  random_scheduler
    final_expr "sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_iterate 
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_delete rm_iterate rm_sel'
    lsi_\<alpha> lsi_invar lsi_empty lsi_ins_dj lsi_to_list
  for P
by(unfold_locales)

interpretation J_rnd!:
  scheduler
    final_expr "sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA
    "J_rnd.random_scheduler P" Jinja_output "pick_wakeup_via_sel rm_sel'" "\<lambda>_ _. True"
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_delete rm_iterate
  for P
apply(rule J_rnd.random_scheduler_scheduler)
apply(unfold eval_sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o)
apply(rule sc.red_mthr_deterministic[OF sc_deterministic_heap_ops])
done

ML {* @{code exec_J_rr} *}

ML {* @{code exec_J_rnd} *}

end