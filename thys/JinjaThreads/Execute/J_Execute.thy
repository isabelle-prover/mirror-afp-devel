(*  Title:      JinjaThreads/Execute/J_Execute.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Executable semantics for J} *}

theory J_Execute imports
  Round_Robin
  "../J/Threaded"
  "../MM/SC" 
  "../../Collections/RBTMapImpl"
  "../../Collections/Fifo"
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

text {*
  Introduce a new constant for @{term round_robin_step} and everything that depends on it.
  This allows to replace @{term "Predicate.the"} with @{term "the2"} in the code equation
  for @{term round_robin_step} via @{text "code_inline"}.
*}

definition J_rr_round_robin_step 
where [code del]: 
  "J_rr_round_robin_step P = 
  round_robin_base.round_robin_step 
    final_expr (sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P) 
    rm_lookup rm_update 
    rm_lookup
    fifo_enqueue fifo_dequeue"

definition J_rr_round_robin_reschedule
where [code del]: 
  "J_rr_round_robin_reschedule P =
   round_robin_base.round_robin_reschedule
     final_expr (sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P)
     rm_lookup rm_update
     rm_lookup 
     fifo_enqueue fifo_dequeue fifo_push"

definition J_rr_round_robin
where [code del]: 
  "J_rr_round_robin P =
   round_robin_base.round_robin
     final_expr (sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P)
     rm_lookup rm_update
     rm_lookup 
     fifo_isEmpty fifo_enqueue fifo_dequeue fifo_push"

definition J_rr_execT
where [code del]:
  "J_rr_execT P n0 =
   scheduler_base.execT
     convert_RA (J_rr_round_robin P n0) (pick_wakeup_via_sel rm_sel')
     rm_lookup rm_update
     rm_lookup rm_update rm_delete rm_iterate"

definition J_rr_exec_step
where [code del]:
  "J_rr_exec_step P n0 =
   scheduler_base.exec_step
     convert_RA (J_rr_round_robin P n0) Jinja_output (pick_wakeup_via_sel rm_sel')
     rm_lookup rm_update
     rm_lookup rm_update rm_delete rm_iterate"

definition J_rr_exec_aux
where [code del]:
  "J_rr_exec_aux P n0 =
   scheduler_base.exec_aux
     convert_RA (J_rr_round_robin P n0) Jinja_output (pick_wakeup_via_sel rm_sel')
     rm_lookup rm_update
     rm_lookup rm_update rm_delete rm_iterate"

definition J_rr_exec
where [code del]:
  "J_rr_exec P n0 =
   scheduler_base.exec
     convert_RA (J_rr_round_robin P n0) Jinja_output (pick_wakeup_via_sel rm_sel')
     rm_lookup rm_update
     rm_lookup rm_update rm_delete rm_iterate"

interpretation J_rr!: 
  round_robin_base
    final_expr "sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P" convert_RA Jinja_output
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update 
    rm_\<alpha> rm_invar rm_empty rm_lookup rm_update rm_delete rm_iterate rm_sel'
    fifo_\<alpha> fifo_invar fifo_empty fifo_isEmpty fifo_enqueue fifo_dequeue fifo_push
  for P
  where 
  "round_robin_base.round_robin_step
     final_expr (sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P) 
     rm_lookup rm_update
     rm_lookup
     fifo_enqueue fifo_dequeue 
  = J_rr_round_robin_step P"
  and 
  "round_robin_base.round_robin_reschedule
     final_expr (sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P)
     rm_lookup rm_update
     rm_lookup 
     fifo_enqueue fifo_dequeue fifo_push
  = J_rr_round_robin_reschedule P"
  and
  "round_robin_base.round_robin
     final_expr (sc_red_i_i_i_i_i_Fii_i_oB_Fii_i_i_oB_i_i_i_i_i_o_o_o P)
     rm_lookup rm_update
     rm_lookup 
     fifo_isEmpty fifo_enqueue fifo_dequeue fifo_push
  = J_rr_round_robin P"
  and
  "scheduler_base.execT
     convert_RA (J_rr_round_robin P n0) (pick_wakeup_via_sel rm_sel')
     rm_lookup rm_update
     rm_lookup rm_update rm_delete rm_iterate
  = J_rr_execT P n0"
  and
  "scheduler_base.exec_step
     convert_RA (J_rr_round_robin P n0) Jinja_output (pick_wakeup_via_sel rm_sel')
     rm_lookup rm_update
     rm_lookup rm_update rm_delete rm_iterate
  = J_rr_exec_step P n0"
  and
  "scheduler_base.exec_aux
     convert_RA (J_rr_round_robin P n0) Jinja_output (pick_wakeup_via_sel rm_sel')
     rm_lookup rm_update
     rm_lookup rm_update rm_delete rm_iterate
  = J_rr_exec_aux P n0"
  and
  "scheduler_base.exec
     convert_RA (J_rr_round_robin P n0) Jinja_output (pick_wakeup_via_sel rm_sel')
     rm_lookup rm_update
     rm_lookup rm_update rm_delete rm_iterate
  = J_rr_exec P n0"
by(fold J_rr_round_robin_step_def J_rr_round_robin_reschedule_def J_rr_round_robin_def J_rr_execT_def J_rr_exec_step_def J_rr_exec_aux_def J_rr_exec_def)(rule refl)+

lemmas [code] =
  J_rr.round_robin_step.simps
  J_rr.round_robin_reschedule.simps
  J_rr.round_robin.simps
  J_rr.execT_def
  J_rr.exec_step.simps
  J_rr.exec_aux_def
  J_rr.exec_def

definition sc_rr_J_start_state :: "nat \<Rightarrow> 'm prog \<Rightarrow> thread_id fifo round_robin"
where "sc_rr_J_start_state n0 P = J_rr.round_robin_start n0 (sc_start_tid P)"

definition exec_J_rr ::
  "nat \<Rightarrow> J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> val list \<Rightarrow> 
  (obs_event list, ((addr, thread_id) locks \<times> ((thread_id, (expr \<times> locals) \<times> addr released_locks) RBT.rbt \<times> heap) \<times>
                    (thread_id, addr wait_set_status) RBT.rbt) diverge) tllist"
where "exec_J_rr n0 P C M vs = J_rr.exec P n0 (sc_rr_J_start_state n0 P) (sc_J_start_state_refine P C M vs)"

definition singleton2 where "singleton2 = Predicate.singleton"
definition the_only2 where "the_only2 = Predicate.the_only"
definition the2 where "the2 = Predicate.the"

lemma singleton2_code [code]:
  "singleton2 dfault (Predicate.Seq f) =
  (case f () of
    Predicate.Empty \<Rightarrow> dfault ()
  | Predicate.Insert x P \<Rightarrow> 
    if Predicate.is_empty P then x else FinFun.code_abort (\<lambda>_. singleton2 dfault (Predicate.Seq f))
  | Predicate.Join P xq \<Rightarrow>
    if Predicate.is_empty P then 
      the_only2 dfault xq
    else if Predicate.null xq then singleton2 dfault P else FinFun.code_abort (\<lambda>_. singleton2 dfault (Predicate.Seq f)))"
unfolding singleton2_def the_only2_def
by(auto simp only: singleton_code code_abort_def split: seq.split split_if)

lemma the_only2_code [code]:
  "the_only2 dfault Predicate.Empty = FinFun.code_abort dfault"
  "the_only2 dfault (Predicate.Insert x P) = 
  (if Predicate.is_empty P then x else FinFun.code_abort (\<lambda>_. the_only2 dfault (Predicate.Insert x P)))"
  "the_only2 dfault (Predicate.Join P xq) = 
  (if Predicate.is_empty P then 
     the_only2 dfault xq
   else if Predicate.null xq then 
     singleton2 dfault P 
   else
     FinFun.code_abort (\<lambda>_. the_only2 dfault (Predicate.Join P xq)))"
unfolding singleton2_def the_only2_def by simp_all

lemma the2_eq [code]:
  "the2 A = singleton2 (\<lambda>x. Predicate.not_unique A) A"
unfolding the2_def singleton2_def by(rule the_eq)

lemma Predicate_the_heap_locals [code_inline]:
  fixes P :: "('a \<times> 'b \<times> heap \<times> locals) Predicate.pred"
  shows "Predicate.the P = the2 P"
unfolding the2_def ..

lemma Predicate_the_locals_heap [code_inline]:
  fixes P :: "('a \<times> ('b \<times> locals) \<times> heap) Predicate.pred"
  shows "Predicate.the P = the2 P"
unfolding the2_def ..

(* FIXME: Does not work with PolyML 5.3 - reactivate with PolyML 5.4 *)
(* ML {* @{code exec_J_rr} *} *)

end