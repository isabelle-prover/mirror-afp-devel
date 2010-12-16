(*  Title:      JinjaThreads/MM/SC_Interp.thy
    Author:     Andreas Lochbihler

    Interpret the language specific heap locales with the SC memory model
*)

theory SC_Interp imports
  SC
  "../Compiler/Correctness" 
  "../J/Deadlocked"
  "../BV/JVMDeadlocked"
begin

text {*
  Do not interpret these locales, it just takes too long to generate all definitions and theorems.
*}

lemma sc_J_typesafe:
  "J_typesafe sc_empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_read sc_heap_write (sc_hconf P) P"
by unfold_locales

lemma sc_JVM_typesafe:
  "JVM_typesafe sc_empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_read sc_heap_write (sc_hconf P) P"
by unfold_locales

lemma compP2_compP1_convs:
  "is_type (compP2 (compP1 P)) = is_type P"
  "is_class (compP2 (compP1 P)) = is_class P"
  "sc.addr_loc_type (compP2 (compP1 P)) = sc.addr_loc_type P"
  "sc.conf (compP2 (compP1 P)) = sc.conf P"
by(simp_all add: compP2_def heap_base.compP_conf heap_base.compP_addr_loc_type fun_eq_iff split: addr_loc.splits)

lemma sc_J_JVM_conf_read:
  "J_JVM_conf_read sc_empty (sc_new_obj P) sc_new_arr sc_typeof_addr sc_array_length sc_heap_read sc_heap_write (sc_hconf P) P"
apply(intro_locales)
 apply(rule heap_conf.axioms)
 prefer 2
 apply(rule heap_conf_read.axioms)
 apply(unfold compP2_def compP1_def compP_heap_conf compP_heap_conf_read)
by(unfold_locales)

end