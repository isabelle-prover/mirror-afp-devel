(*  Title:      JinjaThreads/JVM/JVMState.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

header {* 
  \chapter{Jinja Virtual Machine}\label{cha:jvm}
  \isaheader{State of the JVM} 
*}

theory JVMState imports
  "../Common/Objects"
  "../Framework/FWState"
  "../Common/Observable_Events"
begin

section {* Frame Stack *}

types 
  pc = nat

  frame = "val list \<times> val list \<times> cname \<times> mname \<times> pc"
  -- "operand stack" 
  -- "registers (including this pointer, method parameters, and local variables)"
  -- "name of class where current method is defined"
  -- "parameter types"
  -- "program counter within frame"

translations
  (type) "frame" <= (type) "val list \<times> val list \<times> String.literal \<times> String.literal \<times> nat"

section {* Runtime State *}
types
  jvm_state = "addr option \<times> heap \<times> frame list"  
  -- "exception flag, heap, frames"

types
  jvm_thread_state = "addr option \<times> frame list"
  -- "exception flag, frames, thread lock state"

types
  jvm_thread_action = "(addr,thread_id,jvm_thread_state,heap,addr,obs_event option) thread_action"
  jvm_ta_state = "jvm_thread_action \<times> jvm_state"

translations
  (type) "jvm_thread_action" <= (type) "(nat,nat,nat option \<times> frame list,heap,nat,obs_event option) thread_action"

end
