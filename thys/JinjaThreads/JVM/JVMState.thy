(*  Title:      JinjaThreads/JVM/JVMState.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

header {* 
  \chapter{Jinja Virtual Machine}\label{cha:jvm}
  \isaheader{State of the JVM} 
*}

theory JVMState imports "../Common/Objects" "../Framework/FWState" begin

section {* Frame Stack *}

types 
  pc = nat

  frame = "val list \<times> val list \<times> cname \<times> mname \<times> pc"
  -- "operand stack" 
  -- "registers (including this pointer, method parameters, and local variables)"
  -- "name of class where current method is defined"
  -- "parameter types"
  -- "program counter within frame"

section {* Runtime State *}
types
  jvm_state = "addr option \<times> heap \<times> frame list"  
  -- "exception flag, heap, frames"

types
  jvm_thread_state = "addr option \<times> frame list"
  -- "exception flag, frames, thread lock state"
  
end
