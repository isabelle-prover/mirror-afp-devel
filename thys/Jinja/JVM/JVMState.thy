(*  Title:      Jinja/JVM/JVMState.thy

    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

chapter {* Jinja Virtual Machine \label{cha:jvm} *}

section {* State of the JVM *}

theory JVMState imports "../Common/Objects" begin

subsection {* Frame Stack *}

type_synonym 
  pc = nat

type_synonym
  frame = "val list \<times> val list \<times> cname \<times> mname \<times> pc"
  \<comment> \<open>operand stack\<close> 
  \<comment> \<open>registers (including this pointer, method parameters, and local variables)\<close>
  \<comment> \<open>name of class where current method is defined\<close>
  \<comment> \<open>parameter types\<close>
  \<comment> \<open>program counter within frame\<close>

subsection {* Runtime State *}

type_synonym
  jvm_state = "addr option \<times> heap \<times> frame list"  
  \<comment> \<open>exception flag, heap, frames\<close>
  
end
