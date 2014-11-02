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
  -- "operand stack" 
  -- "registers (including this pointer, method parameters, and local variables)"
  -- "name of class where current method is defined"
  -- "parameter types"
  -- "program counter within frame"

subsection {* Runtime State *}

type_synonym
  jvm_state = "addr option \<times> heap \<times> frame list"  
  -- "exception flag, heap, frames"
  
end
