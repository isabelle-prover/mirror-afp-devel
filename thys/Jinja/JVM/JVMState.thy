(*  Title:      Jinja/JVM/JVMState.thy
    ID:         $Id: JVMState.thy,v 1.3 2007-08-12 17:21:47 makarius Exp $
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* 
  \chapter{Jinja Virtual Machine}\label{cha:jvm}
  \isaheader{State of the JVM} 
*}

theory JVMState imports "../Common/Objects" begin

section {* Frame Stack *}

type_synonym 
  pc = nat

type_synonym
  frame = "val list \<times> val list \<times> cname \<times> mname \<times> pc"
  -- "operand stack" 
  -- "registers (including this pointer, method parameters, and local variables)"
  -- "name of class where current method is defined"
  -- "parameter types"
  -- "program counter within frame"

section {* Runtime State *}

type_synonym
  jvm_state = "addr option \<times> heap \<times> frame list"  
  -- "exception flag, heap, frames"
  
end
