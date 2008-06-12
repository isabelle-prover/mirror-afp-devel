(*  Title:      JinjaThreads/JVM/JVMInstructions.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{Instructions of the JVM} *}


theory JVMInstructions imports JVMState begin


datatype 
  instr = Load nat                  -- "load from local variable"
        | Store nat                 -- "store into local variable"
        | Push val                  -- "push a value (constant)"
        | New cname                 -- "create object"
        | NewArray ty               -- "create array for elements of given type"
        | ALoad                     -- "Load array element from heap to stack"
        | AStore                    -- "Set element in array"
        | Getfield vname cname      -- "Fetch field from object"
        | Putfield vname cname      -- "Set field in object    "
        | Checkcast ty              -- "Check whether object is of given type"
        | Invoke mname nat          -- "inv. instance meth of an object"
        | Return                    -- "return from method"
        | Pop                       -- "pop top element from opstack"
        | IAdd                      -- "integer addition"
        | Goto int                  -- "goto relative address"
        | CmpEq                     -- "equality comparison"
        | IfFalse int               -- "branch if top of stack false"
        | Throw                     -- "throw top of stack as exception"
        | MEnter                    -- "enter the monitor of object on top of the stack"
        | MExit                     -- "exit the monitor of object on top of the stack"

types
  bytecode = "instr list"

  ex_entry = "pc \<times> pc \<times> cname \<times> pc \<times> nat" 
  -- "start-pc, end-pc, exception type, handler-pc, remaining stack depth"

  ex_table = "ex_entry list"

  jvm_method = "nat \<times> nat \<times> bytecode \<times> ex_table"
   -- "max stacksize"
   -- "number of local variables. Add 1 + no. of parameters to get no. of registers"
   -- "instruction sequence"
   -- "exception handler table"

  jvm_prog = "jvm_method prog" 

end
