(*  Title:      JinjaThreads/JVM/JVMInstructions.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

section {* Instructions of the JVM *}

theory JVMInstructions
imports
  JVMState
  "../Common/BinOp"
begin

datatype 'addr instr 
  = Load nat                  -- "load from local variable"
  | Store nat                 -- "store into local variable"
  | Push "'addr val"          -- "push a value (constant)"
  | New cname                 -- "create object"
  | NewArray ty               -- "create array for elements of given type"
  | ALoad                     -- "Load array element from heap to stack"
  | AStore                    -- "Set element in array"
  | ALength                   -- "Return the length of the array"
  | Getfield vname cname      -- "Fetch field from object"
  | Putfield vname cname      -- "Set field in object    "
  | Checkcast ty              -- "Check whether object is of given type"
  | Instanceof ty             -- "instanceof test"
  | Invoke mname nat          -- "inv. instance meth of an object"
  | Return                    -- "return from method"
  | Pop                       -- "pop top element from opstack"
  | Dup                       -- "duplicate top stack element"
  | Swap                      -- "swap top stack elements"
  | BinOpInstr bop            -- "binary operator instruction"
  | Goto int                  -- "goto relative address"
  | IfFalse int               -- "branch if top of stack false"
  | ThrowExc                  -- "throw top of stack as exception"
  | MEnter                    -- "enter the monitor of object on top of the stack"
  | MExit                     -- "exit the monitor of object on top of the stack"

abbreviation CmpEq :: "'addr instr"
where "CmpEq \<equiv> BinOpInstr Eq"

abbreviation CmpLeq :: "'addr instr"
where "CmpLeq \<equiv> BinOpInstr LessOrEqual"

abbreviation CmpGeq :: "'addr instr"
where "CmpGeq \<equiv> BinOpInstr GreaterOrEqual"

abbreviation CmpLt :: "'addr instr"
where "CmpLt \<equiv> BinOpInstr LessThan"

abbreviation CmpGt :: "'addr instr"
where "CmpGt \<equiv> BinOpInstr GreaterThan"

abbreviation IAdd :: "'addr instr"
where "IAdd \<equiv> BinOpInstr Add"

abbreviation ISub :: "'addr instr"
where "ISub \<equiv> BinOpInstr Subtract"

abbreviation IMult :: "'addr instr"
where "IMult \<equiv> BinOpInstr Mult"

abbreviation IDiv :: "'addr instr"
where "IDiv \<equiv> BinOpInstr Div"

abbreviation IMod :: "'addr instr"
where "IMod \<equiv> BinOpInstr Mod"

abbreviation IShl :: "'addr instr"
where "IShl \<equiv> BinOpInstr ShiftLeft"

abbreviation IShr :: "'addr instr"
where "IShr \<equiv> BinOpInstr ShiftRightSigned"

abbreviation IUShr :: "'addr instr"
where "IUShr \<equiv> BinOpInstr ShiftRightZeros"

abbreviation IAnd :: "'addr instr"
where "IAnd \<equiv> BinOpInstr BinAnd"

abbreviation IOr :: "'addr instr"
where "IOr \<equiv> BinOpInstr BinOr"

abbreviation IXor :: "'addr instr"
where "IXor \<equiv> BinOpInstr BinXor"

type_synonym
  'addr bytecode = "'addr instr list"

type_synonym
  ex_entry = "pc \<times> pc \<times> cname option \<times> pc \<times> nat" 
  -- "start-pc, end-pc, exception type (None = Any), handler-pc, remaining stack depth"

type_synonym
  ex_table = "ex_entry list"

type_synonym
  'addr jvm_method = "nat \<times> nat \<times> 'addr bytecode \<times> ex_table"
   -- "max stacksize"
   -- "number of local variables. Add 1 + no. of parameters to get no. of registers"
   -- "instruction sequence"
   -- "exception handler table"

type_synonym
  'addr jvm_prog = "'addr jvm_method prog" 

end
