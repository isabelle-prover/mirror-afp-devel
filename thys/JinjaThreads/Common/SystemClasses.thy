(*  Title:      JinjaThreads/Common/SystemClasses.thy
    Author:     Gerwin Klein, Andreas Lochbihler

    Based on the Jinja theory Common/SystemClasses.thy by Gerwin Klein
*)

header {* \isaheader{System Classes} *}

theory SystemClasses imports Exceptions begin

text {*
  This theory provides definitions for the @{text Object} class,
  and the system exceptions.

  Inline SystemClasses definition because they are polymorphic values that violate ML's value restriction.
*}

text {*
  Object has actually superclass, but we set it to the empty string for code generation.
  Any other class name (like @{term undefined}) would do as well except for code generation.
*}
definition ObjectC :: "'m cdecl"
where [code_inline]: "ObjectC = (Object, (STR '''',[],[]))"

definition ThrowableC :: "'m cdecl"
where [code_inline]: "ThrowableC \<equiv> (Throwable, (Object, [], []))"

definition NullPointerC :: "'m cdecl"
where [code_inline]: "NullPointerC \<equiv> (NullPointer, (Throwable,[],[]))"

definition ClassCastC :: "'m cdecl"
where [code_inline]: "ClassCastC \<equiv> (ClassCast, (Throwable,[],[]))"

definition OutOfMemoryC :: "'m cdecl"
where [code_inline]: "OutOfMemoryC \<equiv> (OutOfMemory, (Throwable,[],[]))"

definition ArrayIndexOutOfBoundsC :: "'m cdecl"
where [code_inline]: "ArrayIndexOutOfBoundsC \<equiv> (ArrayIndexOutOfBounds, (Throwable,[],[]))"

definition ArrayStoreC :: "'m cdecl"
where [code_inline]: "ArrayStoreC \<equiv> (ArrayStore, (Throwable, [], []))"

definition NegativeArraySizeC :: "'m cdecl"
where [code_inline]: "NegativeArraySizeC \<equiv> (NegativeArraySize, (Throwable,[],[]))"

definition IllegalMonitorStateC :: "'m cdecl"
where [code_inline]: "IllegalMonitorStateC \<equiv> (IllegalMonitorState, (Throwable,[],[]))"

definition IllegalThreadStateC :: "'m cdecl"
where [code_inline]: "IllegalThreadStateC \<equiv> (IllegalThreadState, (Throwable,[],[]))"

definition CloneNotSupportedC :: "'m cdecl"
where [code_inline]: "CloneNotSupportedC \<equiv> (CloneNotSupported, (Throwable,[],[]))"

definition InterruptedExceptionC :: "'m cdecl"
where [code_inline]: "InterruptedExceptionC \<equiv> (InterruptedException, (Throwable,[],[]))"

definition StringC :: "'m cdecl"
where [code_inline]: "StringC \<equiv> (String, (Object, [], []))"

definition SystemClasses :: "'m cdecl list"
where [code_inline]: 
  "SystemClasses \<equiv> [ObjectC, ThrowableC, NullPointerC, ClassCastC, OutOfMemoryC,
                    ArrayIndexOutOfBoundsC, ArrayStoreC, NegativeArraySizeC,
                    IllegalMonitorStateC, IllegalThreadStateC, CloneNotSupportedC, InterruptedExceptionC, StringC]"

end
