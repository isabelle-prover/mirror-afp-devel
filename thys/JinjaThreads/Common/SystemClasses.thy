(*  Title:      JinjaThreads/Common/SystemClasses.thy
    Author:     Gerwin Klein, Andreas Lochbihler

    Based on the Jinja theory Common/SystemClasses.thy by Gerwin Klein
*)

header {* \isaheader{System Classes} *}

theory SystemClasses imports Decl Exceptions begin

text {*
  This theory provides definitions for the @{text Object} class,
  and the system exceptions.
*}

definition ObjectC :: "'m cdecl"
where [code_inline]: "ObjectC = (Object, (undefined,[],[]))"

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

definition SystemClasses :: "'m cdecl list"
where [code_inline]: 
  "SystemClasses \<equiv> [ObjectC, ThrowableC, NullPointerC, ClassCastC, OutOfMemoryC,
                    ArrayIndexOutOfBoundsC, ArrayStoreC, NegativeArraySizeC,
                    IllegalMonitorStateC, IllegalThreadStateC]"

end
