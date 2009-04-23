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

constdefs
  ObjectC :: "'m cdecl"
  "ObjectC \<equiv> (Object, (arbitrary,[],[]))"

  ThrowableC :: "'m cdecl"
  "ThrowableC \<equiv> (Throwable, (Object, [], []))"

  NullPointerC :: "'m cdecl"
  "NullPointerC \<equiv> (NullPointer, (Throwable,[],[]))"

  ClassCastC :: "'m cdecl"
  "ClassCastC \<equiv> (ClassCast, (Throwable,[],[]))"

  OutOfMemoryC :: "'m cdecl"
  "OutOfMemoryC \<equiv> (OutOfMemory, (Throwable,[],[]))"

  ArrayIndexOutOfBoundsC :: "'m cdecl"
  "ArrayIndexOutOfBoundsC \<equiv> (ArrayIndexOutOfBounds, (Throwable,[],[]))"

  ArrayStoreC :: "'m cdecl"
  "ArrayStoreC \<equiv> (ArrayStore, (Throwable, [], []))"

  NegativeArraySizeC :: "'m cdecl"
  "NegativeArraySizeC \<equiv> (NegativeArraySize, (Throwable,[],[]))"

  IllegalMonitorStateC :: "'m cdecl"
  "IllegalMonitorStateC \<equiv> (IllegalMonitorState, (Throwable,[],[]))"

  IllegalThreadStateC :: "'m cdecl"
  "IllegalThreadStateC \<equiv> (IllegalThreadState, (Throwable,[],[]))"

  SystemClasses :: "'m cdecl list"
  "SystemClasses \<equiv> [ObjectC, ThrowableC, NullPointerC, ClassCastC, OutOfMemoryC,
                    ArrayIndexOutOfBoundsC, ArrayStoreC, NegativeArraySizeC,
                    IllegalMonitorStateC, IllegalThreadStateC]"

end
