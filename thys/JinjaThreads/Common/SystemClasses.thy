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
  "ObjectC \<equiv> (Object, (undefined,[],[]))"

  NullPointerC :: "'m cdecl"
  "NullPointerC \<equiv> (NullPointer, (Object,[],[]))"

  ClassCastC :: "'m cdecl"
  "ClassCastC \<equiv> (ClassCast, (Object,[],[]))"

  OutOfMemoryC :: "'m cdecl"
  "OutOfMemoryC \<equiv> (OutOfMemory, (Object,[],[]))"

  ArrayIndexOutOfBoundsC :: "'m cdecl"
  "ArrayIndexOutOfBoundsC \<equiv> (ArrayIndexOutOfBounds, (Object,[],[]))"

  ArrayStoreC :: "'m cdecl"
  "ArrayStoreC \<equiv> (ArrayStore, (Object, [], []))"

  NegativeArraySizeC :: "'m cdecl"
  "NegativeArraySizeC \<equiv> (NegativeArraySize, (Object,[],[]))"

  IllegalMonitorStateC :: "'m cdecl"
  "IllegalMonitorStateC \<equiv> (IllegalMonitorState, (Object,[],[]))"

  IllegalThreadStateC :: "'m cdecl"
  "IllegalThreadStateC \<equiv> (IllegalThreadState, (Object,[],[]))"

  SystemClasses :: "'m cdecl list"
  "SystemClasses \<equiv> [ObjectC, NullPointerC, ClassCastC, OutOfMemoryC,
                    ArrayIndexOutOfBoundsC, ArrayStoreC, NegativeArraySizeC,
                    IllegalMonitorStateC, IllegalThreadStateC]"

end
