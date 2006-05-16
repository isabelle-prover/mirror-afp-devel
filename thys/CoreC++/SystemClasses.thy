(* Author: Gerwin Klein *)

header {* System Classes *}

theory SystemClasses imports Exceptions begin

text {*
  This theory provides definitions for the system exceptions.
*}

constdefs
  NullPointerC :: "cdecl"
  "NullPointerC \<equiv> (NullPointer, ([],[],[]))"

  ClassCastC :: "cdecl"
  "ClassCastC \<equiv> (ClassCast, ([],[],[]))"

  OutOfMemoryC :: "cdecl"
  "OutOfMemoryC \<equiv> (OutOfMemory, ([],[],[]))"

  SystemClasses :: "cdecl list"
  "SystemClasses \<equiv> [NullPointerC, ClassCastC, OutOfMemoryC]"

end
