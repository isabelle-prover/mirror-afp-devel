(*  Title:       CoreC++
    Author:      Gerwin Klein
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section {* System Classes *}

theory SystemClasses imports Exceptions begin


text {*
  This theory provides definitions for the system exceptions.
*}

definition NullPointerC :: "cdecl" where
  "NullPointerC \<equiv> (NullPointer, ([],[],[]))"

definition ClassCastC :: "cdecl" where
  "ClassCastC \<equiv> (ClassCast, ([],[],[]))"

definition OutOfMemoryC :: "cdecl" where
  "OutOfMemoryC \<equiv> (OutOfMemory, ([],[],[]))"

definition SystemClasses :: "cdecl list" where
  "SystemClasses \<equiv> [NullPointerC, ClassCastC, OutOfMemoryC]"

end
