(*  Title:       CoreC++
    ID:          $Id: SystemClasses.thy,v 1.3 2006-05-24 01:09:42 lsf37 Exp $
    Author:      Gerwin Klein
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

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
