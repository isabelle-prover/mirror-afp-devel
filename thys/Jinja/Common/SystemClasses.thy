(*  Title:      HOL/MicroJava/J/SystemClasses.thy

    Author:     Gerwin Klein
    Copyright   2002 Technische Universitaet Muenchen
*)

section {* System Classes *}

theory SystemClasses
imports Decl Exceptions
begin

text {*
  This theory provides definitions for the @{text Object} class,
  and the system exceptions.
*}

definition ObjectC :: "'m cdecl"
where
  "ObjectC \<equiv> (Object, (undefined,[],[]))"

definition NullPointerC :: "'m cdecl"
where
  "NullPointerC \<equiv> (NullPointer, (Object,[],[]))"

definition ClassCastC :: "'m cdecl"
where
  "ClassCastC \<equiv> (ClassCast, (Object,[],[]))"

definition OutOfMemoryC :: "'m cdecl"
where
  "OutOfMemoryC \<equiv> (OutOfMemory, (Object,[],[]))"

definition SystemClasses :: "'m cdecl list"
where
  "SystemClasses \<equiv> [ObjectC, NullPointerC, ClassCastC, OutOfMemoryC]"

end
