(*  Title:      HOL/MicroJava/J/SystemClasses.thy
    ID:         $Id: SystemClasses.thy,v 1.4 2008-10-07 14:07:44 fhaftmann Exp $
    Author:     Gerwin Klein
    Copyright   2002 Technische Universitaet Muenchen
*)

header {* \isaheader{System Classes} *}

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
