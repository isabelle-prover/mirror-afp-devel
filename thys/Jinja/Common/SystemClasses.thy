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

constdefs
  ObjectC :: "'m cdecl"
  "ObjectC \<equiv> (Object, (undefined,[],[]))"

  NullPointerC :: "'m cdecl"
  "NullPointerC \<equiv> (NullPointer, (Object,[],[]))"

  ClassCastC :: "'m cdecl"
  "ClassCastC \<equiv> (ClassCast, (Object,[],[]))"

  OutOfMemoryC :: "'m cdecl"
  "OutOfMemoryC \<equiv> (OutOfMemory, (Object,[],[]))"

  SystemClasses :: "'m cdecl list"
  "SystemClasses \<equiv> [ObjectC, NullPointerC, ClassCastC, OutOfMemoryC]"

end
