(*  Title:      Ref.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

header {* An Abstract Type for (Heap-) References *}

theory Ref 
imports Main

begin

typedef ref = "UNIV::nat set" by simp

types_code
  ref ("int") 
attach (term_of) {*
 val term_of_ref = HOLogic.mk_int o IntInf.fromInt;
*}


consts Null::ref 
consts new:: "ref set \<Rightarrow> ref"

locale allocation =
 assumes fresh: "finite A \<Longrightarrow> new A \<notin> A \<union> {Null}"

text {* Constants @{const "Null"} and @{const "new"} can be defined later on.
Conceptually they are @{text "fixes"} of the locale @{text "allocation"}.
But since definitions relative to a locale do not yet work in Isabelle2005
we use this workaround to avoid lots of parameters in definitions.
*}

end
