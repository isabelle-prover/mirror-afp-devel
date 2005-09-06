(*  Title:      Jinja/J/State.thy
    ID:         $Id: State.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Program State} *}

theory State imports "../Common/Exceptions" begin

types
  locals = "vname \<rightharpoonup> val"      -- "local vars, incl. params and ``this''"
  state  = "heap \<times> locals"

constdefs
  hp :: "state \<Rightarrow> heap"
  "hp  \<equiv>  fst"
  lcl :: "state \<Rightarrow> locals"
  "lcl  \<equiv>  snd"

(*<*)
declare hp_def[simp] lcl_def[simp]
(*>*)
end
