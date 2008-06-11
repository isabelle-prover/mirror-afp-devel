(*  Title:      Jinja/J/State.thy
    ID:         $Id: State.thy,v 1.4 2008-06-11 14:22:58 lsf37 Exp $
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Program State} *}

theory State imports Expr "../Common/Exceptions" begin

types
  thread_id = nat

types
  locals = "vname \<rightharpoonup> val"      -- "local vars, incl. params and ``this''"
  Jstate = "heap \<times> locals"     -- "the heap and the local vars"

constdefs
  hp :: "Jstate \<Rightarrow> heap"
  "hp \<equiv> fst"
  lcl :: "Jstate \<Rightarrow> locals"
  "lcl \<equiv> snd"

declare hp_def[simp] lcl_def[simp]

end
