(*  Title:       CoreC++
    ID:          $Id: State.thy,v 1.6 2006-11-06 11:54:13 wasserra Exp $
    Author:      Tobias Nipkow
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)


header {* \isaheader{Program State} *}

theory State imports Exceptions begin


types
  locals = "vname \<rightharpoonup> val"      -- "local vars, incl. params and ``this''"
  state  = "heap \<times> locals"

constdefs
  hp :: "state \<Rightarrow> heap"
  "hp  \<equiv>  fst"
  lcl :: "state \<Rightarrow> locals"
  "lcl  \<equiv>  snd"


declare hp_def[simp] lcl_def[simp]



end
