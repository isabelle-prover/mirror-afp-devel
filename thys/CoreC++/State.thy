(* Author: Tobias Nipkow *)

header {* Program State *}

theory State imports Exceptions begin

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
