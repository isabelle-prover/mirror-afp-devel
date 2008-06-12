(*  Title:      Jinja/J/State.thy
    ID:         $Id: State.thy,v 1.5 2008-06-12 06:57:23 lsf37 Exp $
    Author:     Tobias Nipkow, Andreas Lochbihler
    Copyright   2003 Technische Universitaet Muenchen
*)

header {* \isaheader{Program State} *}

theory State imports "../Objects" begin


types
  locals = "vname \<rightharpoonup> val"      -- "local vars, incl. params and ``this''"
  Jstate = "heap \<times> locals"     -- "the heap and the local vars"

definition hp :: "Jstate \<Rightarrow> heap" where "hp \<equiv> fst"

definition lcl :: "Jstate \<Rightarrow> locals" where "lcl \<equiv> snd"

lemma hp_conv [simp]: "hp (h, l) = h"
by(simp add: hp_def)

lemma lcl_conv [simp]: "lcl (h, l) = l"
by(simp add: lcl_def)

end
