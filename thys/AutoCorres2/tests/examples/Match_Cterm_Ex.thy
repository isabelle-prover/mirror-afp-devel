(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Match_Cterm_Ex
  imports 
    AutoCorres2.Match_Cterm
   
begin

section \<open>ML Antiquotation to Match and Morph\<close>

text \<open>The following example illustrates how to define a localized \<open>simproc\<close> and properly morph
the formal entities to accomodate the interpretations. Note that the \<open>simproc\<close> is a
\<open>declaration\<close> and hence a similar approach might be useful for declarations in general\<close>

declare [[verbose=5]]
locale two_eq =
  fixes f g ::"'a \<Rightarrow> 'b" 
  assumes eq: "f = g"
begin
lemma swap: "(f x = g x) \<equiv> (g x = f x)"
  by (simp add: eq)

simproc_setup swap_simproc (\<open>f x = g y\<close>) = \<open>
fn phi => fn ctxt => fn ct => 
  let 
    val _ = tracing ("swap_simproc: " ^ @{make_string} ct)
    val {x, ...} = @{cterm_morph_match (fo) \<open>f ?x = g ?x\<close>} phi ct \<comment> \<open>the pattern is morphed\<close>
    val _ = tracing ("match for x: " ^ @{make_string} x) 
    val swap = Morphism.thm phi @{thm swap}  \<comment> \<open>the theorem is morphed an instantiated\<close>
             |> Drule.infer_instantiate' ctxt [SOME x]
    val _ = tracing ("swap instantiated: " ^ @{make_string} swap)
  in SOME swap  end
  handle Pattern.MATCH => (tracing "match failed"; NONE)
\<close>

end

definition "F \<equiv> (\<lambda>_::int. 1::nat)"
definition "G \<equiv> (\<lambda>_::int. 1::nat)"


interpretation F_G: two_eq F G
  by (unfold_locales) (simp add: F_def G_def)

lemma "F a = G a"
  apply simp \<comment> \<open>The interpreted pattern is matched by \<open>morph_match\<close>\<close>
  apply (simp add: F_G.eq)
  done

lemma "F a = G b"
  apply simp? \<comment> \<open>Matching fails because \<^term>\<open>a\<close> and \<^term>\<open>b\<close> are not the same\<close>
  oops

lemma "G a = F a"
  apply simp? \<comment> \<open>Already the pattern match of the \<open>simproc_setup\<close> fails here, because the
                  equation has the wrong order. So the \<open>simproc\<close> is not even invoked\<close>
  oops
declare [[verbose=0]]

end