header {* \isaheader{Example for Recursion Combinator} *}
theory Recursion
imports 
  "../Refine" 
  "../Refine_Autoref" "../Autoref_Collection_Bindings" 
  "../Collection_Bindings" 
  "../../Collections/Collections"
begin

text {*
  This example presents the usage of the recursion combinator
  @{text "RECT"}. The usage of the partial correct version 
  @{text "REC"} is similar.

  We define a simple DFS-algorithm, prove a simple correctness
  property, and do data refinement to an efficient implementation.
*}

subsection {* Definition *}
text {* Recursive DFS-Algorithm. 
  @{text "E"} is the edge relation of the graph, @{text "vd"} the node to 
  search for, and @{text "v0"} the start node.
  Already explored nodes are 
  stored in @{text "V"}.*}
definition dfs :: "('a\<times>'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool nres" where
  "dfs E vd v0 \<equiv> do {
   REC\<^isub>T (\<lambda>D (V,v). 
    if v=vd then RETURN True 
    else if v\<in>V then RETURN False
    else do {
      let V=insert v V;
      FOREACH\<^isub>C (E``{v}) (op = False) (\<lambda>v' _. D (V,v')) False
    }
  ) ({},v0)
  }"

subsection {* Correctness *}
text {* As simple correctness property, we show:
  If the algorithm returns true, then @{text "vd"} is reachable from 
  @{text "v0"}.
*}
lemma dfs_correct:
  fixes v0 E
  assumes [simp,intro]: "finite (E\<^sup>*``{v0})"
  shows "dfs E vd v0 \<le> SPEC (\<lambda>r. r \<longrightarrow> (v0,vd)\<in>E\<^sup>*)"
  unfolding dfs_def
  apply (rule RECT_rule[where 
    \<Phi>="\<lambda>(V,v). (v0,v)\<in>E\<^sup>* \<and> V\<subseteq>E\<^sup>*``{v0}" and
    V="finite_psupset (E\<^sup>*``{v0}) <*lex*> {}"
    ])
    apply (refine_mono)

    apply blast

    apply (simp)

    apply (intro refine_vcg)
      apply simp

      apply simp

      apply (rule_tac I="\<lambda>_ r. r \<longrightarrow> (v0, vd) \<in> E\<^sup>*" in FOREACHc_rule)
        apply simp
        apply (rule finite_subset[of _ "(E\<^sup>*``{v0})"])
        apply (auto) []
        apply simp

        apply simp

        apply simp
        (* Ughly way to apply induction hypothesis *)
        apply (tactic {* Refine_Misc.rprems_tac @{context} 1 *})
        apply simp
        apply (auto) []
        apply (auto simp: finite_psupset_def) []

      apply assumption

      apply assumption
  done    

subsection {* Data Refinement and Determinization *}
text {*
  Next, we use automatic data refinement and transfer to generate an
  executable algorithm using a hashset. The edges function
  is refined to a successor function returning a list-set.
*}
schematic_lemma dfs_impl_refine_aux:
  fixes v0::"'v::hashable" and succi
  defines "E \<equiv> {(v,v'). v'\<in>ls_\<alpha> (succi v)}"
  shows "RETURN (?f) \<le> \<Down>Id (dfs E vd v0)"
  apply (rule autoref_det_optI[where \<alpha>="RETURN"])

  txt {* Data Refinement Phase *}
  using IdI[of "E"] IdI[of vd] IdI[of v0] -- "Declare parameters as identities"
  unfolding dfs_def
  apply (refine_autoref -- "Automatic refinement" 
    spec_Id[where 'a='v]
    spec_R[where 'c="'v hs" and 'a="'v set"]
  )

  txt {* Transfer Phase *}
  apply (subgoal_tac "\<And>b. set_iterator (\<lambda>c f. 
    (IT_tag ls_iteratei (succi b)) c f) 
    (E `` {b})") -- "Prepare transfer of iterator"
  apply (refine_transfer the_resI 
  ) -- {* Transfer using monad. 
    Hence @{text "the_resI"} *}

  apply (subgoal_tac -- "Show iterator (Left over from subgoal-tac above)"
    "(E `` {b}) = ls_\<alpha> (succi b)")
  apply (simp only:)
  apply (rule ls.it_is_iterator)
  apply (auto simp: E_def) [2]

  txt {* Optimization Phase. We apply no optimizations here. *}
  apply (rule refl)
  done

subsubsection {* Executable Code *}
text {*
  In our prototype, the code equations for recursion have to be set up
  manually, as done below:
*}
thm dfs_impl_refine_aux[no_vars]

definition "dfs_rec_body succi t \<equiv>
   (\<lambda>f (a, b).
       if b = t then dRETURN True
       else if hs_memb b a then dRETURN False
            else let xa = hs_ins_dj b a
                 in IT_tag ls_iteratei (succi b)
                     (dres_case True True (op = False))
                     (\<lambda>x s. s \<guillemotright>= (\<lambda>s. f (xa, x))) (dRETURN False))
"


definition "dfs_rec succi t \<equiv> REC\<^isub>T (dfs_rec_body succi t)"
definition dfs_impl where "dfs_impl succi t s0 \<equiv> 
  the_res (dfs_rec succi t (hs_empty (), s0))"

text {* Code equation for recursion *}
lemma [code]: "dfs_rec succi t x = dfs_rec_body succi t (dfs_rec succi t) x"
  unfolding dfs_rec_def
  apply (rule RECT_unfold)
  unfolding dfs_rec_body_def
  apply (refine_mono)
  done


text {* We fold the definitions, to get a nice refinement lemma *}
lemma dfs_impl_refine: 
  "RETURN (dfs_impl succi t s0) 
  \<le> \<Down>Id (dfs {(s,s'). s'\<in>ls_\<alpha> (succi s)} t s0)"
  using dfs_impl_refine_aux[folded dfs_rec_body_def dfs_rec_def] 
  unfolding dfs_impl_def .

text {* Combining refinement and the correctness lemma, we get a correctness 
  property of the plain function. *}
lemma dfs_impl_correct:
  fixes succi
  defines "E \<equiv> {(s, s'). s' \<in> ls_\<alpha> (succi s)}"
  assumes F: "finite (E\<^sup>*``{v0})"
  assumes R: "dfs_impl succi vd v0"
  shows "(v0,vd)\<in>E\<^sup>*"
proof -
  note dfs_impl_refine[of succi vd v0]
  also note dfs_correct[OF F, of vd, unfolded E_def]
  finally show ?thesis using R by (auto simp: E_def)
qed

text {* Finally, we can generate code *}
export_code dfs_impl in SML file -
export_code dfs_impl in OCaml file -
export_code dfs_impl in Haskell file -
export_code dfs_impl in Scala file -
  
end
