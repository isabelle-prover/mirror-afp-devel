header {*\isaheader{Verified BFS Implementation in ML}*}
theory Bfs_Impl
imports 
  Breadth_First_Search 
  "../Collection_Bindings" "../Refine"
  "~~/src/HOL/Library/Efficient_Nat"
begin
  text {*
    Originally, this was part of our submission to the 
    VSTTE 2010 Verification Competition. Some slight changes have been applied
    since the submitted version.
    *}


  text {*
    In the @{text "Breadth_First_Search"}-theory, we verified an abstract 
    version of the algorithm. This abstract version tried to reflect the
    given pseudocode specification as precisely as possible.

    However, it was not executable, as it was nondeterministic. Hence,
    we now refine our algorithm to an executable specification, and use
    Isabelle/HOLs code generator to generate ML-code.

    The implementation uses the Isabelle Collection Framework (ICF)
    (Available at \url{http://afp.sourceforge.net/entries/Collections.shtml}),
    to provide efficient set implementations. We choose a hashset 
    (backed by a Red Black Tree) for the visited set, and lists for
    all other sets. Moreover, we fix the node type to natural numbers.
    *}

  text {*
    The following algorithm is a straightforward rewriting of the 
    original algorithm. We only exchanged the abstract set operations by
    concrete operations on the data structures provided by the ICF.

    The operations of the list-set implementation are named
    @{text "ls_xxx"}, the ones of the hashset are named @{text "hs_xxx"}.
    *}
  definition bfs_impl :: "(nat \<Rightarrow> nat ls) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat option nres)"
    where "bfs_impl succ src dst \<equiv> do {
    (f,_,_,_,d) \<leftarrow> WHILE
      (\<lambda>(f,V,C,N,d). f=False \<and> \<not> ls_isEmpty C)
      (\<lambda>(f,V,C,N,d). do {
        v \<leftarrow> RETURN (the (ls_sel' C (\<lambda>_. True))); let C = ls_delete v C;
        if v=dst then RETURN (True,hs_empty,ls_empty,ls_empty,d)
        else do {
          (V,N) \<leftarrow> FOREACH (ls_\<alpha> (succ v)) (\<lambda>w (V,N). 
            if (\<not> hs_memb w V) then 
               RETURN (hs_ins w V, ls_ins_dj w N) 
            else RETURN (V,N)
          ) (V,N);
          if (ls_isEmpty C) then do {
            let C=N; 
            let N=ls_empty; 
            let d=d+1;
            RETURN (f,V,C,N,d)
          } else RETURN (f,V,C,N,d)
        }
      })
      (False,hs_sng src,ls_sng src, ls_empty,0::nat);
    if f then RETURN (Some d) else RETURN None
    }"

  text {* Auxilliary lemma to initialize the refinement prover. *}
  (*lemma [refine]: "(ls_\<alpha> \<circ> succ) v = ls_\<alpha> (succ v)"
    by auto*)

  (* TODO/FIXME:
    There is too much redundancy in the xx_correct - lemmas.
    They do not include the automtically instantiated generic algorithms,
    and they are independent of adding new operations to the interface or to
    the rb-interface
    *)

  text {*
    It is quite easy to show that the implementation respects the 
    specification, as most work is done by the refinement framework. *}
  theorem bfs_impl_correct:
    shows "bfs_impl succ src dst \<le> Graph.bfs_spec (ls_\<alpha>\<circ>succ) src dst"
  proof -
    txt {* As list-sets are always finite, our setting satisfies the
      finitely-branching assumption made about graphs *}
    interpret Graph "ls_\<alpha>\<circ>succ"
      by unfold_locales simp

    txt {* The refinement framework can prove automatically that
      the implementation refines the abstract algorithm.

      The notation @{text "S \<le> \<Down>R S'"} means, that the program @{text "S"}
      refines the program @{text "S'"} w.r.t.\ the refinement relation 
      (also called coupling invariant occasionally) @{text "R"}.

      In our case, the refinement relation is the identity, as
      the result type was not refined.
      *}

    have "bfs_impl succ src dst \<le> \<Down>Id (Graph.bfs (ls_\<alpha>\<circ>succ) src dst)"
      unfolding bfs_impl_def bfs_def

      apply (refine_rcg)
      apply (refine_dref_type)

      apply (rule inj_on_id | simp add: refine_hsimp 
        hs_correct hs.sng_correct ls_correct ls.sng_correct
        split: prod.split prod.split_asm) +
      done
    txt {* The result then follows due to transitivity of refinement. *}
    also have "\<dots> \<le> bfs_spec src dst"
      by (simp add: bfs_correct)
    finally show ?thesis .
  qed

  text {* The last step is to actually generate executable ML-code.
    *}

  text {*
    We first use the partial-correctness code generator of our framework
    to automatically turn the algorithm described in our framework into
    a function that is independent from our framework. This step also
    removes the last nondeterminism, that has remained in the iteration order
    of the inner loop.

    The result of the function is an option type, returning @{text "None"}
    for nontermination. Inside this option-type, there is the option type
    that encodes whether we return with failure or a distance.
    *}

  schematic_lemma bfs_code_refine_aux: 
    "nres_of ?bfs_code \<le> bfs_impl succ src dst"
    unfolding bfs_impl_def
    apply (refine_transfer)
    done

  thm bfs_code_refine_aux[no_vars]

  text {* Currently, our (prototype) framework cannot yet generate the 
    definition itself. The following definition was copy-pasted from the 
    output of the above @{text "thm"} command: *}
  definition 
    bfs_code :: "(nat \<Rightarrow> nat ls) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option dres" where
    "bfs_code succ src dst \<equiv> 
 (dWHILE (\<lambda>(f, V, C, N, d). f = False \<and> \<not> ls_isEmpty C)
   (\<lambda>(a, b).
       case b of
       (aa, ab, ac, bc) \<Rightarrow>
         dRETURN (the (ls_sel' ab (\<lambda>_. True))) \<guillemotright>=
         (\<lambda>xa. let xb = ls_delete xa ab
               in if xa = dst
                  then dRETURN (True, hs_empty, ls_empty, ls_empty, bc)
                  else lift_set_iterator ls_iteratei (succ xa)
                        (dres_case True True (\<lambda>_. True))
                        (\<lambda>x s. s \<guillemotright>=
                               (\<lambda>(ad, bd).
                                   if \<not> hs_memb x ad
                                   then dRETURN
   (hs_ins x ad, ls_ins_dj x bd)
                                   else dRETURN (ad, bd)))
                        (dRETURN (aa, ac)) \<guillemotright>=
                       (\<lambda>(ad, bd).
                           if ls_isEmpty xb
                           then let xd = bd; xe = ls_empty; xf = bc + 1
                                in dRETURN (a, ad, xd, xe, xf)
                           else dRETURN (a, ad, xb, bd, bc))))
   (False, hs_sng src, ls_sng src, ls_empty, 0) \<guillemotright>=
  (\<lambda>(a, b).
      case b of
      (aa, ab, ac, bc) \<Rightarrow> if a then dRETURN (Some bc) else dRETURN None))
"

  text {* Finally, we get the desired lemma by folding the schematic 
    lemma with the definition: *}
  lemma bfs_code_refine: 
    "nres_of (bfs_code succ src dst) \<le> bfs_impl succ src dst" 
    using bfs_code_refine_aux[folded bfs_code_def] .

  text {*
    As a last step, we make the correctness property independent of our 
    refinement framework. This step drastically decreases the trusted code 
    base, as it completely eliminates the specifications made in the
    refinement framework from the trusted code base.

    The following theorem solves both verification tasks, without depending
    on any concepts of the refinement framework, except the deterministic result
    monad.
    *}
  theorem bfs_code_correct:
    "bfs_code succ src dst = dRETURN None 
      \<Longrightarrow> \<not>(Graph.conn (ls_\<alpha> \<circ> succ) src dst)" 
    "bfs_code succ src dst = dRETURN (Some d) 
      \<Longrightarrow> Graph.conn (ls_\<alpha> \<circ> succ) src dst 
          \<and> Graph.min_dist (ls_\<alpha> \<circ> succ) src dst = d"
    "bfs_code succ src dst \<noteq> dFAIL"
  proof -
    interpret Graph "ls_\<alpha>\<circ>succ"
      by unfold_locales simp
    
    from order_trans[OF bfs_code_refine bfs_impl_correct, of succ src dst]
    show "bfs_code succ src dst = dRETURN None 
      \<Longrightarrow> \<not>(Graph.conn (ls_\<alpha> \<circ> succ) src dst)" 
      "bfs_code succ src dst = dRETURN (Some d) 
      \<Longrightarrow> Graph.conn (ls_\<alpha> \<circ> succ) src dst 
          \<and> Graph.min_dist (ls_\<alpha> \<circ> succ) src dst = d"
      "bfs_code succ src dst \<noteq> dFAIL"
      apply (unfold bfs_spec_def)
      apply (auto split: option.split_asm)
      done
  qed
      
  text {* Now we can use the code-generator of Isabelle/HOL to generate
    code into various target languages: *}
  export_code bfs_code in SML file -
  export_code bfs_code in OCaml file -
  export_code bfs_code in Haskell file -
  export_code bfs_code in Scala file -

  text {* The generated code is most conveniently executed within 
    Isabelle/HOL itself. We use a small test graph here: *}

  definition nat_list:: "nat list \<Rightarrow> _" where "nat_list \<equiv> dlist_of_list"
  ML {*
    (* Define a test graph. *)
    fun succ 1 = @{code nat_list} [2,3]
        | succ 2 = @{code nat_list} [4]
        | succ 4 = @{code nat_list} [5]
        | succ 5 = @{code nat_list} [2]
        | succ 3 = @{code nat_list} [6]
        | succ _ = @{code nat_list} [];

    (* Execute algorithm for some node pairs. *)
    @{code bfs_code} succ 1 1;
    @{code bfs_code} succ 1 2;
    @{code bfs_code} succ 1 5;
    @{code bfs_code} succ 1 7;
    *}

end
