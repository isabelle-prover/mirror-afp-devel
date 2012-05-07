header {* Implementation of Dijkstra's-Algorithm using the ICF *}
theory Dijkstra_Impl
imports Dijkstra GraphSpec HashGraphImpl "~~/src/HOL/Library/Efficient_Nat"
begin 
text{*
  In this second refinement step, we use interfaces from the 
  Isabelle Collection Framework (ICF) to implement the priority queue and
  the result map. Moreover, we use a graph interface (that is not contained 
  in the ICF, but in this development) to represent the graph.

  The data types of the first refinement step were designed to fit the
  abstract data types of the used ICF-interfaces, which makes this refinement
  quite straightforward.

  Finally, we instantiate the ICF-interfaces by concrete implementations, 
  obtaining an executable algorithm, for that we generate code using 
  Isabelle/HOL's code generator.
*}


text {*
  Due to idiosyncrasies of the code generator, we have to split the
  locale for the definitions, and the locale that assumes the preconditions.
*}
locale dijkstraC_def =
  g!: StdGraphDefs g_ops +
  mr!: StdMapDefs mr_ops +
  qw!: StdUprioDefs qw_ops 
  for g_ops :: "('V,'W::weight,'G,'moreg) graph_ops_scheme"
  and mr_ops :: "('V, (('V,'W) path \<times> 'W), 'mr, 'more_mr) map_ops_scheme"
  and qw_ops :: "('V ,'W infty,'qw, 'more_qw) uprio_ops_scheme" 
  and nodes_it :: "('V, 'W, 'qw, 'G) graph_nodes_it"
  and succ_it :: "('V, 'W, ('qw\<times>'mr), 'G) graph_succ_it" 
+
  fixes v0 :: "'V"
  fixes ga :: "('V,'W) graph"
  fixes g :: 'G
begin
  definition "\<alpha>sc == map_pair qw.\<alpha> mr.\<alpha>"
  definition "dinvarC_add == \<lambda>(wl,res). qw.invar wl \<and> mr.invar res"

  definition cdinit :: "('qw\<times>'mr) nres" where
    "cdinit \<equiv> do {
      wl \<leftarrow> FOREACH (nodes ga) 
        (\<lambda>v wl. RETURN (qw.insert wl v Weight.Infty)) (qw.empty ());
      RETURN (qw.insert wl v0 (Num 0),mr.sng v0 ([],0))
    }"

  definition cpop_min :: "('qw\<times>'mr) \<Rightarrow> ('V\<times>'W infty\<times>('qw\<times>'mr)) nres" where
    "cpop_min \<sigma> \<equiv> do {
      let (wl,res) = \<sigma>; 
      let (v,w,wl')=qw.pop wl;
      RETURN (v,w,(wl',res))
    }"

  definition cupdate :: "'V \<Rightarrow> 'W infty \<Rightarrow> ('qw\<times>'mr) \<Rightarrow> ('qw\<times>'mr) nres" where
    "cupdate v wv \<sigma> = do {
      ASSERT (dinvarC_add \<sigma>);
      let (wl,res)=\<sigma>;
      let pv=mpath' (mr.lookup v res);
      FOREACH (succ ga v) (\<lambda>(w',v') (wl,res).
        if (wv + Num w' < mpath_weight' (mr.lookup v' res)) then do {
          RETURN (qw.insert wl v' (wv+Num w'), 
                  mr.update v' ((v,w',v')#the pv,val wv + w') res)
        } else RETURN (wl,res)
      ) (wl,res)
    }"

  definition cdijkstra where
    "cdijkstra \<equiv> do {
      \<sigma>0 \<leftarrow> cdinit; 
      (_,res) \<leftarrow> WHILE\<^isub>T (\<lambda>(wl,_). \<not> qw.isEmpty wl) 
            (\<lambda>\<sigma>. do { (v,wv,\<sigma>') \<leftarrow> cpop_min \<sigma>; cupdate v wv \<sigma>' } )
            \<sigma>0;
      RETURN res
    }"

end

locale dijkstraC =
  dijkstraC_def g_ops mr_ops qw_ops nodes_it succ_it v0 ga g +
  Dijkstra ga v0 +
  g!: StdGraph g_ops + 
  mr!: StdMap mr_ops +
  qw!: StdUprio qw_ops +
  g!: graph_nodes_it g.\<alpha> g.invar nodes_it +
  g!: graph_succ_it g.\<alpha> g.invar succ_it
  for g_ops :: "('V,'W::weight,'G,'moreg) graph_ops_scheme"
  and mr_ops :: "('V, (('V,'W) path \<times> 'W), 'mr,'more_mr) map_ops_scheme"
  and qw_ops :: "('V ,'W infty,'qw,'more_qw) uprio_ops_scheme" 
  and nodes_it :: "('V, 'W, 'qw, 'G) graph_nodes_it"
  and succ_it :: "('V, 'W, ('qw\<times>'mr), 'G) graph_succ_it" 
  and ga::"('V,'W) graph" and V :: "'V set" and "v0"::'V and g :: 'G+
  assumes in_abs: "g.\<alpha> g = ga"
  assumes g_invar[simp, intro!]: "g.invar g"
begin

  schematic_lemma cdinit_refines: 
    notes [refine] = inj_on_id
    shows "cdinit \<le>\<Down>?R mdinit"
    unfolding cdinit_def mdinit_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (simp_all add: \<alpha>sc_def dinvarC_add_def
      qw.correct mr.correct)
    done

  schematic_lemma cpop_min_refines:
    "(\<sigma>,\<sigma>') \<in> build_rel \<alpha>sc dinvarC_add
      \<Longrightarrow> cpop_min \<sigma> \<le> \<Down>?R (mpop_min \<sigma>')"
    unfolding cpop_min_def mpop_min_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (simp add: \<alpha>sc_def dinvarC_add_def)
    apply (simp add: \<alpha>sc_def dinvarC_add_def)
    done

  schematic_lemma cupdate_refines:
    notes [refine] = inj_on_id
    shows "(\<sigma>,\<sigma>')\<in>build_rel \<alpha>sc dinvarC_add \<Longrightarrow> v=v' \<Longrightarrow> wv=wv' \<Longrightarrow> 
    cupdate v wv \<sigma> \<le> \<Down>?R (mupdate v' wv' \<sigma>')"
    unfolding cupdate_def mupdate_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (simp_all add: \<alpha>sc_def dinvarC_add_def 
      qw.correct mr.correct)
    done

  lemma cdijkstra_refines: "cdijkstra \<le> \<Down>(build_rel mr.\<alpha> mr.invar) mdijkstra"
  proof -
    note [refine] = cdinit_refines cpop_min_refines cupdate_refines
    show ?thesis
      unfolding cdijkstra_def mdijkstra_def
      apply (refine_rcg)

      apply (simp_all 
        split: prod.split prod.split_asm 
        add: qw.correct mr.correct dinvarC_add_def \<alpha>sc_def)
      done
  qed

  schematic_lemma idijkstra_refines_aux: 
    notes [refine_transfer] = g_invar
    shows "RETURN ?f \<le> cdijkstra"
    unfolding cdijkstra_def cdinit_def cpop_min_def cupdate_def 
    unfolding in_abs[symmetric]
    apply (refine_transfer)
    done

  thm idijkstra_refines_aux[no_vars]

end


  text {* Copy-Pasted from the above lemma: *}
  definition (in dijkstraC_def) "idijkstra \<equiv> 
 (let x = let x = nodes_it g (\<lambda>_. True)
                   (\<lambda>x s. let s = s in upr_insert qw_ops s x infty.Infty)
                   (upr_empty qw_ops ())
          in (upr_insert qw_ops x v0 (Num (0\<Colon>'W)),
              map_op_sng mr_ops v0 ([], 0\<Colon>'W));
      (a, b) =
        while (\<lambda>(wl, _). \<not> upr_isEmpty qw_ops wl)
         (\<lambda>xa. let (a, b) =
                     let (a, b) = xa; (aa, ba) = upr_pop qw_ops a
                     in case ba of (ab, bb) \<Rightarrow> (aa, ab, bb, b)
               in case b of
                  (aa, ba) \<Rightarrow>
                    let (ab, bb) = ba;
                        xd = mpath' (map_op_lookup mr_ops a bb)
                    in succ_it g a (\<lambda>_. True)
                        (\<lambda>x s. let s = s
                               in case x of
                                  (ac, bc) \<Rightarrow>
                                    case s of
                                    (ad, bd) \<Rightarrow>
if aa + Num ac < mpath_weight' (map_op_lookup mr_ops bc bd)
then (upr_insert qw_ops ad bc (aa + Num ac),
      map_op_update mr_ops bc ((a, ac, bc) # the xd, val aa + ac) bd)
else (ad, bd))
                        (ab, bb))
         x
  in b)
"


text {*
  Example instantiation with HashSet.based graph, 
  red-black-tree based result map, and finger-tree based priority queue.
*}
definition dijkstra_impl :: 
  "('V::{hashable,linorder},'W::weight) hlg \<Rightarrow> 'V 
  \<Rightarrow> ('V,('V,'W) path \<times> 'W) rm" where
  "dijkstra_impl g v0 \<equiv> 
    dijkstraC_def.idijkstra rm_ops aluprioi_ops hlg_nodes_it hlg_succ_it v0 g"

lemmas [code] = dijkstraC_def.idijkstra_def

text {*
  Code can be exported to all available target languages:
*}
export_code dijkstra_impl in SML file -
export_code dijkstra_impl in OCaml file -
export_code dijkstra_impl in Haskell file -
export_code dijkstra_impl in Scala file -


context dijkstraC
begin
  lemma idijkstra_refines: "RETURN idijkstra \<le> cdijkstra"
    by (rule idijkstra_refines_aux[folded idijkstra_def])
  text {*
    The following theorem states correctness of the algorithm independent
    from the refinement framework.
    
    Intuitively, the first goal states that the abstraction of the returned 
    result is correct, the second goal states that the result
    datastructure satisfies its invariant, and the third goal states 
    that the cached weights in the returned result are correct.

    Note that this is the main theorem for a user of Dijkstra's algorithm in some 
    bigger context. It may also be specialized for concrete instances of the
    implementation, as exemplarily done below.
    *}
  theorem (in dijkstraC) idijkstra_correct:
    shows
    "weighted_graph.is_shortest_path_map ga v0 (\<alpha>r (mr.\<alpha> idijkstra))" (is ?G1)
    and "mr.invar idijkstra" (is ?G2) 
    and "res_invarm (mr.\<alpha> idijkstra)" (is ?G3)
  proof -
    note idijkstra_refines
    also note cdijkstra_refines
    also note mdijkstra_refines
    finally have Z: "RETURN idijkstra \<le> 
      \<Down>(build_rel (\<alpha>r \<circ> mr.\<alpha>) (\<lambda>m. mr.invar m \<and> res_invarm (mr.\<alpha> m))) 
        dijkstra'"
      apply (subst (asm) conc_fun_chain)
      apply rule
      apply (simp only: br_chain)
      done
    also note dijkstra'_refines[simplified]
    also note dijkstra_correct 
    finally show ?G1 ?G2 ?G3 
      by (auto elim: RETURN_ref_SPECD)
  qed

end

text {*
  We also specialize the correctness theorem.
  Note that the data structure invariant for red-black trees is encoded into
  the type, and hence @{term "rm_invar"} is constantly @{text "True"}. Hence, it
  is not stated in this theorem.
*}
theorem dijkstra_impl_correct:
  assumes INV: "hlg_invar g"
  assumes V0: "v0 \<in> nodes (hlg_\<alpha> g)"
  assumes nonneg_weights: "\<And>v w v'. (v,w,v')\<in>edges (hlg_\<alpha> g) \<Longrightarrow> 0\<le>w"
  shows 
  "weighted_graph.is_shortest_path_map (hlg_\<alpha> g) v0 
      (Dijkstra.\<alpha>r (rm_\<alpha> (dijkstra_impl g v0)))" (is ?G1)
  and "Dijkstra.res_invarm (rm_\<alpha> (dijkstra_impl g v0))" (is ?G2)
proof -
  interpret hlgv!: valid_graph "hlg_\<alpha> g" using hlg.valid INV .
  interpret hlgv!: 
    graph_nodes_it "gop_\<alpha> hlg_ops" "gop_invar hlg_ops" hlg_nodes_it
    by (auto simp: hlg_nodes_it_impl hlg_ops_def)
  interpret hlgv!: graph_succ_it "gop_\<alpha> hlg_ops" "gop_invar hlg_ops" hlg_succ_it
    by (auto simp: hlg_succ_it_impl hlg_ops_def)

  interpret dc: dijkstraC hlg_ops rm_ops aluprioi_ops hlg_nodes_it hlg_succ_it 
    "hlg_\<alpha> g"
    apply unfold_locales 
    apply (simp_all add: hlg.finite INV V0 hlg_ops_def nonneg_weights)
    done

  from dc.idijkstra_correct show ?G1 ?G2
    by (auto simp: rm_ops_def dijkstra_impl_def)
qed

end
