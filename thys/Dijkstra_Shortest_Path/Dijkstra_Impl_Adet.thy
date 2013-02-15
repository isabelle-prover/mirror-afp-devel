header {* Implementation of Dijkstra's-Algorithm using Automatic Determinization *}
theory Dijkstra_Impl_Adet
imports Dijkstra GraphSpec HashGraphImpl "~~/src/HOL/Library/Code_Target_Numeral"
  "../Refine_Monadic/Autoref_Collection_Bindings"
begin 

locale dijkstraC_def =
  g!: StdGraphDefs g_ops +
  mr!: StdMapDefs mr_ops +
  qw!: StdUprioDefs qw_ops 
  for g_ops :: "('V,'W::weight,'G,'moreg) graph_ops_scheme"
  and mr_ops :: "('V, (('V,'W) path \<times> 'W), 'mr, 'more_mr) map_ops_scheme"
  and qw_ops :: "('V ,'W infty,'qw, 'more_qw) uprio_ops_scheme" +
  fixes nodes_it :: "('V, 'W, 'qw, 'G) graph_nodes_it"
  fixes succ_it :: "('V, 'W, 'qw\<times>'mr, 'G) graph_succ_it" 
  fixes v0 :: "'V"
  fixes ga :: "('V,'W) graph"
  fixes g :: 'G
begin
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
  and succ_it :: "('V, 'W, 'qw\<times>'mr, 'G) graph_succ_it" 
  and ga::"('V,'W) graph" and V :: "'V set" and "v0"::'V and g :: 'G+
  assumes in_abs: "g.\<alpha> g = ga"
  assumes g_invar[simp, intro!]: "g.invar g"
begin

  lemma ga_trans: "(g,ga)\<in>br g.\<alpha> g.invar" using in_abs by auto

  lemma ga_nodes_trans: "(nodes (g.\<alpha> g),nodes ga)\<in>Id" using in_abs by auto
  lemma ga_succs_trans: "(v,v')\<in>Id \<Longrightarrow> (succ (g.\<alpha> g) v,succ ga v')\<in>Id" 
    using in_abs by auto

  schematic_lemma cdijkstra_refines_aux: 
    notes [autoref_spec] = 
      spec_R[where 'c="bool" and 'a="bool"]
      spec_R[where 'c="'V" and 'a="'V"]
      spec_R[where 'c="'W" and 'a="'W"]
      spec_R[where 'c="'W infty" and 'a="'W infty"]
      (*spec_R[where 'c="'W infty option" and 'a="'W infty option"]*)
      spec_R[where 'c="'mr" and 'a="'V\<rightharpoonup>(('V,'W) path \<times> 'W)"]
      spec_R[where 'c="'qw" and 'a="'V\<rightharpoonup>'W infty"]
      spec_R[where 'c="('V,'W) path" and 'a="('V,'W) path"]
      spec_R[where 'c="(('V,'W) path \<times> 'W)" and 'a="(('V,'W) path \<times> 'W)"]
      spec_R[where 'c="('V,'W) path option" and 'a="('V,'W) path option"]
      spec_R[where 'c="(('V,'W) path \<times> 'W) option" and 
        'a="(('V,'W) path \<times> 'W) option"]

    notes [autoref_ex] = mr.map_lookup_t ga_succs_trans

    (*notes [[autodet_tracing]]*)
    shows "RETURN (?cdijkstra::'mr) \<le>\<Down>?R  mdijkstra"
    apply (rule autoref_det_optI)
    unfolding mdijkstra_def mdinit_def mpop_min_def prio_pop_min_def 
      mupdate_def
    using ga_trans ga_nodes_trans IdI[of v0]
    apply -
    apply (refine_autoref)
    using g_invar
    apply (refine_transfer) []
    unfolding prod_case_rename
    apply (rule refl)
    done

  notepad begin
    note [[show_types]]
    thm cdijkstra_refines_aux
  end
end

definition (in dijkstraC_def) "cdijkstra \<equiv> 
 (let (a\<Colon>'qw, b\<Colon>'mr) =
        let x\<Colon>'qw =
              (nodes_it\<Colon>'G \<Rightarrow> ('qw \<Rightarrow> bool) \<Rightarrow> ('V \<Rightarrow> 'qw \<Rightarrow> 'qw) \<Rightarrow> 'qw \<Rightarrow> 'qw)
               (g\<Colon>'G) (\<lambda>_\<Colon>'qw. True)
               (\<lambda>(x\<Colon>'V) s\<Colon>'qw.
                   let s\<Colon>'qw = s
                   in upr_insert
                       (qw_ops\<Colon>('V, 'W infty, 'qw,
                                'more_qw) uprio_ops_scheme)
                       s x infty.Infty)
               (upr_empty qw_ops ())
        in (upr_insert qw_ops x (v0\<Colon>'V) (Num (0\<Colon>'W)),
            map_op_update
             (mr_ops\<Colon>('V, ('V \<times> 'W \<times> 'V) list \<times> 'W, 'mr,
                      'more_mr) map_ops_scheme)
             v0 ([], 0\<Colon>'W) (map_op_empty mr_ops ()))
  in Let (while ((\<lambda>a\<Colon>'qw. \<not> upr_isEmpty qw_ops a) \<circ> fst)
           (\<lambda>(aa\<Colon>'qw, ba\<Colon>'mr).
               let (ab\<Colon>'V, bb\<Colon>'W infty \<times> 'qw \<times> 'mr) =
                     let (ab\<Colon>'qw, bb\<Colon>'mr) = (aa, ba);
                         (ac\<Colon>'V, bc\<Colon>'W infty \<times> 'qw) = upr_pop qw_ops ab
                     in case bc of (ad\<Colon>'W infty, bd\<Colon>'qw) \<Rightarrow> (ac, ad, bd, bb)
               in case bb of
                  (ac\<Colon>'W infty, ad\<Colon>'qw, bd\<Colon>'mr) \<Rightarrow>
                    let (ae\<Colon>'qw, be\<Colon>'mr) = (ad, bd);
                        xd\<Colon>('V \<times> 'W \<times> 'V) list option =
                          mpath' (map_op_lookup mr_ops ab be)
                    in (succ_it\<Colon>'G \<Rightarrow> 'V \<Rightarrow> ('qw \<times> 'mr \<Rightarrow> bool)
    \<Rightarrow> ('W \<times> 'V \<Rightarrow> 'qw \<times> 'mr \<Rightarrow> 'qw \<times> 'mr) \<Rightarrow> 'qw \<times> 'mr \<Rightarrow> 'qw \<times> 'mr)
                        g ab (\<lambda>_\<Colon>'qw \<times> 'mr. True)
                        (\<lambda>(x\<Colon>'W \<times> 'V) s\<Colon>'qw \<times> 'mr.
                            let (af\<Colon>'qw, bf\<Colon>'mr) = s
                            in case x of
                               (ag\<Colon>'W, bg\<Colon>'V) \<Rightarrow>
                                 if ac + Num ag
                                    < mpath_weight'
 (map_op_lookup mr_ops bg bf)
                                 then (upr_insert qw_ops af bg
  (ac + Num ag),
 map_op_update mr_ops bg ((ab, ag, bg) # the xd, val ac + ag) bf)
                                 else (af, bf))
                        (ae, be))
           (a, b))
      ((\<lambda>ba\<Colon>'mr. ba) \<circ> snd))
"


context dijkstraC 
begin
  lemma cdijkstra_refines: 
    "RETURN cdijkstra \<le> \<Down>(build_rel mr.\<alpha> mr.invar) mdijkstra"
    by (rule cdijkstra_refines_aux[folded cdijkstra_def])

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
  theorem cdijkstra_correct:
    shows
    "weighted_graph.is_shortest_path_map ga v0 (\<alpha>r (mr.\<alpha> cdijkstra))" (is ?G1)
    and "mr.invar cdijkstra" (is ?G2) 
    and "res_invarm (mr.\<alpha> cdijkstra)" (is ?G3)
  proof -
    note cdijkstra_refines
    also note mdijkstra_refines
    finally have Z: "RETURN cdijkstra \<le> 
      \<Down>(build_rel (\<alpha>r \<circ> mr.\<alpha>) (\<lambda>m. mr.invar m \<and> res_invarm (mr.\<alpha> m))) 
        dijkstra'"
      apply (subst (asm) conc_fun_chain)
      apply rule
      apply (simp only: br_chain)
      done
    also note dijkstra'_refines[simplified]
    also note dijkstra_correct 
    finally show ?G1 ?G2 ?G3 by (auto elim: RETURN_ref_SPECD)
  qed

end

text {*
  Example instantiation with HashSet.based graph, 
  red-black-tree based result map, and finger-tree based priority queue.
*}
definition dijkstra_impl :: 
  "('V::{hashable,linorder},'W::weight) hlg \<Rightarrow> 'V 
  \<Rightarrow> ('V,('V,'W) path \<times> 'W) rm" where
  "dijkstra_impl g v0 \<equiv> 
    dijkstraC_def.cdijkstra rm_ops aluprioi_ops hlg_nodes_it hlg_succ_it v0 g"

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

  from dc.cdijkstra_correct show ?G1 ?G2
    by (auto simp: rm_ops_def dijkstra_impl_def)
qed

lemmas [code] = dijkstraC_def.cdijkstra_def

text {*
  Code can be exported to all available target languages:
*}
export_code dijkstra_impl in SML file -
export_code dijkstra_impl in OCaml file -
export_code dijkstra_impl in Haskell file -
export_code dijkstra_impl in Scala file -

end
