(***********************************************************************************
 * Copyright (c) 2022 University of Exeter, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)


structure Convert_TensorFlow_Digraph:CONVERT_TENSORFLOW_DIGRAPH = struct
  open Convert_TensorFlow_Json     
  open TensorFlow_Digraph_Term
  open Activation_Term  

  val realT = Type ("Real.real", [])
  val unitT     = \<^Type>\<open>unit\<close>
  val activationSingleT =  \<^Type>\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>
  val activationMultiT  =  \<^Type>\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>
  fun neuronT Single    =  \<^Type>\<open>neuron realT activationSingleT\<close>
    | neuronT _     =  \<^Type>\<open>neuron realT activationMultiT\<close>
  fun edgeT Single    =  \<^Type>\<open>edge_ext realT activationSingleT unitT\<close>
    | edgeT _      =  \<^Type>\<open>edge_ext realT activationMultiT unitT\<close>
    
   val make_const_def = Nano_Json_Parser_Isar.make_const_def

  fun fqn_neuron_name defN lthy n = Local_Theory.full_name lthy ((Binding.qualify_name true (Binding.name (defN^".Neurons")) ("N"^Int.toString n)))
  fun fqn_edge_name defN lthy (e:edge) =  Local_Theory.full_name lthy ((Binding.qualify_name true (Binding.name (defN^".Edges")) (("E"^Int.toString(uid_of (#tl e)))^"_"^Int.toString(uid_of (#hd e)))))

  fun term_of_edge defN lthy mode ({tl=tl, weight=weight, hd=hd}:edge) = 
      let 
         val thy = Proof_Context.theory_of lthy
         val verbose = Config.get_global thy json_verbose
         val edge = case mode of 
                         Single => @{const \<open>NN_Digraph.edge.edge_ext\<close>(\<open>real\<close>,\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>,\<open>unit\<close>)}
                       | _  => @{const \<open>NN_Digraph.edge.edge_ext\<close>(\<open>real\<close>,\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>,\<open>unit\<close>)}
      in
        (edge$(Nano_Json_Type.term_of_real verbose weight)$(Const((fqn_neuron_name defN lthy (uid_of tl), neuronT mode)))$
                               (Const((fqn_neuron_name defN lthy (uid_of hd), neuronT mode))) $ @{Const \<open>Unity\<close>})
      end

  fun def_nn mode defN _  _  json lthy = 
    let 
        val nn = json 
                 |> TensorFlow_Json.convert_layers 
                 |> Convert_TensorFlow_Json.mk_neural_network
        val thy = Proof_Context.theory_of lthy
        val verbose = Config.get_global thy json_verbose
        fun mk_neuron_binding n = Binding.qualify_name false (Binding.name (defN^".Neurons"))
                                                      ("N"^Int.toString(uid_of n))
        fun mk_edge_binding (e:edge) = Binding.qualify_name false (Binding.name (defN^".Edges")) 
                                                             ("E"^(Int.toString(uid_of (#tl e)))
                                                           ^"_"^(Int.toString(uid_of (#hd e))))
        fun def_neurons n lthy = 
              make_const_def (mk_neuron_binding n, term_of_neuron verbose mode n) lthy

        fun def_edges e lthy =
              make_const_def  (mk_edge_binding e, term_of_edge defN lthy mode e) lthy

        fun def_neuron_list ns lthy =
            let 
              val ns_term = HOLogic.mk_list (neuronT mode)
               (map (fn n => Const(fqn_neuron_name defN lthy (uid_of n), neuronT mode)) ns)
            in
              make_const_def (Binding.qualify_name false (Binding.name defN) "Neurons", ns_term) lthy
            end 

        fun def_edge_list es lthy =
            let 
              val es_term = HOLogic.mk_list (edgeT mode)
               (map (fn (e:edge) => Const((fqn_edge_name defN lthy e), 
                                 edgeT mode)) es)
            in
              make_const_def (Binding.qualify_name false (Binding.name defN) "Edges", es_term) lthy
            end 

        fun def_graph lthy = 
            let
              val Edges = Local_Theory.full_name lthy (Binding.qualify_name false (Binding.name defN) "Edges")
              val graph_term = case mode of 
                                 Single => @{const \<open>mk_nn_pregraph\<close>(\<open>real\<close>,\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>)}$Const(Edges,HOLogic.listT (edgeT mode))
                               | _      => @{const \<open>mk_nn_pregraph\<close>(\<open>real\<close>,\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>)}$Const(Edges, HOLogic.listT (edgeT mode))
            in
              make_const_def (Binding.qualify_name false (Binding.name defN) "Graph", graph_term) lthy
            end

       fun def_nn lthy = 
           let 
             val Graph = Local_Theory.full_name lthy (Binding.qualify_name false (Binding.name defN) "Graph")
             val Phi = Local_Theory.full_name lthy (Binding.qualify_name false (Binding.name defN) ("\<phi>_"^defN))
             fun def_nn_term Single = (@{const \<open>NN_Digraph.neural_network.neural_network_ext\<close>
                                                (\<open>real\<close>,\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>,\<open>real \<Rightarrow> real\<close>,\<open>unit\<close>)} 
                                 $ Const(Graph, 
                                   @{typ \<open>((real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) neuron, (real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) edge) pre_digraph\<close>})
                                 $ Const(Phi, 
                                    @{typ \<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e \<Rightarrow> (real \<Rightarrow> real) option\<close>})
                                 $ @{const \<open>Unity\<close>})
               | def_nn_term _ = (@{const \<open>NN_Digraph.neural_network.neural_network_ext\<close>
                                                (\<open>real\<close>,\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>,\<open>real list \<Rightarrow> real list\<close>,\<open>unit\<close>)} 
                                 $ Const(Graph,
                                  @{typ \<open> ((real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) neuron, (real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) edge) pre_digraph\<close>})
                                 $ Const(Phi, 
                                    @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real list \<Rightarrow> real list) option\<close>})
                                 $ @{const \<open>Unity\<close>})
           in
             make_const_def (Binding.qualify_name false (Binding.name defN) "NeuralNet", def_nn_term mode) lthy
           end 
    val mk_Trueprop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq

   fun prove_verts_set_conv lthy = 
       let 
         val bgraph = Binding.qualify_name false (Binding.name (defN)) "Graph"
         val bneurons = Binding.qualify_name false (Binding.name (defN)) "Neurons"
         val lhs' = case mode of 
                      Single => 
                             @{const \<open>Digraph.pre_digraph.verts\<close>(\<open>(real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) neuron\<close>,\<open>(real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) edge\<close>,\<open>unit\<close>)}
                             $ Const(Local_Theory.full_name lthy bgraph, @{typ \<open>( (real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e)neuron, (real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e)edge)pre_digraph\<close>})
                    | _       => 
                             @{const \<open>Digraph.pre_digraph.verts\<close>(\<open>(real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) neuron\<close>,\<open>(real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) edge\<close>,\<open>unit\<close>)}
                             $ Const(Local_Theory.full_name lthy bgraph, @{typ \<open>( (real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i)neuron, (real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i)edge)pre_digraph\<close>})
         val rhs' = case mode of 
                      Single => @{const \<open>set\<close>(\<open>(real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) neuron\<close>)}
                                $Const(Local_Theory.full_name lthy bneurons,@{typ\<open>(real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) neuron list\<close>})
                    | _       => @{const \<open>set\<close>(\<open>(real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) neuron\<close>)}
                                $Const(Local_Theory.full_name lthy bneurons,@{typ\<open>(real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) neuron list\<close>})
       in
         nn_tactics.prove_simple (Binding.qualify_name false (Binding.name defN) "verts_set_conv")
                      (mk_Trueprop_eq (lhs',rhs'))
                      (fn s => nn_tactics.eval_or_normalize_tac lthy s 1) lthy
       end

   fun prove_edges_set_conv lthy =
       let 
         val bgraph = Binding.qualify_name false (Binding.name (defN)) "Graph"
         val bedges = Binding.qualify_name false (Binding.name (defN)) "Edges"
         val lhs' = case mode of 
                      Single => @{const \<open>Digraph.pre_digraph.arcs\<close>(\<open>(real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) neuron\<close>,\<open>(real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) edge\<close>,\<open>unit\<close>)}
                                $ Const(Local_Theory.full_name lthy bgraph, @{typ \<open>( (real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e)neuron, (real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e)edge)pre_digraph\<close>})
                    | _       => @{const \<open>Digraph.pre_digraph.arcs\<close>(\<open>(real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) neuron\<close>,\<open>(real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) edge\<close>,\<open>unit\<close>)}
                                $ Const(Local_Theory.full_name lthy bgraph, @{typ \<open>( (real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i)neuron, (real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i)edge)pre_digraph\<close>})
         val rhs' = case mode of 
                      Single => @{const \<open>set\<close>(\<open>(real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) edge\<close>)}
                                  $Const(Local_Theory.full_name lthy bedges,@{typ\<open>(real, activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e) edge list\<close>})
                    | _       => @{const \<open>set\<close>(\<open>(real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) edge\<close>)}
                                  $Const(Local_Theory.full_name lthy bedges,@{typ\<open>(real, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i) edge list\<close>})
       in
         nn_tactics.prove_simple (Binding.qualify_name false (Binding.name defN) "edges_set_conv")
                      (mk_Trueprop_eq (lhs',rhs'))
                      (fn s => nn_tactics.eval_or_normalize_tac lthy s 1) lthy
       end

    fun interpretation_nn_pregraph lthy =
      let
        fun mk_ss ctx thms = put_simpset HOL_basic_ss ctx addsimps thms
        val meth = (Method.Basic (fn ctx => Method.SIMPLE_METHOD (
                simp_tac (mk_ss ctx [Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "Graph_def")), 
                                     @{thm nn_pregraph_def}]) 1
                THEN 
                simp_tac (mk_ss ctx (@{thm nn_pregraph_mk}::(@{thms "nn_pregraph.axioms"}))) 1
              )))
        fun f x y z = ([((x,Position.none),((y,true),(Expression.Positional z,[])))],[])
        val pexpr = f "nn_pregraph" defN [SOME (defN^".Graph")]
        val proof_state = Interpretation.global_interpretation_cmd pexpr [] lthy
      in
        nn_tactics.prove_method_simple (get_nn_proof_mode lthy) meth proof_state
      end

    fun interpretation_neural_network_digraph lthy =
      let
        fun get_local_thm n = Proof_Context.get_thm lthy (Local_Theory.full_name lthy (Binding.qualify_name false (Binding.name (defN)) n))
        fun get_local_thms n = Proof_Context.get_thms lthy (Local_Theory.full_name lthy (Binding.qualify_name false (Binding.name (defN)) n))
        fun mk_ss ctx thms = put_simpset (simpset_of ctx) ctx addsimps thms
        fun simp_meth thms = (Method.Basic (fn ctx => Method.SIMPLE_METHOD (
                 asm_full_simp_tac (mk_ss ctx ([get_local_thm "NeuralNet_def"]@thms)) 1 
                 )))
        val force_meth = (Method.Basic (fn ctx => Method.SIMPLE_METHOD (
                 force_tac (mk_ss ctx ([get_local_thm "NeuralNet_def"])) 1 
                 )))
        val code_simp_meth = (Method.Basic (fn ctx => Method.SIMPLE_METHOD (
                 Code_Simp.dynamic_tac ctx 1 
                 )))
        val normalization_meth = (Method.Basic (fn ctxt => SIMPLE_METHOD' (CHANGED_PROP o
                                                      (CONVERSION (Nbe.dynamic_conv ctxt)
                                                   THEN_ALL_NEW (TRY o resolve_tac ctxt [TrueI])))))
        fun auto_meth thms = (Method.Basic (fn ctx => SIMPLE_METHOD (auto_tac (mk_ss ctx thms))))

        fun f x y z = ([((x,Position.none),((y,true),(Expression.Positional z,[])))],[])
        val pexpr = case mode of 
                      Single => f "neural_network_digraph_single" defN [SOME (defN^".NeuralNet")]
                    | _   => f "neural_network_digraph" defN [SOME (defN^".NeuralNet")]
        val pdefs = [] (* case mode of 
                      Single => [(Binding.empty_atts:Attrib.binding, ((Binding.qualify_name false (Binding.name defN) "predict", NoSyn), "neural_network_digraph_single.predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e"))]
                    | Multi  => [(Binding.empty_atts:Attrib.binding, ((Binding.qualify_name false (Binding.name defN) "predict", NoSyn), "neural_network_digraph.predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h"))] *)
        val proof_state = Interpretation.global_interpretation_cmd pexpr pdefs lthy
       
      in
        proof_state 
        |> Proof.refine_singleton (Method.Source (Token.make_src ("unfold_locales", Position.none) []))
        |> Proof.refine_singleton  (simp_meth [])
        |> Proof.refine_singleton  (simp_meth [])
        |> Proof.refine_singleton  (simp_meth [])
        |> Proof.refine_singleton  (simp_meth [])
        |> Proof.refine_singleton  (simp_meth [get_local_thm "no_loops"])
        |> Proof.refine_singleton  (simp_meth [get_local_thm "no_multi_arcs"])
        |> Proof.refine_singleton  (simp_meth [get_local_thm "id_vert_inj"])
        |> Proof.refine_singleton  (simp_meth [get_local_thm "tail_eq_tl"])
        |> Proof.refine_singleton  (simp_meth [get_local_thm "head_eq_hd"])
        |> Proof.refine_singleton  (simp_meth [get_local_thm "ids_growing"])
        |> Proof.refine_singleton  (simp_meth [Proof_Context.get_thm lthy "input_verts_def"]) |> Proof.refine_singleton  (normalization_meth)
        |> Proof.refine_singleton  (simp_meth [Proof_Context.get_thm lthy "output_verts_def"]) |> Proof.refine_singleton  (normalization_meth)
        |> Proof.refine_singleton  (simp_meth [Proof_Context.get_thm lthy "internal_verts_def"]) |> Proof.refine_singleton  (normalization_meth)
        |> Proof.refine_singleton  (auto_meth (([Proof_Context.get_thm lthy "image_def", Proof_Context.get_thm lthy "dom_def", 
                                                 get_local_thm "NeuralNet_def", get_local_thm "Neurons_def", get_local_thm "verts_set_conv"])
                                               @(get_local_thms "neuron_defs")))
        |> Proof.global_done_proof 
        |> (fn t => (tracing ""; t))
      end                
    in lthy
       |> fold_map def_neurons (#neurons nn)
       |> snd
       |> nn_common_utils.define_lemmas  (Binding.qualify_name false (Binding.name defN) "neuron_defs")
                         (map (fn n => "N"^Int.toString(uid_of n)^"_def") (#neurons nn))
       |> snd
       |> def_neuron_list  (#neurons nn)
       |> snd
       |> fold_map def_edges (#edges nn)
       |> snd
       |> def_edge_list (#edges nn)
       |> snd
       |> nn_common_utils.define_lemmas  (Binding.qualify_name false (Binding.name defN) "edge_defs")
                         (map (fn e => ("E"^Int.toString(uid_of (#tl e)))^"_"^Int.toString(uid_of (#hd e))^"_def") (#edges nn))
       |> snd
       |> def_graph
       |> snd
       |> def_phi_tab mode defN (#activation_tab nn)
       |> def_nn
       |> snd
       |> prove_verts_set_conv
       |> prove_edges_set_conv
       |> interpretation_nn_pregraph 
       |> interpretation_neural_network_digraph
    end
end 
