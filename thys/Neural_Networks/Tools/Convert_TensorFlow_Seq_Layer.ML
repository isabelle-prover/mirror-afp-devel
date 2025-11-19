(***********************************************************************************
 * Copyright (c) 2022-2023 University of Exeter, UK
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

structure Convert_TensorFlow_Seq_Layer :CONVERT_TENSORFLOW_SEQ_LAYER = struct
   datatype layer_type = List | Matrix
   type layer_config =   {ActivationRecordC: term, DenseC: term, InC: term, InOutRecordC: term, LayerRecordC: term, OutC: term, activation_term: Activation_Term.mode, biasT_conv: term -> term, layer_def: thm, layer_extC: term, layersT: typ, locale_name: string, ltype: typ, phiT: typ, valid_activation_tab: thm, weightsT_conv: term -> int -> term}

   val mk_nat = HOLogic.mk_number \<^typ>\<open>nat\<close>
   val mk_real = Nano_Json_Type.term_of_real 

   val make_const_def = Nano_Json_Parser_Isar.make_const_def

   fun define_lemmas name thm_names = Specification.theorems_cmd "" 
                                  [((name, []), map (fn n => (Facts.named n, [])) thm_names)] 
                                  [] false
(*******************)
(* TODO: also implemented in Convert_TensorFlow_Json *)
fun enumerate _ [] = []
  | enumerate n [x] = [(n,x)]
  | enumerate n (x::xs) = (n,x)::(enumerate (n+1) xs)

fun convert_weights [] = []
  | convert_weights [x] = List.map (fn e => [e]) x
  | convert_weights (x::xs) = let
                                val enum =  rev (map fst (enumerate 0 (x)))
                              in
                                 List.foldl (fn (n,a) => (map (fn l => List.nth(l,n)) (x::xs))::a) [] enum
                              end

(********************)
    fun term_of_layer layer_config verbose (l:IEEEReal.decimal_approx TensorFlow_Type.layer) = 
        let 
           val InC    = (#InC layer_config)
           val OutC   = (#OutC layer_config)
           val DenseC = (#DenseC layer_config)
           val InOutRecordC = (#InOutRecordC layer_config)
           val LayerRecordC = (#LayerRecordC layer_config)
           val ActivationRecordC = (#ActivationRecordC layer_config)
           val biasT = let 
                         val biasListT = (HOLogic.mk_list (@{typ "real"}) (map (mk_real verbose) (#bias l)))
                       in 
                         ((#biasT_conv layer_config) biasListT)
                       end 
           val weightsT = let 
                         val weights = convert_weights (#weights l) 
                         val dim = case weights of [] => 0 | xs => length (hd xs)
                         val weightsLlistT = (HOLogic.mk_list (@{typ "real list"}) 
                                             (map (fn ws => (HOLogic.mk_list (@{typ "real"}) (map (mk_real verbose) ws))) (weights)))
                       in 
                         ((#weightsT_conv layer_config ) weightsLlistT dim)
                       end 
        in 
                (case #layer_type l of 

                            TensorFlow_Type.InputLayer  => (InC$
                                              ((@{const "InOutRecord_ext"(\<open>unit\<close>)}$
                                                (HOLogic.mk_literal (#name l))$(mk_nat (#units l)) $ @{const "Unity"} )))
                          |  TensorFlow_Type.OutputLayer  => (OutC$
                                              (@{const "InOutRecord_ext"(\<open>unit\<close>)}$
                                                (HOLogic.mk_literal (#name l))$(mk_nat (#units l))$ @{const "Unity"} ))
                          | TensorFlow_Type.Dense    => (DenseC$
                                              (InOutRecordC$
                                                (HOLogic.mk_literal (#name l))$(mk_nat (#units l))$ 
                                                 (ActivationRecordC$
                                                   (Activation_Term.term_of_activation_multi (the (#activation l)))$ 
                                                     (LayerRecordC$ 
                                                        biasT$weightsT$
                                                  @{const \<open>Unity\<close>}))))
                         )
         end

  fun def_layer layer_config defN (l:IEEEReal.decimal_approx TensorFlow_Type.layer) lthy 
      = let 
          val thy = Proof_Context.theory_of lthy 
          val verbose = Config.get_global thy json_verbose
        in 
          make_const_def (Binding.qualify_name false (Binding.name (defN^".Layers")) (#name l), term_of_layer layer_config verbose l) lthy
        end

    fun def_layer_list layer_config defN (layers:IEEEReal.decimal_approx TensorFlow_Type.layer list)  lthy =
            let 
              val ltype = (#ltype layer_config)
              val ns_term = HOLogic.mk_list ltype 
               (map (fn l => Const(Local_Theory.full_name lthy  (Binding.qualify_name false (Binding.name (defN^".Layers")) (#name l)), ltype)) layers)
            in
              make_const_def (Binding.qualify_name false (Binding.name defN) "Layers", ns_term) lthy
            end 

    fun collect_phi (l::ls) = (case #activation l of
                                SOME a => a::(collect_phi ls)
                              | NONE   =>    (collect_phi ls))
      | collect_phi [] = []


    fun def_nn layer_config defN lthy = 
           let 
             val Phi = Local_Theory.full_name lthy (Binding.qualify_name false (Binding.name defN) ("\<phi>_"^defN))  
             val Layers = Local_Theory.full_name lthy (Binding.qualify_name false (Binding.name defN) "Layers")  
             val def_nn_term = ((#layer_extC layer_config) $ Const(Layers, #layersT layer_config) $ Const(Phi, #phiT layer_config) $ @{const \<open>Unity\<close>})
           in
             make_const_def (Binding.qualify_name false (Binding.name defN) "NeuralNet", def_nn_term) lthy
           end 

    fun interpretation_nn_seq_layer layer_config defN lthy =
      let
        val proof_mode = get_nn_proof_mode lthy
        val _ = nn_log.info 2 "interpretation_nn_seq_layer: " lthy 
        fun mk_ctx_ss ctx thms = ctx addsimps thms
        val meth = (Method.Basic (fn ctx => Method.SIMPLE_METHOD (
                print_tac ctx "Unfolding locale neural_network_sequential_layers NeuralNet"
                     THEN simp_tac (mk_ctx_ss ctx ([#layer_def layer_config])) 1
                THEN print_tac ctx "Separating locale axioms into subgoals"
                     THEN safe_tac ctx  
                THEN print_tac ctx "Proving first axiom: isIn (list.hd (layers NeuralNet))" 
                     THEN simp_tac (mk_ctx_ss ctx (([ Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "Layers_def")),
                                     Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "NeuralNet_def")),
                                     #layer_def layer_config,
                                     @{thm o_def}]))) 1
                     THEN simp_tac (mk_ctx_ss ctx ((Proof_Context.get_thms ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "layer_defs")))@[
                                     @{thm o_def}])) 1
                THEN print_tac ctx "Proving second axiom: isOut (last (layers NeuralNet))" 
                     THEN simp_tac (mk_ctx_ss ctx (([Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "Layers_def")),
                                     Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "NeuralNet_def")),
                                     #layer_def layer_config,
                                     @{thm o_def}]))) 1
                     THEN simp_tac (mk_ctx_ss ctx ((Proof_Context.get_thms ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "layer_defs")))@[
                                     @{thm o_def}])) 1
                THEN print_tac ctx "Proving third axiom: list_all isInternal (list.tl (butlast (layers NeuralNet)))" 
                     THEN simp_tac (mk_ctx_ss ctx (([Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "Layers_def")),
                                     Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "NeuralNet_def")),
                                     #layer_def layer_config,
                                     @{thm o_def}]))) 1
                THEN nn_tactics.eval_or_normalize_tac ctx ctx 1
                THEN print_tac ctx "Proving fourth axiom: valid_activation_tab\<^sub>l (neural_network_seq_layers.activation_tab NeuralNet)"
                       THEN simp_tac (mk_ctx_ss ctx ([#valid_activation_tab layer_config,
                                     Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "NeuralNet_def")),
                                     Proof_Context.get_thm ctx (Local_Theory.full_name  ctx (Binding.qualify_name false (Binding.name (defN)) "\<phi>_ran"))
                                   ])) 1
                THEN print_tac ctx "Proving fith axiom: layers_consistent NeuralNet (in_deg_NN NeuralNet) (layers NeuralNet)"
                THEN nn_tactics.eval_or_normalize_tac ctx ctx 1
              )))
        fun f x y z = ([((x,Position.none),((y,true),(Expression.Positional z ,[])))],[])
        val pexpr = f (#locale_name layer_config) defN [SOME (defN^".NeuralNet")]
        val proof_state = Interpretation.global_interpretation_cmd pexpr [] lthy
      in
        case proof_mode of SKIP => lthy 
           | _ =>  nn_tactics.prove_method_simple proof_mode meth proof_state
      end

  fun def_seq_layer_nn layer_config defN _ _ (json:Nano_Json_Type.json) lthy = let
      val log = nn_log.info 0 "def_seq_layer_nn: " lthy 
      val layers = json |> TensorFlow_Json.convert_layers 
      val phis   = collect_phi layers 
    in lthy                
       |> log ("start encoding")
       |> (snd o Local_Theory.begin_nested)
       |> Local_Theory.end_nested
       |> (snd o Local_Theory.begin_nested)
       |> Activation_Term.def_phi_tab (#activation_term layer_config) defN phis
       |> Local_Theory.end_nested
       |> (snd o Local_Theory.begin_nested)
       |> fold_map (def_layer layer_config defN)  layers
       |> snd
       |> Local_Theory.end_nested
       |> (snd o Local_Theory.begin_nested)
       |> define_lemmas  (Binding.qualify_name false (Binding.name defN) "layer_defs")
                         (map (fn l => "Layers."^(#name l)^"_def") layers)
       |> snd
       |> Local_Theory.end_nested
       |> (snd o Local_Theory.begin_nested)
       |> def_layer_list layer_config defN layers
       |> snd
       |> Local_Theory.end_nested
       |> def_nn layer_config defN 
       |> snd
       |> log ("locale interpretation")
       |> interpretation_nn_seq_layer layer_config defN
       |> log ("end encoding")
    end
end 
