(***********************************************************************************
 * Copyright (c) 2021-2022 University of Exeter, UK
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

structure Convert_TensorFlow_Json:CONVERT_TENSORFLOW_JSON  = struct
   open TensorFlow_Type
   open Nano_Json_Type
   open Nano_Json_Query
   



datatype neuron = In of int | Out of int | Neuron of {phi:activationT, bias:IEEEReal.decimal_approx, uid:int} 
type edge = {tl:neuron, weight:IEEEReal.decimal_approx, hd:neuron}

fun uid_of (In uid)  = uid
  | uid_of (Out uid) = uid
  | uid_of (Neuron r) = #uid r


fun mkInOut mk offset i = if i < 2 then [mk offset] else (mk offset)::(mkInOut mk (offset+1) (i-1))
fun mkNeuron phi offset (b::bs) = [Neuron {phi=phi, bias=b, uid= offset}]@(mkNeuron phi (offset+1)) bs
  | mkNeuron _  _ [] = []

fun neurons_of_layers offset _ ({layer_type = InputLayer, units=i, ...}:IEEEReal.decimal_approx layer) =  
                               if i < 1 then error "Input layer with zero or negative arity."
                                        else mkInOut In offset i
  | neurons_of_layers offset _ ({layer_type = OutputLayer, units=i, ...}:IEEEReal.decimal_approx layer) =  
                               if i < 1 then error "Output layer with zero or negative arity."
                                        else mkInOut Out offset i
  | neurons_of_layers offset _ ({layer_type = Dense, activation=SOME a, bias=b,... })  = mkNeuron a offset b 
  | neurons_of_layers _ _ ({layer_type = Dense, activation=NONE, ... })  = error "Dense layer without activation function."

fun pair (x::xs) (y::ys) = (x,y)::(pair xs ys)
  | pair [] [] = []
  | pair _ [] = error "Error in pair"
  | pair [] _ = error "Error in pair"


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
fun mk_edges OutputLayer (c::current_edges) (p::previous_edges) weights = ({tl=p,
                                                                            weight=Real.toDecimal 1.0, 
                                                                            hd=c})::
                                         (mk_edges OutputLayer current_edges previous_edges weights) 
  | mk_edges OutputLayer [] [] _ = []
  | mk_edges OutputLayer _ [] _ = error "To few neurons in output layer."
  | mk_edges OutputLayer [] _ _ = error "To many neurons in output layer."
  |  mk_edges InputLayer _ _  _ = []
  | mk_edges Dense current previous  (weights:IEEEReal.decimal_approx list list) 
        = map (fn (head,w) => map (fn (tail,w') => ({tl=tail,weight=w',hd=head})) (pair previous w)) (pair current (convert_weights weights)) 
                                         |> List.concat

    type neural_network = {
        edges: edge list,
        neurons: neuron list,
        activation_tab : TensorFlow_Type.activationT list
    }

  fun build_layer layer ((edges, (neurons, phis)), (previous_neurons, offset)) =
      let
        val current_neurons = neurons_of_layers offset [] layer
        val edges' = mk_edges (#layer_type layer) current_neurons previous_neurons (#weights layer)
        val phis'  = case #activation layer of 
                          NONE => phis 
                        | SOME p => if List.exists (fn e => e=p) phis then phis else p::phis  
      in
        ((edges'@edges, (neurons@current_neurons, phis')), (current_neurons, offset+(#units layer)))
      end
  
  fun mk_edges_neurons_phi layers = fold build_layer layers (([], ([], [])), ([], 0)) |> fst
  
  fun mk_neural_network layers = 
      let 
          val (edges, (neurons, phis)) = mk_edges_neurons_phi layers 
      in
          {edges=edges, neurons=neurons, activation_tab = phis}
      end

  end

