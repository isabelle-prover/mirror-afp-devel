(***********************************************************************************
 * Copyright (c) University of Exeter, UK
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

subsection\<open>Sequential Layers (\thy)\<close>
theory 
  NN_Layers
  imports
  Activation_Functions
begin 

text\<open>
  In this theory, we model feed-forward neural networks as ``computational layers'' following 
  the structure of TensorFlow~\<^cite>\<open>"abadi.ea:tensorflow:2015"\<close> closely.
\<close>

record InOutRecord = 
       name:: String.literal
       units:: nat


record ('b) ActivationRecord = InOutRecord +
       \<phi> :: 'b


record ('a, 'b, 'c) LayerRecord = \<open>('b) ActivationRecord\<close> + 
       \<beta> :: \<open>'a\<close>
       \<omega> :: \<open>'c\<close> 

datatype ('a, 'b, 'c) layer = In \<open>InOutRecord\<close>                    
                        | Out \<open>InOutRecord\<close>  
                        | Dense \<open>('a,'b, 'c) LayerRecord\<close> 
                        | Activation \<open>('b) ActivationRecord\<close> 

fun units\<^sub>l where 
   \<open>units\<^sub>l (In l) = units l\<close>
 | \<open>units\<^sub>l (Out l) = units l\<close>
 | \<open>units\<^sub>l (Dense l) = units l\<close>
 | \<open>units\<^sub>l (Activation l) = units l\<close>

lemmas [nn_layer] = InOutRecord.simps ActivationRecord.simps LayerRecord.simps layer.simps units\<^sub>l.simps
                        
text\<open>
  The datatype @{type "layer"} models the currently supported layer types
\<close>

text \<open>As we are using a representation of a network as a list of layers, we also
support different layer types and their computations. Currently, our sequential
layers model supports five layer types @{term "In (input::InOutRecord)"} (input layer), 
@{term "Out (output::InOutRecord)"} (output layer), 
@{term "Dense (dense_layer::('a, 'b, 'c) LayerRecord)"} (dense layer),  and 
@{term "Activation (activation_layer::'b ActivationRecord)"} (activation layer).
As we allow for the abstraction of activation functions, we abstract from the actual type
for the activation function (modelled by the type variable @{typ "'b"} and from the 
actual type of weight and bias (modelled by the type variables @{typ "'a"} and @{typ "'c"} 
respectively).

Therefore, we do not need to model TensorFlow's Lambda layer explicitly
(which is TensorFlow's mechanism for supporting custom activation functions).\<close>

text \<open>Each @{type "LayerRecord"} contains the activation, weights and bias in our network 
@{term "\<phi>"}, @{term "\<beta>"} and @{term "\<omega>"} respectively), while our @{type "ActivationRecord"} 
only contains our abstracted activation function. \<close>

fun isIn where
    \<open>isIn (In _) = True\<close>
  | \<open>isIn _      = False\<close>

fun isOut where
    \<open>isOut (Out _) = True\<close>
  | \<open>isOut _       = False\<close>

fun isInternal where
    \<open>isInternal (Out _) = False\<close>
  | \<open>isInternal (In _)  = False\<close>
  | \<open>isInternal _       = True\<close>

lemma isInternal': \<open>isInternal n = (\<not> (isIn n) \<and> \<not> (isOut n))\<close>
  by (metis isIn.elims(2) isIn.simps(1) isInternal.elims(3) isInternal.simps(1) isInternal.simps(2) 
            isOut.elims(2) isOut.simps(1)) 

record ('a, 'b,'c) neural_network_seq_layers = 
  layers ::  \<open>('a, 'b, 'c) layer  list\<close>
  activation_tab :: \<open>'b \<Rightarrow> (('a \<Rightarrow> 'a ) option)\<close>

lemmas [nn_layer] = neural_network_seq_layers.simps

text \<open>For this encoding of a neural network, we mostly follow TensorFlow Sequential model 
\<^cite>\<open>"abadi.ea:tensorflow:2015"\<close> and represent our network as a sequential list of layers 
with an abstract table of activation functions, allowing for extensible and customisable 
functionality. The record @{typ "('a, 'b, 'c) neural_network_seq_layers"} represents our network where 
@{typ "'a"} is type variable representing the type of our bias, @{typ "'b"} is the 
type of the activation function, and @{typ "'c"} is the type variable representing the type of our
weights.\<close>

fun  out_deg_layer 
where 
   \<open>out_deg_layer (In l) = (units l)\<close>
 | \<open>out_deg_layer (Out l) = (units l)\<close>
 | \<open>out_deg_layer (Activation l) = units l\<close>
 | \<open>out_deg_layer (Dense l) = units l\<close>
 
fun units_layer where
   \<open>units_layer (In l) = units l\<close>
 | \<open>units_layer (Out l) = units l\<close>
 | \<open>units_layer (Activation l) = units l\<close> 
 | \<open>units_layer (Dense l) = units l\<close>

fun \<phi>_layer where
   \<open>\<phi>_layer (In l) = None\<close>
 | \<open>\<phi>_layer (Out l) = None\<close>
 | \<open>\<phi>_layer (Activation l) = Some (\<phi> l)\<close> 
 | \<open>\<phi>_layer (Dense l) = Some (\<phi> l)\<close>

fun in_deg_layer where
  "in_deg_layer (In l) = units l"
| "in_deg_layer (Out l) = units l"
| "in_deg_layer (Activation l) =  units l" 
| "in_deg_layer (Dense l) = length (\<omega> l ! 0)"

lemmas [nn_layer] = out_deg_layer.simps units_layer.simps \<phi>_layer.simps

definition 
  \<open>out_deg_NN  N = (if layers N = [] then 0 else (units_layer \<circ> last \<circ> layers) N)\<close>

definition 
  \<open>in_deg_NN  N = (if layers N = [] then 0 else (units_layer \<circ> hd \<circ> layers) N)\<close>


ML\<open>
signature CONVERT_TENSORFLOW_SEQ_LAYER = 
  sig
    type layer_config =   {ActivationRecordC: term, DenseC: term, InC: term, InOutRecordC: term, LayerRecordC: term, OutC: term, activation_term: Activation_Term.mode, biasT_conv: term -> term, layer_def: thm, layer_extC: term, layersT: typ, locale_name: string, ltype: typ, phiT: typ, valid_activation_tab: thm, weightsT_conv: term -> int -> term}
   val def_seq_layer_nn: layer_config -> bstring -> typ -> typ -> Nano_Json_Type.json -> local_theory 
                          -> Proof.context
  end

\<close>

ML_file\<open>Tools/Convert_TensorFlow_Seq_Layer.ML\<close> 

end 
