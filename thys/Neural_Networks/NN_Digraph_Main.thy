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

section\<open>Main Theory (Digraph)\<close>
theory
  NN_Digraph_Main
imports
  NN_Common
  NN_Digraph
  Activation_Functions
  Properties
begin
text\<open>\label{thy:NN_Digraph_Main}\<close>

ML\<open>
signature CONVERT_TENSORFLOW_JSON = sig
  datatype neuron = In of int | Out of int 
                  | Neuron of {phi:TensorFlow_Type.activationT, bias:IEEEReal.decimal_approx, uid:int} 
  type edge = {
                tl:neuron, 
                weight:IEEEReal.decimal_approx, 
                hd:neuron
              }
  type neural_network = {
                          edges: edge list,
                          neurons: neuron list,
                          activation_tab: TensorFlow_Type.activationT list
                        }
  val uid_of: neuron -> int
 
  val mk_neural_network: IEEEReal.decimal_approx TensorFlow_Type.layer list -> neural_network
end
\<close>
ML_file\<open>Tools/Convert_TensorFlow_Json.ML\<close>

ML\<open>

signature TENSORFLOW_DIGRAPTH_TERM = sig
  val term_of_neuron: bool -> Activation_Term.mode -> Convert_TensorFlow_Json.neuron -> term
end
\<close>

ML_file \<open>Tools/TensorFlow_Digraph_Term.ML\<close>

ML\<open>
signature CONVERT_TENSORFLOW_DIGRAPH =
  sig
    val def_nn: Activation_Term.mode -> string -> 'a -> 'b -> Nano_Json_Type.json -> local_theory -> Proof.context
  end
\<close>

ML_file\<open>Tools/Convert_TensorFlow_Digraph.ML\<close>

ML\<open>
  val _ = Theory.setup
           (Convert_TensorFlow_Symtab.add_encoding("digraph", 
                                 Convert_TensorFlow_Digraph.def_nn Activation_Term.MultiList))
  val _ = Theory.setup
           (Convert_TensorFlow_Symtab.add_encoding("digraph_single", 
                                 Convert_TensorFlow_Digraph.def_nn Activation_Term.Single))
\<close>

end

