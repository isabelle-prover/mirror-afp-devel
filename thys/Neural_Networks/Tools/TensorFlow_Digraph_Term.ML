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

structure TensorFlow_Digraph_Term:TENSORFLOW_DIGRAPTH_TERM = struct
  open Activation_Term  
  open Convert_TensorFlow_Json              
 
  val mk_nat = HOLogic.mk_number \<^typ>\<open>nat\<close>
  val mk_real = Nano_Json_Type.term_of_real 

fun term_of_neuron _ Single (In uid)  = @{const \<open>NN_Digraph.neuron.In\<close>(\<open>real\<close>,\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>)}$(mk_nat uid)
  | term_of_neuron _ _  (In uid) = @{const \<open>NN_Digraph.neuron.In\<close>(\<open>real\<close>,\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>)}$(mk_nat uid)
  | term_of_neuron _ Single (Out uid) = @{const \<open>NN_Digraph.neuron.Out\<close>(\<open>real\<close>,\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>)}$(mk_nat uid)
  | term_of_neuron _ _  (Out uid) = @{const \<open>NN_Digraph.neuron.Out\<close>(\<open>real\<close>,\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>)}$(mk_nat uid)
  | term_of_neuron verbose Single (Neuron {phi:TensorFlow_Type.activationT, bias:IEEEReal.decimal_approx, uid:int})
                          = (@{const \<open>NN_Digraph.neuron.Neuron\<close>(\<open>real\<close>,\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>)} $
                             (@{const \<open>NN_Digraph.Neuron.Neuron_ext\<close>(\<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>,\<open>real\<close>,\<open>unit\<close>)} $
                              (term_of_activation_single phi) $ (mk_real verbose (Real.toDecimal 1.0)) 
                                 $ (mk_real verbose bias)$ (mk_nat uid)  $ @{Const \<open>Unity\<close>}))
  | term_of_neuron verbose _ (Neuron {phi:TensorFlow_Type.activationT, bias:IEEEReal.decimal_approx, uid:int})
                          = (@{const \<open>NN_Digraph.neuron.Neuron\<close>(real,\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>)} $
                             (@{const \<open>NN_Digraph.Neuron.Neuron_ext\<close>(\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>,\<open>real\<close>,\<open>unit\<close>)} $
                              (term_of_activation_multi phi) $ (mk_real verbose (Real.toDecimal 1.0)) 
                                 $ (mk_real verbose bias)$ (mk_nat uid)  $ @{Const \<open>Unity\<close>}))
end

