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

subsection\<open>Neural Networks as Directed Graphs (\thy)\<close>

theory
  Compass_Digraph 
  imports 
  Neural_Networks.NN_Digraph_Main 
begin

subsubsection\<open>Manual Encoding\<close>

paragraph\<open>Definition: Neurons\<close>

definition "m_N0 \<equiv> In 0"
definition "m_N1 \<equiv> In 1"
definition "m_N2 \<equiv> In 2"
definition "m_N3 \<equiv> In 3"
definition "m_N4 \<equiv> In 4"
definition "m_N5 \<equiv> In 5"
definition "m_N6 \<equiv> In 6"
definition "m_N7 \<equiv> In 7"
definition "m_N8 \<equiv> In 8"
definition "m_N9 \<equiv> Neuron \<lparr>\<phi> = Identity, \<alpha> = 1, \<beta> = 7082077208906412 / 1000000000000000000, uid = 9\<rparr>"
definition "m_N10 \<equiv> Neuron \<lparr>\<phi> = Identity, \<alpha> = 1, \<beta> = 10754479467868805 / 100000000000000000, uid = 10\<rparr>"
definition "m_N11 \<equiv> Neuron \<lparr>\<phi> = Identity, \<alpha> = 1, \<beta> = - 15743795782327652 / 1000000000000000000, uid = 11\<rparr>"
definition "m_N12 \<equiv> Neuron \<lparr>\<phi> = Identity, \<alpha> = 1, \<beta> = 4792080223560333 / 10000000000000000, uid = 12\<rparr>"
definition "m_N13 \<equiv> Neuron \<lparr>\<phi> = Identity, \<alpha> = 1, \<beta> =  - 16364477574825287 / 100000000000000000, uid = 13\<rparr>"
definition "m_N14 \<equiv> Neuron \<lparr>\<phi> = Identity, \<alpha> = 1, \<beta> = - 24132762849330902 / 100000000000000000, uid = 14\<rparr>"
definition "m_N15 \<equiv> Neuron \<lparr>\<phi> = Identity, \<alpha> = 1, \<beta> = - 3057991564273834 / 10000000000000000, uid = 15\<rparr>"
definition "m_N16 \<equiv> Out 16"
definition "m_N17 \<equiv> Out 17"
definition "m_N18 \<equiv> Out 18"
definition "m_N19 \<equiv> Out 19"

lemmas
  m_neuron_defs = m_N0_def m_N1_def m_N2_def m_N3_def m_N4_def m_N5_def m_N6_def m_N7_def m_N8_def 
                  m_N9_def m_N10_def m_N11_def m_N12_def m_N13_def m_N14_def m_N15_def m_N16_def 
                  m_N17_def m_N18_def m_N19_def

definition "m_Neurons = [m_N0, m_N1, m_N2, m_N3, m_N4, m_N5, m_N6, m_N7, m_N8, m_N9, m_N10, m_N11, 
                         m_N12, m_N13, m_N14, m_N15, m_N16, m_N17, m_N18, m_N19]"

paragraph\<open>Definition: Edges\<close>

definition "m_E12_16 \<equiv> \<lparr>\<omega> = 1, tl = m_N12, hd = m_N16\<rparr>"
definition "m_E13_17 \<equiv> \<lparr>\<omega> = 1, tl = m_N13, hd = m_N17\<rparr>"
definition "m_E14_18 \<equiv> \<lparr>\<omega> = 1, tl = m_N14, hd = m_N18\<rparr>"
definition "m_E15_19 \<equiv> \<lparr>\<omega> = 1, tl = m_N15, hd = m_N19\<rparr>"
definition "m_E9_12 \<equiv> \<lparr>\<omega> = 4108836501836777 / 100000000000000000, tl = m_N9, hd = m_N12\<rparr>"
definition "m_E10_12 \<equiv> \<lparr>\<omega> = 14860405027866364 / 100000000000000000, tl = m_N10, hd = m_N12\<rparr>"
definition "m_E11_12 \<equiv> \<lparr>\<omega> = 24455930292606354 / 100000000000000000, tl = m_N11, hd = m_N12\<rparr>"
definition "m_E9_13 \<equiv> \<lparr>\<omega> = - 2398796558380127 / 1000000000000000, tl = m_N9, hd = m_N13\<rparr>"
definition "m_E10_13 \<equiv> \<lparr>\<omega> = - 7789374142885208 / 100000000000000000, tl = m_N10, hd = m_N13\<rparr>"
definition "m_E11_13 \<equiv> \<lparr>\<omega> = 5169432163238525 / 10000000000000000, tl = m_N11, hd = m_N13\<rparr>"
definition "m_E9_14 \<equiv> \<lparr>\<omega> = - 46464818716049194 / 100000000000000000, tl = m_N9, hd = m_N14\<rparr>"
definition "m_E10_14 \<equiv> \<lparr>\<omega> = 10928256511688232 / 10000000000000000, tl = m_N10, hd = m_N14\<rparr>"
definition "m_E11_14 \<equiv> \<lparr>\<omega> = - 14084954261779785 / 10000000000000000, tl = m_N11, hd = m_N14\<rparr>"
definition "m_E9_15 \<equiv> \<lparr>\<omega> = 1946548342704773 / 1000000000000000, tl = m_N9, hd = m_N15\<rparr>"
definition "m_E10_15 \<equiv> \<lparr>\<omega> = - 952406108379364 / 1000000000000000, tl = m_N10, hd = m_N15\<rparr>"
definition "m_E11_15 \<equiv> \<lparr>\<omega> = - 6348744630813599 / 10000000000000000, tl = m_N11, hd = m_N15\<rparr>"
definition "m_E0_9 \<equiv> \<lparr>\<omega> =  6684625744819641 / 10000000000000000, tl = m_N0, hd = m_N9\<rparr>"
definition "m_E1_9 \<equiv> \<lparr>\<omega> = - 1295279860496521 / 1000000000000000, tl = m_N1, hd = m_N9\<rparr>"
definition "m_E2_9 \<equiv> \<lparr>\<omega> = - 28579580783843994 / 100000000000000000, tl = m_N2, hd = m_N9\<rparr>"
definition "m_E3_9 \<equiv> \<lparr>\<omega> = 17300206422805786 / 10000000000000000, tl = m_N3, hd = m_N9\<rparr>"
definition "m_E4_9 \<equiv> \<lparr>\<omega> =  6391876339912415 / 10000000000000000, tl = m_N4, hd = m_N9\<rparr>"
definition "m_E5_9 \<equiv> \<lparr>\<omega> = - 13919317722320557 / 10000000000000000, tl = m_N5, hd = m_N9\<rparr>"
definition "m_E6_9 \<equiv> \<lparr>\<omega> = - 45270395278930664 / 100000000000000000, tl = m_N6, hd = m_N9\<rparr>"
definition "m_E7_9 \<equiv> \<lparr>\<omega> = 13654941320419312 / 10000000000000000, tl = m_N7, hd = m_N9\<rparr>"
definition "m_E8_9 \<equiv> \<lparr>\<omega> = - 18450486660003662 / 100000000000000000, tl = m_N8, hd = m_N9\<rparr>"
definition "m_E0_10 \<equiv> \<lparr>\<omega> = 6286060065031052 / 100000000000000000, tl = m_N0, hd = m_N10\<rparr>"
definition "m_E1_10 \<equiv> \<lparr>\<omega> = 3662835955619812 / 10000000000000000, tl = m_N1, hd = m_N10\<rparr>"
definition "m_E2_10 \<equiv> \<lparr>\<omega> = 6922798752784729 / 10000000000000000, tl = m_N2, hd = m_N10\<rparr>"
definition "m_E3_10 \<equiv> \<lparr>\<omega> = - 3759842813014984 / 10000000000000000, tl = m_N3, hd = m_N10\<rparr>"
definition "m_E4_10 \<equiv> \<lparr>\<omega> = 1505584865808487 / 10000000000000000, tl = m_N4, hd = m_N10\<rparr>"
definition "m_E5_10 \<equiv> \<lparr>\<omega> = 10981513261795044 / 10000000000000000, tl = m_N5, hd = m_N10\<rparr>"
definition "m_E6_10 \<equiv> \<lparr>\<omega> = 17104554921388626 / 1000000000000000000, tl = m_N6, hd = m_N10\<rparr>"
definition "m_E7_10 \<equiv> \<lparr>\<omega> = 7420693039894104 / 10000000000000000, tl = m_N7, hd = m_N10\<rparr>"
definition "m_E8_10 \<equiv> \<lparr>\<omega> = 1954902894794941 / 12500000000000000, tl = m_N8, hd = m_N10\<rparr>"
definition "m_E0_11 \<equiv> \<lparr>\<omega> = 986328125 / 10000000000, tl = m_N0, hd = m_N11\<rparr>"
definition "m_E1_11 \<equiv> \<lparr>\<omega> = 9530481100082397 / 10000000000000000, tl = m_N1, hd = m_N11\<rparr>"
definition "m_E2_11 \<equiv> \<lparr>\<omega> = 35006752610206604 / 100000000000000000, tl = m_N2, hd = m_N11\<rparr>"
definition "m_E3_11 \<equiv> \<lparr>\<omega> = 7897922992706299 / 10000000000000000, tl = m_N3, hd = m_N11\<rparr>"
definition "m_E4_11 \<equiv> \<lparr>\<omega> = - 5813585519790649 / 10000000000000000, tl = m_N4, hd = m_N11\<rparr>"
definition "m_E5_11 \<equiv> \<lparr>\<omega> = 5679721832275391 / 10000000000000000, tl = m_N5, hd = m_N11\<rparr>"
definition "m_E6_11 \<equiv> \<lparr>\<omega> = 5311743021011353 / 10000000000000000, tl = m_N6, hd = m_N11\<rparr>"
definition "m_E7_11 \<equiv> \<lparr>\<omega> = - 9090567231178284 / 10000000000000000, tl = m_N7, hd = m_N11\<rparr>"
definition "m_E8_11 \<equiv> \<lparr>\<omega> = - 45479249954223633 / 100000000000000000, tl = m_N8, hd = m_N11\<rparr>"

lemmas
m_edge_defs = m_E12_16_def m_E13_17_def m_E14_18_def m_E15_19_def m_E9_12_def m_E10_12_def 
              m_E11_12_def m_E9_13_def m_E10_13_def m_E11_13_def m_E9_14_def m_E10_14_def 
              m_E11_14_def m_E9_15_def m_E10_15_def m_E11_15_def m_E0_9_def m_E1_9_def m_E2_9_def
              m_E3_9_def m_E4_9_def m_E5_9_def m_E6_9_def m_E7_9_def m_E8_9_def m_E0_10_def 
              m_E1_10_def m_E2_10_def m_E3_10_def m_E4_10_def m_E5_10_def m_E6_10_def m_E7_10_def
              m_E8_10_def m_E0_11_def m_E1_11_def m_E2_11_def m_E3_11_def m_E4_11_def m_E5_11_def 
              m_E6_11_def m_E7_11_def m_E8_11_def

definition
  \<open>m_Edges = [m_E12_16, m_E13_17, m_E14_18, m_E15_19, m_E9_12, m_E10_12, m_E11_12, m_E9_13, m_E10_13, 
              m_E11_13, m_E9_14, m_E10_14, m_E11_14, m_E9_15, m_E10_15, m_E11_15, m_E0_9, m_E1_9, 
              m_E2_9, m_E3_9, m_E4_9, m_E5_9, m_E6_9, m_E7_9, m_E8_9, m_E0_10, m_E1_10, m_E2_10, 
              m_E3_10, m_E4_10, m_E5_10, m_E6_10, m_E7_10, m_E8_10, m_E0_11, m_E1_11, m_E2_11, 
              m_E3_11, m_E4_11, m_E5_11, m_E6_11, m_E7_11, m_E8_11]\<close>

definition 
  \<open>m_Graph \<equiv> mk_nn_pregraph m_Edges\<close>

paragraph\<open>Definition: Activation Tab\<close>

fun m_\<phi>_compass where 
  \<open>m_\<phi>_compass  Identity = Some identity\<close>
| \<open>m_\<phi>_compass _ = None\<close>

paragraph\<open>Definition: Neural Network\<close>

definition
  \<open>m_NeuralNet = \<lparr>graph = m_Graph, activation_tab = m_\<phi>_compass\<rparr>\<close>

paragraph \<open>Locale Interpretations\<close>

global_interpretation m_compass: nn_pregraph m_Graph
  apply(simp add: m_Graph_def)
  apply(simp add: nn_pregraph_mk nn_pregraph.axioms)
  done 
     

subsubsection \<open>Automated Encoding Using The TensorFlow Import\<close>

paragraph\<open>Single Encoding\<close>
declare [[nn_proof_mode = eval]]
import_TensorFlow compass file "model/model.json" as digraph_single
declare [[nn_proof_mode = nbe]]


thm compass.neuron_defs       
thm compass.Neurons_def
thm compass.edge_defs
thm compass.Edges_def
thm compass.Graph_def
thm compass.verts_set_conv
thm compass.edges_set_conv
thm compass.\<phi>_compass.simps
thm compass.NeuralNet_def
thm compass.nn_pregraph_axioms
thm compass.neural_network_digraph_single_axioms

text \<open>importing the data files\<close>

import_data_file "model/input.txt" defining input
import_data_file "model/predictions.txt" defining predictions

thm input_def
thm predictions_def

value \<open>(checkget_result_singleton 0.15 (predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet (map_of_list (input!0)) E12_16)) (Some (predictions!0!0))\<close>
value \<open>(checkget_result_singleton 0.15 (predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet (map_of_list (input!0)) E12_16)) (Some (predictions!1!0))\<close>
value \<open>(checkget_result_singleton 0.15 (predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet (map_of_list (input!0)) E12_16)) (Some (predictions!2!0))\<close>
value \<open>(checkget_result_singleton 0.15 (predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet (map_of_list (input!0)) E12_16)) (Some (predictions!3!0))\<close>

lemma compass_truth_table_predict:
  \<open>(predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet (map_of_list (input!0)) E12_16) \<approx>[0.0001]\<approx>\<^sub>s (Some (predictions!0!0))\<close>
  \<open>(predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet (map_of_list (input!1)) E12_16) \<approx>[0.0001]\<approx>\<^sub>s (Some (predictions!1!0))\<close>
  \<open>(predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet (map_of_list (input!2)) E12_16) \<approx>[0.0001]\<approx>\<^sub>s (Some (predictions!2!0))\<close>
  \<open>(predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet (map_of_list (input!3)) E12_16) \<approx>[0.0001]\<approx>\<^sub>s (Some (predictions!3!0))\<close>
  by(normalization)+

lemma compass_truth_table_predict':
  \<open>(predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e_\<^sub>l\<^sub>i\<^sub>s\<^sub>t compass.NeuralNet (input!0) \<approx>[0.0001]\<approx>\<^sub>l (Some (predictions!0)))\<close>
  \<open>(predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e_\<^sub>l\<^sub>i\<^sub>s\<^sub>t compass.NeuralNet (input!1) \<approx>[0.0001]\<approx>\<^sub>l (Some (predictions!1)))\<close>
  \<open>(predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e_\<^sub>l\<^sub>i\<^sub>s\<^sub>t compass.NeuralNet (input!2) \<approx>[0.0001]\<approx>\<^sub>l (Some (predictions!2)))\<close>
  \<open>(predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e_\<^sub>l\<^sub>i\<^sub>s\<^sub>t compass.NeuralNet (input!3) \<approx>[0.0001]\<approx>\<^sub>l (Some (predictions!3)))\<close>
  by(normalization)+

paragraph\<open>Multi Encoding\<close>

declare [[nn_proof_mode = eval]]
import_TensorFlow compass_multi file "model/model.json" as digraph
declare [[nn_proof_mode = nbe]]

thm compass_multi.neuron_defs
thm compass_multi.Neurons_def

thm compass_multi.edge_defs
thm compass_multi.Edges_def

thm compass_multi.Graph_def
thm compass_multi.verts_set_conv
thm compass_multi.edges_set_conv

thm compass_multi.\<phi>_compass_multi.simps

thm compass_multi.NeuralNet_def

thm compass_multi.nn_pregraph_axioms
thm compass_multi.neural_network_digraph_axioms

paragraph\<open>Checking Equivalence of Manual Definitions and Automated Import\<close>

lemma Neurons_equiv: "compass.Neurons = m_Neurons"
  by normalization
  
lemma Edges_equiv: "compass.Edges = m_Edges"
  by normalization
 
lemma Graph_equiv: "compass.Graph = m_Graph"
  unfolding compass.Graph_def m_Graph_def
  by (simp add: Edges_equiv)

lemma \<phi>_equiv: "compass.\<phi>_compass f = m_\<phi>_compass f"
  by(cases "f", simp_all)

lemma NeuralNet_equiv: "compass.NeuralNet = m_NeuralNet"
  unfolding compass.NeuralNet_def m_NeuralNet_def
  by(auto simp add: Graph_equiv \<phi>_equiv)

lemma \<open> predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e_\<^sub>l\<^sub>i\<^sub>s\<^sub>t compass.NeuralNet =  predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e_\<^sub>l\<^sub>i\<^sub>s\<^sub>t m_NeuralNet\<close>
  using NeuralNet_equiv by simp

paragraph\<open>Code Evaluation\<close>

definition "NW = [0::nat \<mapsto> 1, 1::nat \<mapsto> 1, 2::nat \<mapsto> 1,
                  3::nat \<mapsto> 1, 4::nat \<mapsto> 1, 5::nat \<mapsto> 0,
                  6::nat \<mapsto> 1, 7::nat \<mapsto> 0, 8::nat \<mapsto> 1]"

definition \<open>eval_compass = predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e compass.NeuralNet NW compass.Edges.E12_16\<close>

end

