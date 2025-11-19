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

subsection\<open>Neural Networks as List of Layers using Matrix Types (\thy)\<close>

theory
  Compass_Layers_Matrix
  imports
  Neural_Networks.NN_Layers_Matrix_Main
  Jordan_Normal_Form.Matrix_Impl
  Prediction_Utils_Matrix
begin 

subsubsection\<open>Infrastructure\<close>

definition 
\<open>checkget_result_matrix \<epsilon> prediction input expectations = checkget_result_list \<epsilon> (map_option list_of_vec (prediction (Some (vec_of_list (input))))) (Some (expectations))\<close>

definition predict_def[simp]: \<open>predict N x = (map_option list_of_vec (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N (vec_of_list x)))\<close>

subsubsection\<open>Manual Definition\<close>


paragraph\<open>Definition: Activation Tab\<close>

fun m_\<phi>_compass where
   \<open>m_\<phi>_compass mIdentity       = Some (map_vec identity)\<close>                 
 | \<open>m_\<phi>_compass _               = None\<close>

paragraph\<open>Definition: Layers\<close>

definition "m_dense_input = In \<lparr>name = STR ''dense_input'', units = 9\<rparr>"
definition "m_dense =
  Dense
   \<lparr>name = STR ''dense'', units = 3, \<phi> = mIdentity,
      \<beta> = vec_of_list [9153944253921509 / 100000000000000000, - 959978699684143 / 10000000000000000, 7840137928724289 / 100000000000000000],
      \<omega> = mat_of_cols_list 9
            [[- 28655481338500977 / 100000000000000000, 1398887038230896 / 1000000000000000, - 4396021068096161 / 10000000000000000,
             - 3206970691680908 / 10000000000000000, - 25562143325805664 / 100000000000000000, 11852015256881714 / 10000000000000000,
             6039865016937256 / 10000000000000000, - 16825008392333984 / 10000000000000000, - 413370318710804 / 10000000000000000],
            [24456006288528442 / 100000000000000000, - 11522198915481567 / 10000000000000000, 4993317425251007 / 10000000000000000,
             - 17345187664031982 / 10000000000000000, 48335906863212585 / 100000000000000000, 1511125922203064 / 1000000000000000,
             - 36204618215560913 / 100000000000000000, 9508050084114075 / 10000000000000000, - 3617756962776184 / 10000000000000000],
            [704086497426033 / 10000000000000000, - 51195383071899414 / 1000000000000000000, - 34204763174057007 / 100000000000000000,
             - 72454833984375 / 100000000000000, - 33541640639305115 / 100000000000000000, 12738076448440552 / 10000000000000000,
             7601173520088196 / 10000000000000000, - 2638514041900635 / 10000000000000000, - 5478811264038086 / 10000000000000000]]\<rparr>"
definition "m_dense_2 =
  Dense
   \<lparr>name = STR ''dense_2'', units = 4, \<phi> = mIdentity,
      \<beta> = vec_of_list [39810407906770706 / 1000000000000000000, 874686986207962 / 10000000000000000, - 4944610595703125 / 100000000000000000,
           - 5116363242268562 / 100000000000000000],
      \<omega> =  mat_of_cols_list 3
            [[(9063153862953186 / 10000000000000000::real), - 142851984500885 / 100000000000000, - 10823805332183838 / 10000000000000000],
            [17654908895492554 / 10000000000000000, 1934271901845932 / 10000000000000000, 1214023232460022 / 1000000000000000],
            [- 17099318504333496 / 10000000000000000, - 7595149427652359 / 100000000000000000, - 12841564416885376 / 10000000000000000],
            [- 615866482257843 / 1000000000000000, 1532884955406189 / 1000000000000000, 17860114574432373 / 100000000000000000]]\<rparr>"
definition "m_OUTPUT \<equiv> Out \<lparr>name = STR ''OUTPUT'', units = 4\<rparr>"

lemmas 
  m_layer_defs = m_dense_input_def m_dense_def m_dense_2_def m_OUTPUT_def

definition
  \<open>m_Layers =  [m_dense_input, m_dense, m_dense_2, m_OUTPUT]\<close>


paragraph\<open>Definition: Neural Network\<close>

definition
  \<open>m_NeuralNet = \<lparr> layers = m_Layers, activation_tab = m_\<phi>_compass\<rparr>\<close>

paragraph \<open>Locale Interpretations\<close>

lemma m_\<phi>_ran: \<open>ran m_\<phi>_compass = {map_vec identity}\<close>
  apply(auto simp add: ran_def ranI)[1]
    apply(elim m_\<phi>_compass.elims)
  apply((auto simp add: ran_def ranI)[1])+
  apply(meson bot.extremum insert_subsetI ranI m_\<phi>_compass.simps)+
  done

interpretation nn\<^sub>n\<^sub>o\<^sub>r: neural_network_sequential_layers\<^sub>m m_NeuralNet
  apply(simp add:neural_network_sequential_layers\<^sub>m_def)
  apply(safe)
  subgoal by(simp add: m_layer_defs m_NeuralNet_def m_Layers_def)
  subgoal by(simp add: m_layer_defs m_NeuralNet_def m_Layers_def)
  subgoal by(simp add: m_layer_defs m_NeuralNet_def m_Layers_def)
  subgoal by(simp add: m_\<phi>_ran valid_activation_tab\<^sub>m_def m_NeuralNet_def)
  subgoal by(normalization)
  done 

subsubsection\<open>TensorFlow Import\<close>
declare[[nn_proof_mode = eval]]
import_TensorFlow compass file "model/model.json" as seq_layer_matrix
declare[[nn_proof_mode = nbe]]

find_theorems name:"compass." name:\<phi> name:ran


thm compass.Layers.dense_input_def
thm compass.Layers.dense_def
thm compass.Layers.OUTPUT_def
thm compass.layer_defs
thm compass.Layers_def
thm compass.\<phi>_compass.simps
thm compass.NeuralNet_def
thm compass.neural_network_sequential_layers\<^sub>m_axioms

import_data_file "model/input.txt" defining input                             
import_data_file "model/predictions.txt" defining predictions 

thm input_def
thm predictions_def

value \<open>(predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m compass.NeuralNet) (vec_of_list(input!0))\<close>

value  \<open>checkget_result_matrix 0.001 (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m NeuralNet o the) (input!0) (predictions!0)\<close>
value  \<open>checkget_result_matrix 0.001 (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m NeuralNet o the) (input!1) (predictions!1)\<close>
value  \<open>checkget_result_matrix 0.001 (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m NeuralNet o the) (input!2) (predictions!2)\<close>
value  \<open>checkget_result_matrix 0.001 (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m NeuralNet o the) (input!3) (predictions!3)\<close>


text \<open>We convince ourselves that our Isabelle representation complies with the TensorFlow network
by generating the same prediction, within 0.001 (accounted for as Isabelle uses perfect mathematical 
reals whereas TensorFlow uses 32-bit floating point numbers)\<close>

lemma compass_predictions:
  \<open>(map_option list_of_vec (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m NeuralNet ((vec_of_list (input!0))))) \<approx>[0.001]\<approx>\<^sub>l (Some (predictions!0))\<close>
  \<open>(map_option list_of_vec (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m NeuralNet ((vec_of_list (input!1))))) \<approx>[0.001]\<approx>\<^sub>l (Some (predictions!1))\<close>
  \<open>(map_option list_of_vec (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m NeuralNet ((vec_of_list (input!2))))) \<approx>[0.001]\<approx>\<^sub>l (Some (predictions!2))\<close>
  \<open>(map_option list_of_vec (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m NeuralNet ((vec_of_list (input!3))))) \<approx>[0.001]\<approx>\<^sub>l (Some (predictions!3))\<close>
  by eval+

lemma \<open>0.000001 \<Turnstile>\<^sub>l {input} (predict NeuralNet) {predictions}\<close> 
  by eval

lemma activation[simp]: \<open>activation_tab NeuralNet = compass.\<phi>_compass \<close>
  by(simp add:  compass.Layers_def compass.layer_defs compass.NeuralNet_def)

lemma layers[simp]: \<open>layers NeuralNet = [dense_input, Layers.dense, dense_2, OUTPUT] \<close>
  by(simp add:  compass.Layers_def compass.NeuralNet_def)

lemma input[simp]: \<open>in_deg_NN NeuralNet = 9 \<close>
  by(simp add:  compass.Layers_def compass.NeuralNet_def in_deg_NN_def dense_input_def)


import_data_file "model/compass.txt" defining compass  

lemma c0[simp]: "compass!0 = [1,1,1,
                              1,1,0,
                              1,0,1]"
  by (simp add: compass_def)

lemma c1[simp]: "compass!1 = [1,1,1,
                              0,1,1,
                              1,0,1]"
  by (simp add: compass_def)

lemma c2[simp]: "compass!2 = [1,0,1,
                              0,1,1,
                              1,1,1]"
  by (simp add: compass_def)

lemma c3[simp]: "compass!3 = [1,0,1,
                              1,1,0,
                              1,1,1]"
  by (simp add: compass_def)


lemma compass_img_defined: \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m compass.NeuralNet xs) \<noteq> None) = (length (list_of_vec xs) = 9)\<close>
  using compass.neural_network_sequential_layers\<^sub>m_axioms 
        neural_network_sequential_layers\<^sub>m.img_None[of compass.NeuralNet] 
  by simp 

definition classify_as :: \<open>real Matrix.vec \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>classify_as xs n = (Option.bind (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m compass.NeuralNet xs) pos_of_max = Some n)\<close>

lemma classify_NW: \<open>classify_as (vec_of_list(compass!0)) 0\<close>
  by eval
lemma classify_NE: \<open>classify_as (vec_of_list(compass!1)) 1\<close>
  by eval
lemma classify_SE: \<open>classify_as (vec_of_list(compass!2)) 2\<close>
  by eval
lemma classify_SW: \<open>classify_as (vec_of_list(compass!3)) 3\<close>
  by eval

end