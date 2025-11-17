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

subsection\<open>Layer-based Modelling using List Types (\thy)\<close>

theory
  Grid_Layers_Matrix
  imports
  Grid_Layers
  NN_Layers_Matrix_Main
  Jordan_Normal_Form.Matrix_Impl (* improves performance of methods relying on code generation, e.g., normalization *)
begin

declare[[nn_proof_mode = "eval"]]
import_TensorFlow grid file "model/trained-model_binary-step_linear/model.json"
  as seq_layer_matrix
declare[[nn_proof_mode = "nbe"]]

text \<open>
Our new Isabelle/Isar command @{term "import_TensorFlow"} encodes the neural network model stored in 
the file model.json as sequence of layers, i.e., the formal encoding we developed. Our datatype 
package also proves that the imported model complies with the requirements of our formal model as 
well as proves various auxiliary properties (e.g., conversion between different representations)
that can be useful during interactive verification.\<close>

import_data_file "model/trained-model_binary-step_linear/input_small.txt"
  defining inputs_small
import_data_file "model/trained-model_binary-step_linear/expectations_small.txt" 
  defining expectations_small

import_data_file "model/trained-model_binary-step_linear/input.txt"        
  defining inputs
import_data_file "model/trained-model_binary-step_linear/expectations.txt" 
  defining expectations
import_data_file "model/trained-model_binary-step_linear/predictions.txt" 
  defining predictions

text \<open>To ensure that our formalisation is a faithful representation of the neural 
networks that we defined in TensorFlow, we provide a framework that supports 
the import of trained TensorFlow networks and their test data. We can then 
use this to evaluate our Isabelle network and validate that the output is the 
same, hence providing confidence that our formalisation is accurate.

We can import text files containing NumPy arrays of our test inputs, 
expectations and predictions from our trained TensorFlow network.\<close>


thm grid.Layers_def
thm grid.Layers.dense_input_def
thm grid.Layers.OUTPUT_def
thm grid.layer_defs
thm grid.Layers_def
thm grid.\<phi>_grid.simps
thm grid.NeuralNet_def
thm inputs_def
thm predictions_def

lemmas grid_defs = grid.Layers_def grid.layer_defs grid.NeuralNet_def
lemmas activation_defs = identity_def binary_step_def


subsubsection \<open>Proving using the matrix prediction function.\<close>

lemma grid_closed_mat [simp]: 
      \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list xs) = (case xs of  
      [x3, x2, x1, x0] \<Rightarrow> let y = 2 * (x3 + (x2 * 2 + (x1 * 4 + x0 * 8))) 
       in Some (
         vec_of_list[(if y - 7 \<le> 0 then 0 else 1) +
            ((if y - 11 \<le> 0 then 0 else 1) + ((if y - 21 \<le> 0 then 0 else 1) 
               + ((if y - 25 \<le> 0 then 0 else 1) - (if y - 23 \<le> 0 then 0 else 1)) 
                 - (if y - 19 \<le> 0 then 0 else 1)) - (if y - 9 \<le> 0 then 0 else 1)) 
                    - (if y - 5 \<le> 0 then 0 else 1) + 1,
          (if y - 5 \<le> 0 then 0 else 1) + ((if y - 23 \<le> 0 then 0 else 1) 
              - (if y - 25 \<le> 0 then 0 else 1) - (if y - 7 \<le> 0 then 0 else 1)),
          (if y - 9 \<le> 0 then 0 else 1) + ((if y - 19 \<le> 0 then 0 else 1) 
              - (if y - 21 \<le> 0 then 0 else 1) - (if y - 11 \<le> 0 then 0 else 1))]
       )
       | _ \<Rightarrow> None)\<close>
  apply (auto simp add: predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def grid_defs activation_defs split:list.split)[1]
  apply(normalization)
  by (simp_all add: grid_defs predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def activation_defs dom_def dim_col_mat_of_col_list dim_row_mat_of_col_list)

lemma grid_img_defined_mat: \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list xs)) \<noteq> None) = (dim_vec (vec_of_list xs) = 4)\<close>
  by(auto simp add:Let_def split:list.split)

lemma grid_img_defined_mat': \<open>(\<exists> y. (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list xs)) = Some (vec_of_list y)) = (dim_vec (vec_of_list xs) = 4)\<close>
proof(cases "(dim_vec (vec_of_list xs)) = 4")
  case True
  then show ?thesis
    by (metis grid_img_defined_mat option.exhaust vec_list) 
next
  case False
  then show ?thesis 
    using grid_img_defined_mat by blast
qed
   
lemma grid_image_mat:
  assumes \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list xs) = Some y\<close>
  shows \<open>y \<in> { vec_of_list [0, 0, 1], vec_of_list [0, 1, 0], vec_of_list [1, 0, 0]}\<close>
  using assms grid_img_defined_mat 
  apply(simp split:list.splits)
  unfolding Let_def vec_of_list_def vCons_def
  apply(simp)
  by auto

lemma ran_aux:          
  assumes \<open>\<forall> x . f x \<noteq> None \<longrightarrow> the (f x) \<in> Y\<close>
  shows \<open>ran (f) \<subseteq> Y\<close>
  unfolding ran_def using assms   
  by force

lemma grid_image_approx_mat:
 \<open>ran (\<lambda> x . predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list x)) 
              \<subseteq> {vec_of_list [0, 0, 1], vec_of_list [0, 1, 0], vec_of_list [1, 0, 0]}\<close>
  using grid_image_mat ran_aux
  by (metis (no_types, lifting) option.exhaust_sel)
  

text \<open>The lemma @{term "grid_image_approx"} shows that the output of the classification
is never ambiguous (i.e., two or more classification output having the value 1). \<close>

lemma grid_dom_mat: \<open>dom ( \<lambda> x . predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet  (vec_of_list x)) = {a. length a = 4}\<close>
  by (simp add: grid_defs predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def activation_defs dom_def dim_col_mat_of_col_list dim_row_mat_of_col_list)

definition "range_of x = (if x = (0::real) then {0..0.04::real} else {0.96..1})"

lemma \<open>x3 \<in> {0.96..1.00} \<and> x2 \<in> {0.96..1.00} 
     \<and> x1 \<in> {0.00..0.04} \<and> x0 \<in> {0.00..0.04} \<Longrightarrow>  predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list [x3, x2, x1, x0]) = Some(vec_of_list [0, 1, 0])\<close>
    by(simp add: Let_def, normalization, argo)
lemma \<open>x3 \<in> {0.00..0.04} \<and> x2 \<in> {0.00..0.04}
     \<and> x1 \<in> {0.96..1.00} \<and> x0 \<in> {0.96..1.00} \<Longrightarrow> predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list [x3, x2, x1, x0]) = Some(vec_of_list [0, 1, 0])\<close>
    by(simp add: Let_def, normalization, argo)
lemma \<open>x3 \<in> {0.95..1.00} \<and> x2 \<in> {0.00..0.05} 
     \<and> x1 \<in> {0.95..1.00} \<and> x0 \<in> {0.00..0.05} \<Longrightarrow>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list [x3, x2, x1, x0]) = Some(vec_of_list [0, 0, 1])\<close>
  by(simp add: Let_def, normalization, argo)
lemma \<open>x3 \<in> {0.00..0.1} \<and> x2 \<in> {0.96..1.00} 
     \<and> x1 \<in> {0.00..0.1} \<and> x0 \<in> {0.96..1.00} \<Longrightarrow>  predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet (vec_of_list [x3, x2, x1, x0]) = Some(vec_of_list [0, 0, 1])\<close>
   by(simp add: Let_def, normalization, argo)

text \<open>A common definition of safety in neural networks is the requirement that small changes to an 
input should not change the classification. For this grid example, we express such a verification 
goal as shown above, where we set a small bound of noise on the input, and verify that the output 
classification remains constant.\<close>

subsubsection \<open>Proving using the list to matrix prediction\<close>

text \<open>The following proofs on the grid example use our wrapper function that converts lists to 
vectors, uses the matrix based prediction function and converts the output back into a list\<close>

lemma grid_closed' [simp]: 
      \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet xs = (case xs of  
      [x3, x2, x1, x0] \<Rightarrow> let y = 2 * (x3 + (x2 * 2 + (x1 * 4 + x0 * 8))) 
       in Some (
         [(if y - 7 \<le> 0 then 0 else 1) +
            ((if y - 11 \<le> 0 then 0 else 1) + ((if y - 21 \<le> 0 then 0 else 1) 
               + ((if y - 25 \<le> 0 then 0 else 1) - (if y - 23 \<le> 0 then 0 else 1)) 
                 - (if y - 19 \<le> 0 then 0 else 1)) - (if y - 9 \<le> 0 then 0 else 1)) 
                    - (if y - 5 \<le> 0 then 0 else 1) + 1,
          (if y - 5 \<le> 0 then 0 else 1) + ((if y - 23 \<le> 0 then 0 else 1) 
              - (if y - 25 \<le> 0 then 0 else 1) - (if y - 7 \<le> 0 then 0 else 1)),
          (if y - 9 \<le> 0 then 0 else 1) + ((if y - 19 \<le> 0 then 0 else 1) 
              - (if y - 21 \<le> 0 then 0 else 1) - (if y - 11 \<le> 0 then 0 else 1))]
       )
       | _ \<Rightarrow> None)\<close>
   apply (auto simp add: predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def grid_defs activation_defs split:list.split)[1]
       apply (normalization)
       apply(simp add:dim_col_mat_of_col_list dim_row_mat_of_col_list)+
done

lemma grid_img_defined': \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet xs) \<noteq> None) = (length xs = 4)\<close>
  by(auto simp add:Let_def split:list.split)

lemma grid_img_defined: \<open>(\<exists> y. (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet xs) = Some y) = (length xs = 4)\<close>
  using grid_img_defined' by auto 

lemma grid_image:
  assumes \<open>(predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet xs) \<noteq> None\<close>
  shows \<open>the (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet xs) \<in> { [0, 0, 1], 
                                                    [0, 1, 0],
                                                    [1, 0, 0]}\<close>
  using assms grid_img_defined' apply simp 
  by(auto simp add:Let_def split:list.split) 

lemma grid_image_approx:
 \<open>ran (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet) \<subseteq> {[0, 0, 1], [0, 1, 0], [1, 0, 0]}\<close>
  apply(simp only:ran_def) 
  using grid_image by force

text \<open>The lemma @{term "grid_image_approx"} shows that the output of the classification
is never ambiguous (i.e., two or more classification output having the value 1).\<close>

lemma grid_dom': \<open>dom (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet) = {a. length a = 4} \<close>
  unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'_def   predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def
  by (smt (verit, best) Collect_cong dom_def grid_img_defined' predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def) 

lemma grid_dom_mat': \<open>dom ( \<lambda> x . predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m grid.NeuralNet  (vec_of_list x)) = {a. length a = 4}\<close>
  by (simp add: grid_defs predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def activation_defs dom_def dim_col_mat_of_col_list dim_row_mat_of_col_list)


lemma \<open>x3 \<in> {0.96..1.00} \<and> x2 \<in> {0.96..1.00} 
     \<and> x1 \<in> {0.00..0.04} \<and> x0 \<in> {0.00..0.04} \<Longrightarrow>  predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet [x3, x2, x1, x0] = Some [0, 1, 0]\<close>
  by(simp add: Let_def)
lemma \<open>x3 \<in> {0.00..0.04} \<and> x2 \<in> {0.00..0.04} 
     \<and> x1 \<in> {0.96..1.00} \<and> x0 \<in> {0.96..1.00} \<Longrightarrow>  predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet [x3, x2, x1, x0] = Some [0, 1, 0]\<close>
  by(simp add: Let_def)
lemma \<open>x3 \<in> {0.95..1.00} \<and> x2 \<in> {0.00..0.05} 
     \<and> x1 \<in> {0.95..1.00} \<and> x0 \<in> {0.00..0.05} \<Longrightarrow>  predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet [x3, x2, x1, x0] = Some [0, 0, 1]\<close>
  by(simp add: Let_def)
lemma \<open>x3 \<in> {0.00..0.1} \<and> x2 \<in> {0.96..1.00} 
     \<and> x1 \<in> {0.00..0.1} \<and> x0 \<in> {0.96..1.00} \<Longrightarrow>  predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet [x3, x2, x1, x0] = Some [0, 0, 1]\<close>
  by(simp add: Let_def)

text \<open>A common definition of safety in neural networks is the requirement that small changes to an 
input should not change the classification. For this grid example, we express such a verification 
goal as shown above, where we set a small bound of noise on the input, and verify that the output 
classification remains constant.\<close>

lemma grid_meets_predictions: 
      \<open>\<Turnstile>\<^sub>i\<^sub>l {inputs} (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet) {intervals_of_l 0.000001 predictions}\<close>
  by(simp add: ensure_testdata_interval_list_def upper_Interval lower_Interval predictions_def 
               intervals_of_l_def inputs_def in_set_interval) 
 
lemma grid_meets_expectations_max_classifier:
      \<open>\<Turnstile>\<^sub>l {inputs_small} (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet) {expectations_small}\<close>
  by (simp add: ensure_testdata_max_list_def expectations_small_def inputs_small_def)

lemma grid_min_delta_classifier: 
      \<open>1.0 \<Turnstile> predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' grid.NeuralNet\<close> 
  unfolding ensure_delta_min_def Prediction_Utils.\<delta>\<^sub>m\<^sub>i\<^sub>n_def max\<^sub>l\<^sub>i\<^sub>s\<^sub>t_def
  using grid_image_approx
  by auto

text \<open>The lemmas @{thm [source] "grid_meets_predictions"},  @{thm [source] "grid_meets_expectations_max_classifier"}
and @{thm [source] "grid_min_delta_classifier"} show that our definition of the grid neural network computes 
the same prediction as the TensorFlow trained network. \<close>

end
