(**********************************************************************************
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
 * SPDX-License-Identifier: BSD-3-Clause
 ***********************************************************************************)

chapter\<open>Activation Functions\<close>

theory Activation_Functions
imports
  "HOL-Analysis.Derivative"
  TensorFlow_Import
  NN_Common
  "Interval_Analysis.Affine_Functions"
  Jordan_Normal_Form.Matrix (* only needed for Matrix.vec type constructor in ML package *)
begin

text\<open>
  In this theory, we provide definitions for the most common activation functions. 
  Moreover, we also provide an ML-API for working with HOL-terms of activation functions.
\<close>

section\<open>Defining Activation Functions and Their Derivatives\<close>

text\<open>
  Many common activation functions use the function @{term "f(x) = e^x"} (written 
  @{term "f(x) = exp (x)"}. For those activation functions, we also define approximations
  using the Taylor series of the exponential function:
\<close>

definition
  \<open>exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n x = (\<Sum>i = 0..n . x^i / fact i)\<close>

lemma exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<^sub>2: "exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r 2 (x::real) = (1::real) + x + x^2/2"
  by(code_simp, simp)

subsection\<open>Activation Functions\<close>

definition 
  \<open>identity = (\<lambda>v. v)\<close>

lemma identity_linear[simp]: \<open>affine_fun identity\<close>
unfolding identity_def   by simp 
  
definition binary_step :: \<open>'a::{zero, ord, one, zero} \<Rightarrow> 'a\<close> where
 \<open>binary_step = (\<lambda> v. if v \<le> 0 then 0 else 1)\<close>

hide_const sign
definition
  \<open>sign = sgn\<close>

definition
  \<open>softsign = (\<lambda>v. v / (\<bar>v\<bar> + 1))\<close>
definition 
  \<open>logistic L k v\<^sub>0 = (\<lambda>v. L / (1 + exp(-k * (v -v\<^sub>0))))\<close>
definition 
  \<open>logistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n L k v\<^sub>0 = (\<lambda>v. L / (1 + (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n (-k * (v -v\<^sub>0)))))\<close>


definition sigmoid :: "real \<Rightarrow> real" where
 \<open>sigmoid = (\<lambda>v. 1 / (1 + exp(-v)))\<close>

definition
  \<open>sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n = (\<lambda>v. 1 / (1 + (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n (-v))))\<close>

lemma \<open>sigmoid = (logistic (1.0::real) 1.0 0)\<close>
  unfolding sigmoid_def logistic_def by auto 
lemma \<open>sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n = (logistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n (1.0::real) 1.0 0)\<close>
  unfolding sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def logistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def by auto 


definition 
  \<open>swish           = (\<lambda>v. v * (sigmoid v))\<close>
definition 
  \<open>swish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n    = (\<lambda>v. v * (sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n v))\<close>
definition 
  \<open>relu            = (\<lambda>v. max 0 v)\<close>

definition 
  \<open>generalized_relu \<alpha> m t = (\<lambda>v. case m of Some m' \<Rightarrow> min (if v \<le> t then \<alpha> * v else v) m' 
                                         | None \<Rightarrow> if v \<le> t then \<alpha> * v else v)\<close>

  
lemma \<open>relu = (generalized_relu (0.0::real) None (0.0))\<close>
  unfolding relu_def generalized_relu_def by auto 

definition 
  \<open>softplus = (\<lambda>v. ln (1 + exp v))\<close>

definition 
  \<open>elu \<alpha> = (\<lambda>v. if v \<le> 0 then \<alpha> * ((exp v)-1) else v)\<close> 
definition 
  \<open>elu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n \<alpha> = (\<lambda>v. if v \<le> 0 then \<alpha> * ((exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n v)-1) else v)\<close> 
definition 
  \<open>selu = (\<lambda>v. let \<alpha> = 1.67326324; 
                   scale = 1.05070098 
               in if v \<le> 0 then scale * \<alpha> * ((exp v)-1) else scale * v)\<close> 
definition 
  \<open>selu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n = (\<lambda>v. let \<alpha> = 1.67326324; 
                        scale = 1.05070098 
                      in if v \<le> 0 then scale * \<alpha> * ((exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n v)-1) else scale * v)\<close> 

definition
  \<open>prelu \<alpha>  = (\<lambda>v. if v < 0 then \<alpha> * v else v)\<close>
definition 
  \<open>silu = (\<lambda>v. v / (1 + (exp (-v))))\<close>
definition 
  \<open>silu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n = (\<lambda>v. v / (1 + (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n (-v))))\<close>
definition
  \<open>gaussian = (\<lambda>v. exp (- v\<^sup>2))\<close>
definition 
  \<open>gaussian\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n = (\<lambda>v. exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n (- v\<^sup>2))\<close>

definition 
  \<open>hard_sigmoid = (\<lambda>v. if v < -2.5 then 0 else if v > 2.5 then 1 else 0.2 * v + 0.5)\<close>
definition
  \<open>gelu_approx = (\<lambda>v. 0.5 * v * (1 + tanh(sqrt(2 / pi) * (v + 0.044715 * v * v * v))))\<close> 

text\<open>
  Note, the error function @{term "erf"} is available in the AFP entry~\<^cite>\<open>"eberl:erf:2018"\<close>, which can 
  be used for defining a non-approximated @{term "gelu"} activation function.
\<close>

definition softmax :: "('a::{banach,real_normed_algebra_1,inverse}) list \<Rightarrow> 'a list" where 
  \<open>softmax vs = map (\<lambda> v. exp v / (\<Sum>v'\<leftarrow>vs. exp v')) vs\<close> 

definition msoftmax :: "('a::{banach,real_normed_algebra_1,inverse}) vec \<Rightarrow> 'a vec" where 
  \<open>msoftmax vs = map_vec (\<lambda> v. exp v / (\<Sum>v'\<leftarrow> (list_of_vec vs). exp v')) vs\<close> 


definition softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r :: "nat \<Rightarrow> ('a::{banach,real_normed_algebra_1,inverse}) list \<Rightarrow> 'a list" where
  \<open>softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n vs = map (\<lambda> v. (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n v) / (\<Sum>v'\<leftarrow>vs. (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n v'))) vs\<close> 

definition msoftmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r :: "nat \<Rightarrow> ('a::{banach,real_normed_algebra_1,inverse}) vec \<Rightarrow> 'a vec" where
  \<open>msoftmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n vs = map_vec (\<lambda> v. (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n v) / (\<Sum>v'\<leftarrow> (list_of_vec vs). (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n v'))) vs\<close>


lemma softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<^sub>2: 
      "softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r 2 vs = map (\<lambda> (v::real). (1 + v + v\<^sup>2/2) / (foldl (+) 0 (map (\<lambda> v'. 1 + v' + v'\<^sup>2/2) vs))) vs"
  unfolding softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<^sub>2  
  by (simp add: Groups.add_ac(2) fold_plus_sum_list_rev foldl_conv_fold) 

lemma softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<^sub>2': "softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r 2 vs = map (\<lambda> (v::real). (1 + v + v\<^sup>2/2) / (foldl (\<lambda>a x. a + (1 + x + x\<^sup>2 / 2)) 0 vs)) vs"
  apply(simp add: softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<^sub>2)
  by(code_simp, simp)

definition
  \<open>argmax vs = map (\<lambda> v. if v = Max (set vs) then 1 else 0) vs\<close> 

text\<open>
\autoref{tab:tensorflow-activation} provides a mapping from our names of the activation functions 
to the names used by TensorFlow (see \<^url>\<open>https://www.tensorflow.org/api_docs/python/tf/keras/activations/\<close>).
  
\begin{landscape}
\begin{table}
\caption{Mapping of the activation functions supported by TensorFlow.}
\label{tab:tensorflow-activation}
\begin{center}
\small\renewcommand{\arraystretch}{1.2}
\begin{tabular}{@ {}llp{14cm}@ {}}
   \toprule
                                 & TensorFlow 2.8.0 & Definition\\
    \cmidrule(r){2-3}
    @{const \<open>identity\<close>}          & linear                         & \vspace{-.7cm}@{thm [display, margin=120]  "identity_def"}\vspace{-0.9cm}\\ 
    @{const \<open>softsign\<close>}          & softsign                       & \vspace{-.7cm}@{thm [display, margin=120]  "softsign_def"}\vspace{-0.9cm}\\ 
    @{const \<open>sigmoid\<close>}           & sigmoid                        & \vspace{-.7cm}@{thm [display, margin=120]  "sigmoid_def"}\vspace{-0.9cm}\\  
    @{const \<open>sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}      & \multicolumn{1}{c}{--}         & \vspace{-.7cm}@{thm [display, margin=120]  "sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def"}\vspace{-0.9cm}\\  
    @{const \<open>swish\<close>}             & swish                          & \vspace{-.7cm}@{thm [display, margin=120]  "swish_def"}\vspace{-0.9cm}\\  
    @{const \<open>swish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}        & \multicolumn{1}{c}{--}         & \vspace{-.7cm}@{thm [display, margin=120]  "swish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def"}\vspace{-0.9cm}\\  
    @{const \<open>tanh\<close>}              & thanh                          & \vspace{-.7cm}@{thm [display, margin=120]  "tanh_def"}\vspace{-0.9cm}\\ 
    @{const \<open>generalized_relu\<close>}  & relu                           & \vspace{-.7cm}@{thm [display, margin=120]  "generalized_relu_def"}\vspace{-0.9cm}\\
    @{const \<open>relu\<close>}              & relu (with default parameters) & \vspace{-.7cm}@{thm [display, margin=120]  "relu_def"}\vspace{-0.9cm}\\ 
    @{const \<open>gelu_approx\<close>}       & gelu (approx=True)             & \vspace{-.7cm}@{thm [display, margin=120]  "gelu_approx_def"}\vspace{-0.9cm}\\
    \multicolumn{1}{c}{--}       & gelu (approx=False)            & \multicolumn{1}{c}{--}\\
    @{const \<open>softplus\<close>}          & softplus                       & \vspace{-.7cm}@{thm [display, margin=120]  "softplus_def"}\vspace{-0.9cm}\\     
    @{const \<open>elu\<close>}               & elu                            & \vspace{-.7cm}@{thm [display, margin=120]  "elu_def"}\vspace{-0.9cm}\\
    @{const \<open>elu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}          & \multicolumn{1}{c}{--}          & \vspace{-.7cm}@{thm [display, margin=120]  "elu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def"}\vspace{-0.9cm}\\
    @{const \<open>selu\<close>}              & selu                           &\vspace{-.7cm}@{thm [display, margin=120]  "selu_def"}\vspace{-0.9cm}\\
    @{const \<open>selu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}         & \multicolumn{1}{c}{--}         & \vspace{-.7cm}@{thm [display, margin=120]  "selu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def"}\vspace{-0.9cm}\\
    @{const \<open>exp\<close>}               & exponential                    & \vspace{-.7cm}@{thm [display, margin=120]  "exp_def"}\vspace{-0.9cm}\\
    @{const \<open>exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}          & \multicolumn{1}{c}{--}          & \vspace{-.7cm}@{thm [display, margin=120]  "exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def"}\vspace{-0.9cm}\\
    @{const \<open>hard_sigmoid\<close>}      & hard\_sigmoid                  & \vspace{-.7cm}@{thm [display, margin=120]  "hard_sigmoid_def"}\vspace{-0.9cm}\\ 
    @{const \<open>softmax\<close>}           & softmax                        & \vspace{-.7cm}@{thm [display, margin=120]  "softmax_def"}\vspace{-0.9cm}\\ 
    @{const \<open>softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r\<close>}      & \multicolumn{1}{c}{--}          & \vspace{-.7cm}@{thm [display, margin=120]  "softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r_def"}\vspace{-0.9cm}\\ 
    \bottomrule
\end{tabular}\end{center}\end{table}
\end{landscape}
\<close>

subsection\<open>Derivatives of Activation Functions\<close>

lemma has_real_derivative_transform:
  \<open>x \<in> s \<Longrightarrow> (\<And>x. x \<in> s \<Longrightarrow> g x = f x) \<Longrightarrow> (f has_real_derivative f') (at x within s) 
                                        \<Longrightarrow> (g has_real_derivative f') (at x within s)\<close>
  by (simp add: has_derivative_transform has_field_derivative_def)

lemma one_plus_exp_eq: "(1 + exp v) = (exp v) * (1 + exp (- v))  "
  by (simp add: distrib_left exp_minus_inverse)

definition \<open>identity'        = (\<lambda> v. 1.0)\<close>
lemma identity'[simp]: \<open>(identity has_real_derivative (identity' v))  (at v)\<close>
  by(simp add:identity_def identity'_def) 

definition \<open>logistic' L k v\<^sub>0 = (\<lambda> v. (exp( (-k)*(v-v\<^sub>0)) * k * L) / (1 + exp((-k)*(v-v\<^sub>0)))\<^sup>2)\<close>
lemma logistic'[simp]: \<open>((logistic L k v\<^sub>0) has_real_derivative ((logistic' L k v\<^sub>0) v))  (at v)\<close>
  apply (simp add:logistic_def logistic'_def, intro derivative_eq_intros, simp_all)
    subgoal by (metis add_eq_0_iff exp_ge_zero le_minus_one_simps(3))
    subgoal by (simp add: power2_eq_square) 
    done 

definition \<open>tanh'            = (\<lambda> v. 1 - ((tanh v)\<^sup>2))\<close>
lemma tanh'[simp]: \<open>(tanh has_real_derivative (tanh' v))  (at v)\<close>
  by (auto intro: derivative_eq_intros simp add:tanh'_def) 

definition \<open>softplus'        = (\<lambda> v. 1 / (1 + exp(-v)))\<close>
lemma softplus'[simp]: \<open>(softplus has_real_derivative (softplus' v))  (at v)\<close>
    apply (simp add: softplus_def softplus'_def, intro derivative_eq_intros, simp_all add: add_pos_pos) 
    by (metis one_plus_exp_eq add.left_neutral exp_not_eq_zero mult.right_neutral 
              nonzero_divide_mult_cancel_left)

definition \<open>prelu1'          = (\<lambda> v. 1)\<close>
lemma prelu1'[simp]: \<open>((prelu 1) has_real_derivative (prelu1' v))  (at v)\<close>
proof (-)
  have *:  \<open>(\<lambda> v. if v < (0::real) then (1::real) * v else v) = (\<lambda> v. v)\<close> by auto
  show ?thesis
  by (simp add: prelu_def prelu1'_def if_split *)
qed
  
definition \<open>silu'            = (\<lambda> v. (1 + exp (-v) + v * (exp (-v)) ) / ((1 + exp(-v))\<^sup>2))\<close>
lemma silu'[simp]: \<open>(silu has_real_derivative (silu' v))  (at v)\<close>
  apply(simp add:silu_def silu'_def) 
  apply (intro derivative_eq_intros, simp_all) 
  subgoal by (metis add_eq_0_iff exp_ge_zero le_minus_one_simps(3))
  subgoal by (simp add: power2_eq_square) 
  done

definition \<open>gaussian'        = (\<lambda> v. -2 * v * exp (- v\<^sup>2))\<close>
lemma gaussian'[simp]: \<open>(gaussian has_real_derivative (gaussian' v))  (at v)\<close>
  by (simp add:gaussian_def gaussian'_def, intro derivative_eq_intros, simp_all, simp) 


subsection\<open>Single Class Folding Activation Functions\<close>

datatype activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e = Identity |  Sign | BinaryStep | Logistic real real real | Logistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat real real real 
                         | Tanh | Sigmoid | Sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | ReLU | GReLU real \<open>real option\<close> real 
                         | Softplus | SoftSign | Swish | Swish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | GeLUapprox | ELU real 
                         | ELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat real | SELU | SELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | PReLU real | SiLU | SiLU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat 
                         | Gaussian | Gaussian\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | Exp | Exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | HardSigmoid 

fun \<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e:: \<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e \<Rightarrow> (real \<Rightarrow> real) option\<close> where
   \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e Identity          = Some identity\<close>                 
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e Sign              = Some sign\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e BinaryStep        = Some binary_step\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e SoftSign          = Some softsign\<close>                 
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (Logistic L k v\<^sub>0) = Some (logistic L k v\<^sub>0)\<close>           
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (Logistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n L k v\<^sub>0) = Some (logistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n L k v\<^sub>0)\<close>           
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e Sigmoid           = Some sigmoid\<close>                  
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (Sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)   = Some (sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)\<close>                  
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e Swish             = Some swish\<close>                    
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (Swish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)    = Some (swish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)\<close>                    
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e Tanh              = Some tanh\<close>                     
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e ReLU              = Some relu\<close>                     
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e GeLUapprox        = Some gelu_approx\<close>              
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (GReLU \<alpha> m t)     = Some (generalized_relu \<alpha> m t)\<close> 
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e Softplus          = Some softplus\<close>                     
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (ELU \<alpha>)           = Some (elu \<alpha>)\<close>                  
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (ELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n \<alpha>)    = Some (elu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n \<alpha>)\<close>                  
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e SELU              = Some selu\<close>                     
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (SELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)      = Some (selu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)\<close>                     
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e Exp               = Some exp\<close>                      
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (Exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)       = Some (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)\<close>                      
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e HardSigmoid       = Some hard_sigmoid\<close>             
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (PReLU \<alpha>)         = Some (prelu \<alpha>)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e SiLU              = Some silu\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (SiLU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)      = Some (silu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e Gaussian          = Some gaussian\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e (Gaussian\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)  = Some (gaussian\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)\<close>
text\<open> 
  The datatype @{type \<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>} enumerates a list of standard activation functions that are 
  commonly used as part of computing the weighted sum (fold) of all inputs of a neuron. The 
  function @{const \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>} provides easy access to the activation function itself.
\<close>

fun \<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e':: \<open>activation\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e \<Rightarrow> (real \<Rightarrow> real option)\<close> where
   \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' Identity          = (\<lambda>v. Some (identity' v))\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' Sign              = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' BinaryStep        = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (Logistic L k v\<^sub>0) = (\<lambda>v. Some (logistic' L k v\<^sub>0 v))\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (Logistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n L k v\<^sub>0) = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' Tanh              = (\<lambda>v. Some (tanh' v))\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' ReLU              = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' Softplus          = (\<lambda>v. Some (softplus' v))\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (ELU \<alpha>)           =  (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (ELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n \<alpha>)    =  (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (PReLU \<alpha>)         = (\<lambda> v. if \<alpha> = 1 then Some (prelu1' v) else None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' SiLU              = (\<lambda>v. Some (silu' v))\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (SiLU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)     = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' Gaussian          = (\<lambda>v. Some (gaussian' v))\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (Gaussian\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n) = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (GReLU v va vb)   = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' GeLUapprox        = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' Sigmoid           = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (Sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)  = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' SoftSign          = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' Swish             = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (Swish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)    = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' SELU              = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (SELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)     = (\<lambda>v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' Exp               = (\<lambda> v. Some (exp v))\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (Exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)      = (\<lambda> v. None)\<close>
 | \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' HardSigmoid       = (\<lambda>v. None)\<close> 

text\<open>
  The function @{const \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e'\<close>} defines, for derivable activation functions, their derivative. 
  Note that we require derivability in the mathematical sense. For example, while some machine 
  learning text books consider the binary step function derivable except at the point 0, we consider 
  it non derivable, as the binary step function is non continuous at the point 0. In the following, 
  we also provide the ``approximated  derivatives'' of non-continuous activation functions:
\<close>
                 
lemma 
  assumes \<open>v \<in> (dom (\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' a))\<close>
  shows   \<open>((\<lambda> v. the (\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e a) v) has_real_derivative (the (\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' a v))) (at v within (dom (\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' a)))\<close>
  using assms by (cases a, auto)

subsection\<open>Multiclass Folding Activation Functions\<close>

datatype activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i = mIdentity |  mSign | mBinaryStep |  mLogistic real real real | mLogistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat real real real 
                        | mTanh  | mSigmoid | mSigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | mReLU | mGReLU real \<open>real option\<close> real
                        | mSoftplus | mSoftSign | mSwish | mSwish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | mGeLUapprox | mELU real 
                        | mELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat real | mSELU | mSELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | mPReLU real | mSiLU | mSiLU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat 
                        | mGaussian | mGaussian\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | mExp | mExp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | mHardSigmoid | mSoftmax 
                        | mSoftmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r nat | mArgmax

fun \<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i :: \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  \<Rightarrow> (real list \<Rightarrow> real list) option\<close> where
   \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mIdentity          = Some (map identity)\<close>                 
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mSign              = Some (map sign)\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mBinaryStep        = Some (map binary_step)\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mSoftSign          = Some (map softsign)\<close>                 
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mLogistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n L k v\<^sub>0) = Some (map (logistic\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n L k v\<^sub>0))\<close>           
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mLogistic L k v\<^sub>0) = Some (map (logistic L k v\<^sub>0))\<close>           
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mSigmoid           = Some (map sigmoid)\<close>                   
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mSigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)  = Some (map (sigmoid\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n))\<close>                   
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mSwish             = Some (map swish)\<close>                      
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mSwish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)    = Some (map (swish\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n))\<close>                      
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mTanh              = Some (map tanh)\<close>                     
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mReLU              = Some (map relu)\<close>                      
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mGeLUapprox        = Some (map gelu_approx)\<close>               
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mGReLU \<alpha> m t)     = Some (map (generalized_relu \<alpha> m t))\<close>  
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mSoftplus          = Some (map softplus)\<close>                      
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mELU \<alpha>)           = Some (map (elu \<alpha>))\<close>                  
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n \<alpha>)    = Some (map (elu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n \<alpha>))\<close>                  
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mSELU              = Some (map selu)\<close>                     
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mSELU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)     = Some (map (selu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n))\<close>                     
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mExp               = Some (map exp)\<close>                      
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mExp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)      = Some (map (exp\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n))\<close>                      
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mHardSigmoid       = Some (map hard_sigmoid)\<close>              
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mPReLU \<alpha>)         = Some (map (prelu \<alpha>))\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mSiLU              = Some (map silu)\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mSiLU\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)     = Some (map (silu\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n))\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mGaussian          = Some (map gaussian)\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mGaussian\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n) = Some (map (gaussian\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n))\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mSoftmax           = Some softmax\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  (mSoftmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)  = Some (softmax\<^sub>t\<^sub>a\<^sub>y\<^sub>l\<^sub>o\<^sub>r n)\<close>
 | \<open>\<phi>\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i  mArgmax            = Some argmax\<close>

text\<open> 
  The datatype @{type \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>} enumerates a list of standard activation functions that are 
  commonly used as part of computing the weighted sum (fold) of all inputs of a neuron. The 
  function @{const \<open>\<phi>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e\<close>} provides easy access to the activation function itself.
\<close>

section\<open>Encoding of Activion Functions\<close>

ML\<open>
signature ACTIVATION_TERM = sig
    datatype mode = MultiList | MultiMatrix | Single
    datatype activationT = Elu | Exponential | GRelu | Gelu | Hard_sigmoid | Linear | Relu | Selu 
                         | Sigmoid | Softmax | Softmax_taylor | Softplus | Softsign | Sign | BinaryStep | Swish | Tanh
                         | Sigmoid_taylor
    val add_function: binding -> term list -> local_theory -> Proof.context
    val def_phi_tab: mode -> string -> activationT list -> local_theory -> Proof.context
    val term_of_activation_eqn_multi_list: activationT -> term
    val term_of_activation_eqn_multi_matrix: activationT -> term
    val term_of_activation_eqn_single: activationT -> term
    val term_of_activation_multi: activationT -> term
    val term_of_activation_single: activationT -> term
  end
\<close>

ML_file \<open>Tools/Activation_Functions.ML\<close>
                        
text\<open>
  The ML structure @{ML_structure  \<open>Activation_Term:ACTIVATION_TERM\<close> } provides the core infrastructure
  to construct HOL terms for the activation on the ML-level.
\<close>

end
