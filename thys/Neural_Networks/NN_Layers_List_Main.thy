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

subsection\<open>Neural Network as Sequential Layers using Lists (\thy)\<close>
theory 
  NN_Layers_List_Main
  imports
    Main
    NN_Layers
    "HOL-Library.Interval"
    Properties
begin 
text\<open>\label{sec:list}\<close>

definition \<open>valid_activation_tab\<^sub>l tab = (\<forall> f \<in> ran tab. \<forall> xs. length xs = length (f xs))\<close>

lemma valid_activation_preserves_length: 
  assumes \<open>valid_activation_tab\<^sub>l t\<close>
  assumes \<open>t n = Some f\<close>
  shows \<open>length xs = length (f xs)\<close>
  using assms unfolding valid_activation_tab\<^sub>l_def
  by (simp add: ranI) 

fun  layer_consistent\<^sub>l :: "('a list, 'b, 'a list list) neural_network_seq_layers \<Rightarrow> nat \<Rightarrow> ('a list, 'b , 'a list list) layer \<Rightarrow> bool"  where
  \<open>layer_consistent\<^sub>l _ nc (In l) = (0 < units l \<and> nc = units l)\<close>
| \<open>layer_consistent\<^sub>l _ nc (Out l) = (0 < units l \<and> nc = units l)\<close>
| \<open>layer_consistent\<^sub>l N nc (Activation l) = ( (0 < units l \<and> nc =  units l) 
                                             \<and> ( ((activation_tab N) (\<phi> l)) \<noteq> None  ))\<close>
| \<open>layer_consistent\<^sub>l N nc (Dense l) =  (0 < units l \<and> 0 < nc 
                                             \<and> length (\<beta> l) = units l 
                                             \<and> length (\<omega> l) = units l
                                             \<and> (\<forall>r\<in>set (\<omega> l). length r = nc)
                                             \<and> ( ((activation_tab N) (\<phi> l)) \<noteq> None  ))\<close>

fun layers_consistent\<^sub>l where
  \<open>layers_consistent\<^sub>l N  _ [] = True \<close>
 |\<open>layers_consistent\<^sub>l  N w (l#ls) = ((layer_consistent\<^sub>l N w l) \<and> (layers_consistent\<^sub>l N (out_deg_layer l)  ls))\<close>


lemma layer_consistent\<^sub>l_in_deg_layer:
  assumes "layer_consistent\<^sub>l N nc l " 
  shows "in_deg_layer l = nc "
proof(cases l)
  case (In x1)
  then show ?thesis using assms by simp
next
  case (Out x2)
  then show ?thesis using assms by simp
next
  case (Dense x3)
  then show ?thesis using assms by simp
next
  case (Activation x4)
  then show ?thesis using assms by simp
qed

lemma layers_consistent\<^sub>l_in_deg:
  assumes "(layers_consistent\<^sub>l N nc (l#ls'))"
shows "in_deg_layer l = nc"
proof(insert assms, cases l)
  case (In x1)
  then show ?thesis 
    using assms by simp
next
  case (Out x2)
  then show ?thesis using assms by simp
next
  case (Dense x3)
  then show ?thesis using assms by simp
next
  case (Activation x4)
  then show ?thesis using assms by simp
qed


lemma layer_consistent\<^sub>l_activation_tab_const:
  \<open>layer_consistent\<^sub>l N nc l = layer_consistent\<^sub>l \<lparr>layers = ls, activation_tab = activation_tab N\<rparr> nc l\<close>
  by(cases l, simp_all) 


lemma layers_consistent\<^sub>l_activation_tab_const: 
  \<open>layers_consistent\<^sub>l N nc ls = layers_consistent\<^sub>l \<lparr>layers = ls', activation_tab = activation_tab N\<rparr> nc ls\<close>
proof(induction ls arbitrary: nc)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  then show ?case 
    by(simp add: layer_consistent\<^sub>l_activation_tab_const[symmetric])
qed

lemma layers_consistent\<^sub>l_layersN_const: 
  \<open>layers_consistent\<^sub>l N = layers_consistent\<^sub>l \<lparr>layers = ls', activation_tab = activation_tab N\<rparr>\<close>
  using layers_consistent\<^sub>l_activation_tab_const by blast 

lemma layers_consistent\<^sub>lAll:
  assumes \<open>layers_consistent\<^sub>l N inputs (layers N)\<close>
  shows \<open>\<forall> l \<in> set (layers N). \<exists> n . layer_consistent\<^sub>l N n l\<close>
proof(cases N)
  case (fields layers activation_tab)
  then have "\<forall>l\<in>set layers. \<exists>n. layer_consistent\<^sub>l \<lparr>layers = layers, activation_tab = activation_tab\<rparr> n l"
  proof(insert assms[simplified fields, simplified], induction "layers" arbitrary:inputs activation_tab N)
    case Nil
    then show ?case by simp
  next
    case (Cons a layers)
    then show ?case 
      apply(simp)
      using Cons fields layers_consistent\<^sub>l_activation_tab_const layer_consistent\<^sub>l_activation_tab_const
        neural_network_seq_layers.select_convs(2) 
      by metis
  qed
  then 
  show ?thesis
    using fields by simp 
qed

lemma layers_consistent\<^sub>lAll': 
  assumes \<open>layers_consistent\<^sub>l N (in_deg_NN N) (layers N)\<close>
  shows \<open>\<forall> l \<in> set (layers N). \<exists> n . layer_consistent\<^sub>l N n l\<close>
  using assms layers_consistent\<^sub>lAll by blast

lemma layers_consistent\<^sub>l_layer_consistent\<^sub>l_Dense:
  assumes \<open>layers_consistent\<^sub>l N (in_deg_NN N) (layers N)\<close> 
    and "(Dense x3) \<in> set (layers N )"
  shows \<open>layer_consistent\<^sub>l N (length (\<omega> x3 ! 0)) (Dense x3) \<close>
  using assms layer_consistent\<^sub>l.simps(4)[of N "(length (\<omega> x3 ! 0))" x3] 
  by (metis layer_consistent\<^sub>l.simps(4) layers_consistent\<^sub>lAll' nth_mem)

lemma layers_consistent\<^sub>l_layer_consistent\<^sub>l_Activation:
  assumes \<open>layers_consistent\<^sub>l N (in_deg_NN N) (layers N)\<close> 
    and "(Activation x3) \<in> set (layers N )"
  shows \<open>layer_consistent\<^sub>l N (units x3) (Activation x3) \<close>
  using assms layer_consistent\<^sub>l.simps(3)[of N _ x3] 
  by (meson layer_consistent\<^sub>l.simps(3) layers_consistent\<^sub>lAll)


locale neural_network_sequential_layers\<^sub>l = 
  fixes N::\<open>('a::comm_ring list, 'b, 'a list list) neural_network_seq_layers\<close>
  assumes head_is_In:  \<open>isIn (hd (layers N))\<close>
    and     last_is_Out: \<open>isOut (last (layers N))\<close>
    and     layer_internal: \<open>list_all isInternal  ((tl o butlast) (layers N))\<close>
    and     activation_tab_valid: \<open>valid_activation_tab\<^sub>l (activation_tab N)\<close>  
    and     layer_valid:  \<open>layers_consistent\<^sub>l N (in_deg_NN N) (layers N)\<close> 
begin              
lemma layers_nonempty: \<open>layers N \<noteq> []\<close>
  by (metis hd_Nil_eq_last head_is_In isIn.elims(2) isOut.simps(2) last_is_Out) 

lemma min_length_layers_two: \<open>1 < length (layers N)\<close>
  by (metis (no_types, lifting) One_nat_def add_0 append_Nil append_butlast_last_id 
      append_eq_append_conv head_is_In isIn.simps(2) isOut.elims(2) last_is_Out 
      layers_nonempty length_0_conv less_one linorder_neqE_nat list.sel(1) list.size(4)) 

lemma layers_structure: \<open>\<exists> il ol ls. layers N = (In il)#ls@[Out ol]\<close> 
  by (metis (no_types, lifting) append_butlast_last_id head_is_In isIn.elims(2) isOut.elims(2) 
      last.simps last_is_Out layer.distinct(1) layers_nonempty list.exhaust list.sel(1)) 

end 


text \<open>We use locales (i.e., Isabelle's mechanism for parametric theories) to capture
fundamental concepts that are shared between different models of neural
networks. 

We start by defining a locale @{term "neural_network_sequential_layers\<^sub>l"} to
describe the common concepts of all neural network models that use layers are core building 
blocks. For our representation to be a well-formed sequential model, we require that the 
first layer is an input layer and the last layer is an output layer\<close>



fun  predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l ::\<open>('a::{monoid_add,times} list, 'b, 'a list list) neural_network_seq_layers \<Rightarrow> ('a list) option \<Rightarrow> ('a list, 'b, 'a list list) layer \<Rightarrow> ('a list ) option\<close>  
  where
    \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (In l)  = (if layer_consistent\<^sub>l N (length vs) (In l) then Some vs else None)\<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (Out l) = (if layer_consistent\<^sub>l N (length vs) (Out l) then Some vs else None)\<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (Dense pl) = (if layer_consistent\<^sub>l N (length vs) (Dense pl)  then 
                                              (let
                                                in_w_pairs = map (\<lambda> e. zip vs e) (\<omega> pl);
                                                wsums      = map (\<lambda> vs'. \<Sum>(x,y)\<leftarrow>vs'. x*y) in_w_pairs;
                                                wsum_bias  = map (\<lambda> (s,b). s+b) (zip wsums (\<beta> pl))
                                              in 
                                              (case activation_tab N (\<phi> pl) of 
                                                  None   \<Rightarrow> None 
                                                | Some f \<Rightarrow> Some (f wsum_bias )))
                                            else None)
                                          \<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (Activation pl) = (if layer_consistent\<^sub>l N (length vs) (Activation pl) then
                                                  (case activation_tab N (\<phi> pl) of
                                                     None \<Rightarrow> None
                                                   | Some f \<Rightarrow> Some (f vs))
                                                else None)
                                               \<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l _ None _ = None\<close>
lemma length_out: \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N' vs (Out l) = Some res \<Longrightarrow> length(res) = (units l)\<close>
  by(cases vs, auto split:if_splits)

fun  
  predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl ::\<open>('a::{monoid_add,times} list, 'b, 'a list list) neural_network_seq_layers \<Rightarrow> 'a list \<Rightarrow> ('a list, 'b, 'a list list) layer \<Rightarrow> 'a list\<close>  
  where
    \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl N vs (In l)  = vs\<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl N vs (Out l) = vs\<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl N vs (Dense pl) = (let
                                             in_w_pairs = map (\<lambda> e. zip vs e) (\<omega> pl);
                                             wsums      = map (\<lambda> vs'. \<Sum>(x,y)\<leftarrow>vs'. x*y) in_w_pairs;
                                             wsum_bias  = map (\<lambda> (s,b). s+b) (zip wsums (\<beta> pl));
                                             \<phi>\<^sub>l = the (activation_tab N (\<phi> pl)) 
                                           in 
                                             \<phi>\<^sub>l wsum_bias)
                                          \<close>

| \<open> predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl N vs (Activation pl) = (let
                                             \<phi>\<^sub>l = the (activation_tab N (\<phi> pl)) 
                                           in 
                                             \<phi>\<^sub>l vs)
                                           \<close>

definition \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N inputs = foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N) (Some inputs) (layers N)\<close>
definition \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_impl N inputs = foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl N) inputs (layers N)\<close>


lemma predict_layer_Some:
  assumes \<open>(layer_consistent\<^sub>l N (length xs) l)\<close> 
  shows \<open>(predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some xs) l \<noteq> None) \<close>  
proof(cases l)
  case (In x1)
  then show ?thesis using assms by(simp)
next
  case (Out x2)
  then show ?thesis using assms by simp 
next
  case (Dense x3)
  then show ?thesis using assms by force
next
  case (Activation x4)
  then show ?thesis using assms by force
qed

text \<open>The input and output layers of our network pass the inputs directly onto the
next layer without any calculation performed; this can be seen in the first two
cases of the @{const "predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l"} function. The dense layer of the network is where 
the weighted sum is calculated, case three in @{const "predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l"}, where first the 
input weights are transposed (@{term "in_weights"}), then zipped with their input value
(@{term "in_w_pairs"}), before calculating the weighted sum (@{term" wsums"}), adding the bias (@{term "wsum_bias"}), 
and finally applying the activation function on the result, producing the output for a
single dense layer. To calculate the prediction of the network given a set of
inputs we then fold @{const "predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l"} over the network from left to right 
(@{const "foldl"}) in @{const "predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l"}. \<close>

lemma fold_predict_l_strict: \<open>(foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N) None ls) = None\<close>
  by(induction "ls", simp_all)


lemmas [nn_layer] = predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l.simps predict_layer_Some fold_predict_l_strict

lemma predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_activation_tab: assumes "activation_tab N = activation_tab N'" shows
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N x xs = predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N' x xs\<close>
proof(cases xs)
  case (In x1)
  then show ?thesis proof(cases "x")
    case None
    then show ?thesis using In assms by(simp) 
  next
    case (Some a)
    then show ?thesis using In assms by(simp) 
  qed  
next
  case (Out x2)
  then show ?thesis proof(cases "x")
    case None
    then show ?thesis using Out assms by(simp) 
  next
    case (Some a)
    then show ?thesis using Out assms by(simp) 
  qed  
next
  case (Dense x3)
  then show ?thesis proof(cases x)
    case None
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis by(auto simp add:assms Dense)
  qed
next
  case (Activation x4)
  then show ?thesis proof(cases "x")
    case None
    then show ?thesis using Activation assms by(simp) 
  next
    case (Some a)
    then show ?thesis using Activation assms by(simp) 
  qed  
qed

lemma predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_activation_tab_const: \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N = predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = l, activation_tab = activation_tab N\<rparr>\<close>
  apply(rule ext)+
  by (metis neural_network_seq_layers.select_convs(2) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_activation_tab)

lemma input_layer:
  assumes \<open>y = length i\<close> and \<open>0 < y\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some i) (In  \<lparr>name = x, units = y\<rparr>) = (Some i)\<close>
  using assms 
  by simp

lemma output_layer:
  assumes \<open>y = length i\<close> and \<open>0 < y\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some i) (Out  \<lparr>name = x, units = y\<rparr>) = (Some i)\<close>
  using assms 
  by simp

lemma dense_layer:
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some i) (Dense \<lparr>name = x, units = y, ActivationRecord.\<phi> = p, LayerRecord.\<beta> = b, \<omega> = w\<rparr>) = 
        (if layer_consistent\<^sub>l N (length i) (Dense \<lparr>name = x, units = y, ActivationRecord.\<phi> = p, LayerRecord.\<beta> = b, \<omega> = w\<rparr>) then 
          (let in_w_pairs = map (\<lambda> e. zip i e) w;
               wsums      = map (\<lambda> vs'. \<Sum>(x,y)\<leftarrow>vs'. x*y) in_w_pairs;
               wsum_bias  = map (\<lambda> (s,b). s+b) (zip wsums b)
          in 
           (case activation_tab N p of 
                  None   \<Rightarrow> None
                | Some f \<Rightarrow> Some (f wsum_bias )))
           else None)\<close>
  by simp 


lemma dense_layer':
  assumes \<open>activation_tab N p = Some a\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some i) (Dense \<lparr>name = x, units = y, ActivationRecord.\<phi> = p, LayerRecord.\<beta> = b, \<omega> = w\<rparr>) = 
        (if layer_consistent\<^sub>l N (length i) (Dense \<lparr>name = x, units = y, ActivationRecord.\<phi> = p, LayerRecord.\<beta> = b, \<omega> = w\<rparr>) then 
          (let in_w_pairs = map (\<lambda> e. zip i e) w;
               wsums      = map (\<lambda> vs'. \<Sum>(x,y)\<leftarrow>vs'. x*y) in_w_pairs;
               wsum_bias  = map (\<lambda> (s,b). s+b) (zip wsums b)
          in Some (a wsum_bias))
         else None)\<close>
  using assms
  by simp

lemma activation_layer:
  assumes \<open>y = length i\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some i) (Activation  \<lparr>name = x, units = y, ActivationRecord.\<phi> = p\<rparr>) = 
        (if layer_consistent\<^sub>l N (length i) (Activation \<lparr>name = x, units = y, ActivationRecord.\<phi> = p\<rparr>) then 
              (case activation_tab N p of None \<Rightarrow> None | Some f \<Rightarrow> Some (f i))
        else None)\<close>
  using assms
  by simp

lemma activation_layer':
  assumes \<open>y = length i\<close>
    and \<open>activation_tab N p = Some a\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some i) (Activation  \<lparr>name = x, units = y, ActivationRecord.\<phi> = p\<rparr>) = 
        (if layer_consistent\<^sub>l N (length i) (Activation \<lparr>name = x, units = y, ActivationRecord.\<phi> = p\<rparr>) then Some (a i) else None)\<close>
  using assms
  by simp

lemma predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl_activation_tab_const: \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl N = predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl \<lparr>layers = l, activation_tab = activation_tab N\<rparr>\<close>
  apply(rule ext)+
  using neural_network_seq_layers.select_convs predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_activation_tab predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl.elims predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl.simps
  by (smt (verit))

context neural_network_sequential_layers\<^sub>l begin 

lemma img_None_1: assumes \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N xs) \<noteq> None)\<close> shows \<open>(length xs = (in_deg_NN N))\<close>
proof - 
  have 1: \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N xs) \<noteq> None) \<longrightarrow> (length xs = (in_deg_NN N))\<close>
  proof(cases N)
    case (fields layers' activation_tab') note i = this
    then show ?thesis 
      unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_def 
      using i layers_nonempty 
    proof(induction layers')
      case Nil
      then show ?case by simp
    next
      case (Cons a layers')
      then show ?case proof(cases a)
        case (In x1)
        then show ?thesis using Cons 
          by (simp add: fold_predict_l_strict in_deg_NN_def) 
      next
        case (Out x2)
        then show ?thesis using Cons neural_network_sequential_layers\<^sub>l_axioms
          by (simp add: fold_predict_l_strict in_deg_NN_def) 
      next
        case (Dense x3)
        then show ?thesis using Cons neural_network_sequential_layers\<^sub>l_axioms i
          apply(simp add: fold_predict_l_strict in_deg_NN_def)
          using Cons   by (metis isIn.simps(3) list.sel(1) neural_network_seq_layers.select_convs(1) 
              neural_network_sequential_layers\<^sub>l.head_is_In) 
      next
        case (Activation x4)
        then show ?thesis using Cons neural_network_sequential_layers\<^sub>l_axioms i
          by(simp add: fold_predict_l_strict in_deg_NN_def)
      qed
    qed
  qed 
  show ?thesis using assms 1 by simp 
qed

lemma img_None_2':
  assumes  a0: \<open>layers' \<noteq> [] \<close> 
    and a4: \<open>valid_activation_tab\<^sub>l activation_tab'\<close>
    and a1:  \<open>layers_consistent\<^sub>l \<lparr>layers = [], activation_tab=activation_tab' \<rparr> (length xs) layers'\<close> 
  shows \<open>foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = [], activation_tab = activation_tab'\<rparr>) (Some xs) layers' \<noteq> None\<close>
proof(insert assms, induction "layers'" arbitrary: xs rule:list_nonempty_induct)
  case (single l)
  then show ?case 
  proof(cases l)
    case (In x1)
    then show ?thesis 
      using single by(simp)
  next
    case (Out x2)
    then show ?thesis 
      using single by(simp)
  next
    case (Dense x3)
    then show ?thesis 
      using single by(force)
  next
    case (Activation x4)
    then show ?thesis 
      using single by(force)
  qed
next
  case (cons l ls)
  then show ?case 
  proof(cases l)
    case (In x1)
    then show ?thesis using cons by simp 
  next
    case (Out x2)
    then show ?thesis using cons by simp 
  next
    case (Dense x3)
    then show ?thesis 
     using cons assms
     apply clarsimp
     apply (subst cons.IH[simplified], simp_all)
     using valid_activation_preserves_length by force
  next
    case (Activation x4)
    then show ?thesis 
      using cons assms apply clarsimp
      apply(subst cons.IH[simplified], simp_all)
      by (metis valid_activation_preserves_length) 
  qed
qed

lemma img_None_2: 
  assumes \<open>length xs = in_deg_NN N\<close> 
  shows \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N xs) \<noteq> None)\<close>
proof(cases N)
  case (fields layers activation_tab)
  then show ?thesis 
    using assms layer_valid apply simp
    unfolding neural_network_sequential_layers\<^sub>l_def  predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_def
    apply(subst         predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_activation_tab_const[of _ "[]"]) 
    apply simp
    apply(subst img_None_2'[of layers activation_tab xs, simplified], simp_all)
    using layers_nonempty apply force 
    using activation_tab_valid apply fastforce 
    using assms layer_valid unfolding in_deg_NN_def apply simp
    using layers_consistent\<^sub>l_activation_tab_const by fastforce 
qed


lemma img_None: \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N xs) \<noteq> None) = (length xs = in_deg_NN N)\<close>
  using img_None_1 img_None_2 by blast 

lemma img_Some: \<open>(\<exists> y. (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N xs) = Some y) = (length xs = in_deg_NN N)\<close>
  using img_None by simp 

lemma img_length: \<open>(\<exists> y. ((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N xs) = Some y) \<longrightarrow> (length y = out_deg_NN N))\<close>
proof(cases N)
  case (fields layers' activation_tab') note i = this
  then show ?thesis 
    unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_def i
  proof(induction layers' arbitrary: xs rule:rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc a layers')
    then show ?case proof(cases a)
      case (In x1)
      then show ?thesis using snoc
        using Ex_list_of_length by blast 
    next
      case (Out x2)
      then show ?thesis using snoc
        apply (simp add: fold_predict_l_strict out_deg_NN_def neural_network_sequential_layers\<^sub>l_def) 
        using Ex_list_of_length by blast
    next
      case (Dense x3)
      then show ?thesis using Cons neural_network_sequential_layers\<^sub>l_axioms i
        apply(simp add: fold_predict_l_strict in_deg_NN_def)
        using snoc
        by (smt (verit, ccfv_threshold) Ex_list_of_length)
    next
      case (Activation x4)
      then show ?thesis using Cons neural_network_sequential_layers\<^sub>l_axioms i
        apply(simp add: fold_predict_l_strict in_deg_NN_def)
        using snoc 
        by (smt (verit, ccfv_threshold) Ex_list_of_length)
    qed
  qed
qed 

lemma predit\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl_eq:
  assumes \<open>layer_consistent\<^sub>l N (length inputs) l\<close>
  shows   \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some inputs) l = Some (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl N inputs l)\<close>
proof(cases "l")
  case (In x1)
  then show ?thesis using assms by(simp)
next
  case (Out x2)
  then show ?thesis using assms by(simp)
next
  case (Dense x3)
  then show ?thesis 
    using Dense assms by(force)
next
  case (Activation x4)
  then show ?thesis using Activation assms by(force)
qed


lemma aux_length: \<open>
 0 < units x3 \<Longrightarrow> valid_activation_tab\<^sub>l atab  \<Longrightarrow>
         inputs \<noteq> [] \<Longrightarrow>
         length (\<beta> x3) = units x3 \<Longrightarrow>
         length (\<omega> x3) = units x3 \<Longrightarrow>
         \<forall>r\<in>set (\<omega> x3). length r = length inputs \<Longrightarrow>
         atab (\<phi> x3) = Some y \<Longrightarrow>
         (length (y (map2 (+) (map ((\<lambda>vs'. \<Sum>(x, y)\<leftarrow>vs'. x * y) \<circ> zip inputs) (\<omega> x3)) (\<beta> x3)))) = units x3
\<close>
  using valid_activation_preserves_length[of atab "(\<phi> x3)" "y", symmetric] by simp

lemma pred_list_impl_aux': 
  assumes \<open>ls \<noteq> []\<close>
    and     layer_valid:  \<open>layers_consistent\<^sub>l \<lparr>layers = [], activation_tab = atab\<rparr> (length inputs) ls\<close> 
    and     activation_tab_valid: \<open>valid_activation_tab\<^sub>l atab\<close>  
  shows \<open>
    foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = [], activation_tab = atab\<rparr>) (Some inputs) ls =
    Some (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl \<lparr>layers = [], activation_tab = atab\<rparr>) inputs ls)
  \<close>
proof(insert assms(1) assms(2), induction "ls"  arbitrary:inputs rule:list_nonempty_induct)
  case (single x)
  then show ?case proof(cases x)
    case (In x1)
    then show ?thesis 
      using In single by force 
  next
    case (Out x2)
    then show ?thesis 
      using Out single.prems by force
  next
    case (Dense x3)
    then show ?thesis 
      using Dense single by force
  next
    case (Activation x4)
    then show ?thesis 
      using Activation single by force
  qed
next
  case (cons x xs)
  then show ?case proof(cases x)
    case (In x1)
    then show ?thesis 
      by (metis (no_types, lifting) cons.IH cons.prems foldl_Cons layer_consistent\<^sub>l.simps(1) layers_consistent\<^sub>l.simps(2) 
          layers_consistent\<^sub>l_layersN_const neural_network_seq_layers.select_convs(2) out_deg_layer.simps(1) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l.simps(1) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl.simps(1)) 
  next
    case (Out x2)
    then show ?thesis 
      apply(simp add:cons assms)
       using cons.prems
       cons.IH cons.prems layers_consistent\<^sub>l.simps(2) out_deg_layer.simps(2) 
        by simp
  next
    case (Dense x3)
    then show ?thesis 
      apply(thin_tac "x = Dense x3")
      using cons.prems apply(clarsimp simp add:Dense)
      apply(subst cons.IH, simp_all)
      apply(insert assms(3))
      apply(subst aux_length, simp_all)  
      unfolding valid_activation_tab\<^sub>l_def ran_def by auto
  next
    case (Activation x4)
    then show ?thesis 
      apply(simp add:cons assms)
      using cons.prems assms(3) cons.IH cons.prems layers_consistent\<^sub>l.simps(2) 
            layers_consistent\<^sub>l_layersN_const neural_network_seq_layers.select_convs(2) out_deg_layer.simps(3) 
            valid_activation_preserves_length 
      by (smt (verit, del_insts) layer_consistent\<^sub>l.simps(3) neq0_conv option.sel option.simps(5)) 
  qed
qed

lemma pred_list_impl_aux:
  assumes layer_valid:  \<open>layers_consistent\<^sub>l \<lparr>layers = ls, activation_tab = atab\<rparr> (length inputs) ls\<close> 
    and     activation_tab_valid: \<open>valid_activation_tab\<^sub>l atab\<close>  
  shows \<open>
    foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = ls, activation_tab = atab\<rparr>) (Some inputs) ls =
    Some (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl \<lparr>layers = ls, activation_tab = atab\<rparr>) inputs ls)
  \<close>
proof(cases ls)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then show ?thesis 
    using pred_list_impl_aux' assms layers_consistent\<^sub>l_activation_tab_const list.discI 
      neural_network_seq_layers.select_convs(2) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_activation_tab_const
    by (metis predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_activation_tab_const predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl_activation_tab_const) 
qed


lemma predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_code [code]:
  assumes \<open>in_deg_NN N = length inputs\<close>
  shows \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N inputs = Some (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_impl N inputs)\<close>
proof(cases N)
  case (fields ls atab)
  then show ?thesis 
    unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_impl_def
    using assms apply(simp,subst pred_list_impl_aux)
    using layer_valid apply force
    using activation_tab_valid apply force
    by simp
qed

lemma predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_code' [code]:
  assumes \<open>in_deg_NN N = length inputs\<close>
  shows \<open>the (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l N inputs) = predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_impl N inputs\<close>
  by (simp add: assms predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_code)


end

ML\<open>
  val layer_config_list =  {
         InC    = @{const "NN_Layers.layer.In"(\<open>real list\<close>, \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>, \<open>real list list\<close>)},
         OutC   = @{const "NN_Layers.layer.Out"(\<open>real list\<close>, \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>, \<open>real list list\<close>)},
         DenseC = @{const "NN_Layers.layer.Dense"(\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>,\<open>real list\<close>, \<open>real list list\<close>)},
         InOutRecordC = @{const "NN_Layers.InOutRecord.InOutRecord_ext"(\<open>(activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i, (real list,real list list, unit)LayerRecord_ext) ActivationRecord_ext\<close>)},
         LayerRecordC = @{const "LayerRecord_ext"(\<open>real list\<close>, \<open>real list list\<close>, \<open>unit\<close>)},
         ActivationRecordC = @{const "ActivationRecord_ext" (\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>,\<open>(real list, real list list, unit) LayerRecord_ext\<close>)},
         biasT_conv = (fn x => x),
         weightsT_conv = (fn x => fn _ => x),
         ltype =  @{typ \<open>(real list, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i, real list list) layer\<close>},
         activation_term = Activation_Term.MultiList,
         layersT = @{typ \<open> ((real list, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i, real list list ) layer) list\<close>},
         phiT    = @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real list \<Rightarrow> real list) option\<close>},   
         layer_extC =  @{const \<open>NN_Layers.neural_network_seq_layers.neural_network_seq_layers_ext\<close> (\<open>real list\<close>,      \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>, \<open>real list list\<close>,  \<open>unit\<close>)},
         layer_def = @{thm neural_network_sequential_layers\<^sub>l_def},
         valid_activation_tab = @{thm valid_activation_tab\<^sub>l_def},
         locale_name = "neural_network_sequential_layers\<^sub>l"
  }:Convert_TensorFlow_Seq_Layer.layer_config
  val _ = Theory.setup
           (Convert_TensorFlow_Symtab.add_encoding("seq_layer_list", 
                    Convert_TensorFlow_Seq_Layer.def_seq_layer_nn layer_config_list))
\<close>
end
