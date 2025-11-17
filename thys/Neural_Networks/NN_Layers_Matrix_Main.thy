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


subsection\<open>Neural Network as Sequential Layers using Vector Spaces (\thy)\<close>

theory
  NN_Layers_Matrix_Main
  imports
    NN_Lipschitz_Continuous
    NN_Layers
    Matrix_Utils
    Properties_Matrix
begin


text\<open>\label{sec:matrix}
  In this theory, we model feed-forward neural networks as ``computational layers'' following 
  the structure of TensorFlow~\<^cite>\<open>"abadi.ea:tensorflow:2015"\<close> closely.
\<close>



definition \<open>valid_activation_tab\<^sub>m tab = (\<forall> f \<in> ran tab. \<forall> xs. dim_vec xs = dim_vec (f xs))\<close>

lemma valid_activation_preserves_dim: 
  assumes \<open>valid_activation_tab\<^sub>m t\<close>
  assumes \<open>t n = Some f\<close>
  shows \<open>dim_vec xs = dim_vec (f xs)\<close>
  using assms unfolding valid_activation_tab\<^sub>m_def
  using ranI by metis 


fun layer_consistent\<^sub>m :: "('a vec, 'b, 'c mat) neural_network_seq_layers \<Rightarrow> nat \<Rightarrow> ('a vec, 'b, 'c mat) layer \<Rightarrow> bool" 
  where
    \<open>layer_consistent\<^sub>m _  nc  (In l) = (0 < units l \<and>  nc = units l)\<close>
  | \<open>layer_consistent\<^sub>m _ nc (Out l) = (0 < units l \<and> nc = units l)\<close>
  | \<open>layer_consistent\<^sub>m N nc (Activation l) = ( (0 < units l \<and> nc = units l)
                                            \<and> ( ((activation_tab N) (\<phi> l)) \<noteq> None  ))\<close>
  | \<open>layer_consistent\<^sub>m N nc (Dense l) = (0 < units l \<and> 0 < nc 
                                     \<and> dim_vec (\<beta> l) = units l 
                                     \<and> dim_col (\<omega> l) = units l
                                     \<and> dim_row (\<omega> l) = nc
                                     \<and> ( ((activation_tab N) (\<phi> l)) \<noteq> None  ))\<close>

fun layers_consistent\<^sub>m where
  \<open>layers_consistent\<^sub>m  N _ [] = True\<close>
|\<open>layers_consistent\<^sub>m  N w (l#ls) = ((layer_consistent\<^sub>m N w l) \<and> (layers_consistent\<^sub>m N (out_deg_layer l)  ls))\<close>

lemma layer_consistent\<^sub>m_activation_tab_const: 
  \<open>layer_consistent\<^sub>m N nc l = layer_consistent\<^sub>m \<lparr>layers = ls, activation_tab = activation_tab N\<rparr> nc l\<close>
  by(cases l, simp_all) 

lemma layers_consistent\<^sub>m_activation_tab_const: 
  \<open>layers_consistent\<^sub>m N nc ls = layers_consistent\<^sub>m \<lparr>layers = ls', activation_tab = activation_tab N\<rparr> nc ls\<close>
proof(induction ls arbitrary: nc)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  then show ?case 
    by(simp add: layer_consistent\<^sub>m_activation_tab_const[symmetric])
qed

lemma layers_consistent\<^sub>mAll: 
  assumes \<open>layers_consistent\<^sub>m N inputs (layers N)\<close>
  shows \<open>\<forall> l \<in> set (layers N). \<exists> n . layer_consistent\<^sub>m N n l\<close>
proof(cases N)
  case (fields layers activation_tab) note i = this
  then show ?thesis 
    apply(insert assms, simp add: i, safe)
    apply(thin_tac "N = \<lparr>layers = layers, activation_tab = activation_tab\<rparr>")
    apply(subst layer_consistent\<^sub>m_activation_tab_const[of _ _ _ "[]"])
    apply(induction "layers" arbitrary:inputs activation_tab)
    apply(simp)
    using layers_consistent\<^sub>m_activation_tab_const layer_consistent\<^sub>m_activation_tab_const[of _ _ _ "[]"] 
    apply(clarsimp)[1] 
    using layer_consistent\<^sub>m_activation_tab_const by fastforce
qed


lemma layers_consistent\<^sub>mAll': 
  assumes \<open>layers_consistent\<^sub>m N (in_deg_NN N) (layers N)\<close>
  shows \<open>\<forall> l \<in> set (layers N). \<exists> n . layer_consistent\<^sub>m N n l\<close>
  using assms layers_consistent\<^sub>mAll by blast

locale neural_network_sequential_layers\<^sub>m = 
  fixes N::\<open>('a::comm_ring Matrix.vec, 'b, 'a Matrix.mat) neural_network_seq_layers\<close> 
  assumes head_is_In:  \<open>isIn (hd (layers N))\<close>
    and     last_is_Out: \<open>isOut (last (layers N))\<close>
    and     layer_internal: \<open>list_all isInternal  ((tl o butlast) (layers N))\<close>
    and     activation_tab_valid: \<open>valid_activation_tab\<^sub>m (activation_tab N)\<close>  
    and     layer_valid:  \<open>layers_consistent\<^sub>m N (in_deg_NN N) (layers N)\<close> 
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


fun predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m::\<open>('a::comm_ring Matrix.vec, 'b, 'a Matrix.mat) neural_network_seq_layers \<Rightarrow> ('a Matrix.vec) option \<Rightarrow> ('a Matrix.vec, 'b, 'a Matrix.mat) layer \<Rightarrow> ('a Matrix.vec) option\<close> where
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (In l) = (if layer_consistent\<^sub>m N (dim_vec vs) (In l) then Some vs else None) \<close>
| \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (Out l) = (if layer_consistent\<^sub>m N (dim_vec vs) (Out l) then Some vs else None) \<close>
| \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (Dense pl) = (if layer_consistent\<^sub>m N (dim_vec vs) (Dense pl) then
                                             (case activation_tab N (\<phi> pl) of
                                               None \<Rightarrow> None
                                             | Some f \<Rightarrow> Some (f ((vs \<^sub>v*  \<omega> pl) + \<beta> pl) )
                                            ) else None )\<close>
| \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (Activation pl) = (if layer_consistent\<^sub>m N (dim_vec vs) (Activation pl) then
                                                 (case activation_tab N (\<phi> pl) of
                                                   None \<Rightarrow> None
                                                 | Some f \<Rightarrow> Some (f vs)
                                               ) else None )\<close>
| \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m _ None _ =  None \<close>

fun  
  predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl ::\<open>('a::{comm_ring} Matrix.vec, 'b, 'a Matrix.mat) neural_network_seq_layers \<Rightarrow> 'a Matrix.vec \<Rightarrow> ('a Matrix.vec, 'b, 'a Matrix.mat) layer \<Rightarrow> 'a Matrix.vec\<close>  
  where
    \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl N vs (In l)  = vs\<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl N vs (Out l) = vs\<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl N vs (Dense pl) = ((the (activation_tab N (\<phi> pl))) ((vs \<^sub>v*  \<omega> pl) + \<beta> pl))\<close>
  | \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl N vs (Activation pl) = ( the (activation_tab N (\<phi> pl)) vs)\<close>


lemma predict_layer_Some:
  assumes \<open>(layer_consistent\<^sub>m N (dim_vec xs) l)\<close> 
  shows \<open>(predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some xs) l \<noteq> None) \<close>  
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

definition \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N inputs = foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N) (Some inputs) (layers N)\<close>
definition \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m_impl N inputs = foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl N) inputs (layers N)\<close>

definition \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' N inputs = map_option list_of_vec (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N (vec_of_list inputs))\<close>

lemma predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl_activation_tab_const: \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl N = predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl \<lparr>layers = l, activation_tab = activation_tab N\<rparr>\<close>
  apply(rule ext)+
  using neural_network_seq_layers.select_convs predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl.elims predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl.simps
  by (smt (verit))


lemma layers_consistent\<^sub>m_layersN_const: 
  \<open>layers_consistent\<^sub>m N = layers_consistent\<^sub>m \<lparr>layers = ls', activation_tab = activation_tab N\<rparr>\<close>
  using layers_consistent\<^sub>m_activation_tab_const by blast 


lemma predit\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl_eq:
  assumes \<open>layer_consistent\<^sub>m N (dim_vec inputs) l\<close>
  shows   \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some inputs) l = Some (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl N inputs l)\<close>
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

lemma valid_activation_preserves_length: 
  assumes \<open>valid_activation_tab\<^sub>m t\<close>
  assumes \<open>t n = Some f\<close>
  shows \<open>dim_vec xs = dim_vec (f xs)\<close>
  using assms unfolding valid_activation_tab\<^sub>m_def
  by (simp add: ranI) 


lemma fold_predict_m_strict: \<open>(foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N) None ls) = None\<close>
  by(induction "ls", simp_all)

lemmas [nn_layer] = predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m.simps predict_layer_Some fold_predict_m_strict

lemma predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_activation_tab: assumes "activation_tab N = activation_tab N'" shows
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N x xs = predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N' x xs\<close>
proof(cases xs)
  case (In x1)
  then show ?thesis 
    by (metis layer_consistent\<^sub>m.simps(1) option.collapse predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m.simps(1) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m.simps(5)) 
next
  case (Out x2)
  then show ?thesis 
    by (metis layer_consistent\<^sub>m.simps(2) option.exhaust predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m.simps(2) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m.simps(5)) 
next
  case (Dense x3)
  then show ?thesis proof(cases x)
    case None
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis using Dense assms by force  
  qed 
next
  case (Activation x4)
  then show ?thesis proof(cases x)
    case None
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis using Activation assms by force  
  qed 
qed

lemma predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_activation_tab_const: \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N = predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m \<lparr>layers = l, activation_tab = activation_tab N\<rparr>\<close>
  apply(rule ext)+
  by (metis neural_network_seq_layers.select_convs(2) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_activation_tab) 

context neural_network_sequential_layers\<^sub>m begin 
lemma img_None_1: assumes \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N xs) \<noteq> None)\<close> shows \<open>(dim_vec xs = (in_deg_NN N))\<close>
proof - 
  have \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N xs) \<noteq> None) \<longrightarrow> (dim_vec xs = (in_deg_NN N))\<close>
  proof(cases N)
    case (fields layers' activation_tab') note i = this
    then show ?thesis 
      unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def
      using i layers_nonempty
    proof(induction layers')
      case Nil
      then show ?case by simp
    next
      case (Cons a layers')
      then show ?case proof(cases a)
        case (In x1)
        then show ?thesis using Cons 
          by (simp add: fold_predict_m_strict in_deg_NN_def) 
      next
        case (Out x2)
        then show ?thesis using Cons 
          by (simp add: fold_predict_m_strict in_deg_NN_def) 
      next
        case (Dense x3)
        then show ?thesis using Cons neural_network_sequential_layers\<^sub>m_axioms i
          apply(simp add: fold_predict_m_strict in_deg_NN_def)
          using Cons by (metis isIn.simps(3) list.sel(1) neural_network_seq_layers.select_convs(1) 
              neural_network_sequential_layers\<^sub>m.head_is_In) 
      next
        case (Activation x4)
        then show ?thesis using Cons neural_network_sequential_layers\<^sub>m_axioms i
          by(simp add: fold_predict_m_strict in_deg_NN_def)
      qed
    qed
  qed
  then show ?thesis using assms by simp 
qed

lemma img_None_2': 
  assumes  a0: \<open>layers' \<noteq> [] \<close> 
    and a4: \<open>valid_activation_tab\<^sub>m activation_tab'\<close>
    and a1:  \<open>layers_consistent\<^sub>m \<lparr>layers = [], activation_tab=activation_tab' \<rparr> (dim_vec xs) layers'\<close> 
  shows \<open>foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m \<lparr>layers = [], activation_tab = activation_tab'\<rparr>) (Some xs) layers' \<noteq> None\<close>
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
      using single by(force)
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
    then show ?thesis using cons by force 
  next
    case (Out x2)
    then show ?thesis using cons by force 
  next
    case (Dense x3)
    then show ?thesis 
      using cons assms apply(clarsimp)[1]
      apply(subst cons.IH[simplified], simp_all)
      using valid_activation_preserves_dim by force 
  next
    case (Activation x4)
    then show ?thesis 
      using cons assms apply(clarsimp)[1]
      apply(subst cons.IH[simplified], simp_all) 
      by (metis valid_activation_preserves_dim) 
  qed
qed

lemma img_None_2: 
  assumes \<open>dim_vec xs = in_deg_NN N\<close> 
  shows \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N xs) \<noteq> None)\<close>
proof(cases N)
  case (fields layers activation_tab)
  then show ?thesis 
    using assms layer_valid apply(simp)
    unfolding neural_network_sequential_layers\<^sub>m_def  predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def
    apply(subst         predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_activation_tab_const[of _ "[]"]) 
    apply(simp)
    apply(subst img_None_2'[of layers activation_tab xs, simplified], simp_all)
    using layers_nonempty apply force 
    using activation_tab_valid apply fastforce 
    using assms layer_valid unfolding in_deg_NN_def apply(simp) 
    using layers_consistent\<^sub>m_activation_tab_const by fastforce 
qed

lemma img_None: \<open>((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N xs) \<noteq> None) = (dim_vec xs = in_deg_NN N)\<close>
  using img_None_1 img_None_2 by blast 

lemma img_Some: \<open>(\<exists> y. (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N xs) = Some y) = (dim_vec xs = in_deg_NN N)\<close>
  using img_None by simp 

lemma img_deg: \<open>(\<exists> y. ((predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N xs) = Some y) \<longrightarrow> (dim_vec y = out_deg_NN N))\<close>
proof(cases N)
  case (fields layers' activation_tab')
  then show ?thesis 
    unfolding fields predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def
    using fields layers_nonempty
  proof(induction layers' arbitrary: xs rule:rev_induct)
    case Nil
    then show ?case by simp
  next
    case (snoc a layers')
    then show ?case proof(cases a)
      case (In x1)
      then show ?thesis using snoc
        using dim_vec by blast
    next
      case (Out x2)
      then show ?thesis using snoc
        apply (simp add: fold_predict_m_strict out_deg_NN_def neural_network_sequential_layers\<^sub>m_def) 
        using dim_vec_first by blast 
    next
      case (Dense x3)
      then show ?thesis using Cons neural_network_sequential_layers\<^sub>m_axioms
        apply(simp add: fold_predict_m_strict in_deg_NN_def)
        using snoc 
        by (simp add: neural_network_sequential_layers\<^sub>m_def)
    next
      case (Activation x4)
      then show ?thesis using Cons neural_network_sequential_layers\<^sub>m_axioms
        apply(simp add: fold_predict_m_strict in_deg_NN_def)
        using snoc
        using snoc 
        by (simp add: neural_network_sequential_layers\<^sub>m_def)
    qed
  qed
qed

lemma aux_length: " 0 < units x3 \<Longrightarrow>
         0 < dim_vec inputs \<Longrightarrow>
         dim_vec (\<beta> x3) = units x3 \<Longrightarrow>
         dim_col (\<omega> x3) = units x3 \<Longrightarrow>
         dim_row (\<omega> x3) = dim_vec inputs \<Longrightarrow>
         layers_consistent\<^sub>m \<lparr>layers = [], activation_tab = atab\<rparr> (units x3) xs \<Longrightarrow>
         atab (\<phi> x3) = Some y \<Longrightarrow> valid_activation_tab\<^sub>m atab \<Longrightarrow> layers_consistent\<^sub>m \<lparr>layers = [], activation_tab = atab\<rparr> (dim_vec (y (inputs \<^sub>v* \<omega> x3 + \<beta> x3))) xs"
  using valid_activation_preserves_length[of atab "(\<phi> x3)" "y", symmetric] by simp

lemma pred_mat_impl_aux': 
  assumes \<open>ls \<noteq> []\<close>
    and     layer_valid:  \<open>layers_consistent\<^sub>m \<lparr>layers = [], activation_tab = atab\<rparr> (dim_vec inputs) ls\<close> 
    and     activation_tab_valid: \<open>valid_activation_tab\<^sub>m atab\<close>  
  shows \<open>
    foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m \<lparr>layers = [], activation_tab = atab\<rparr>) (Some inputs) ls =
    Some (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl \<lparr>layers = [], activation_tab = atab\<rparr>) inputs ls)
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
      by (metis (no_types, lifting) cons.IH cons.prems foldl_Cons layer_consistent\<^sub>m.simps(1) layers_consistent\<^sub>m.simps(2) 
          layers_consistent\<^sub>m_layersN_const neural_network_seq_layers.select_convs(2) out_deg_layer.simps(1) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m.simps(1) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl.simps(1)) 
  next
    case (Out x2)
    then show ?thesis 
      apply(clarsimp simp add:cons assms)[1] 
     using cons.IH cons.prems layers_consistent\<^sub>m.simps(2) out_deg_layer.simps(2) 
       cons.prems cons(2,3) 
     by fastforce 
  next
    case (Dense x3)
    then show ?thesis 
      apply(thin_tac "x = Dense x3")
      using cons.prems apply(clarsimp simp add:Dense)[1]
      apply(subst cons.IH, simp_all)
      apply(insert assms(3))
      by(subst aux_length, simp_all)  
  next
    case (Activation x4)
    then show ?thesis 
      apply(clarsimp simp add:cons assms)[1]
      using assms(3) cons.IH cons.prems layers_consistent\<^sub>m.simps(2) 
            layers_consistent\<^sub>m_layersN_const neural_network_seq_layers.select_convs(2) out_deg_layer.simps(3) 
            valid_activation_preserves_length 
        by (smt (z3) layer_consistent\<^sub>m.simps(3) neq0_conv option.case_eq_if option.sel) 
     
  qed
qed


lemma pred_mat_impl_aux:
  assumes layer_valid:  \<open>layers_consistent\<^sub>m \<lparr>layers = ls, activation_tab = atab\<rparr> (dim_vec inputs) ls\<close> 
    and     activation_tab_valid: \<open>valid_activation_tab\<^sub>m atab\<close>  
  shows \<open>
    foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m \<lparr>layers = ls, activation_tab = atab\<rparr>) (Some inputs) ls =
    Some (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_impl \<lparr>layers = ls, activation_tab = atab\<rparr>) inputs ls)
  \<close>
proof(cases ls)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then show ?thesis 
    using pred_mat_impl_aux' assms layers_consistent\<^sub>m_activation_tab_const list.discI 
      neural_network_seq_layers.select_convs(2) predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_activation_tab_const
    by (metis predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_activation_tab_const predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l_impl_activation_tab_const) 
qed

lemma predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m_code [code]:
  assumes \<open>in_deg_NN N = dim_vec inputs\<close>
  shows \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N inputs = Some (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m_impl N inputs)\<close>
proof(cases N)
  case (fields ls atab)
  then show ?thesis 
    unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m_impl_def
    using assms apply(simp,subst pred_mat_impl_aux)
    using layer_valid apply force
    using activation_tab_valid apply force
    by simp
qed

lemma predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m_code' [code]:
  assumes \<open>in_deg_NN N = dim_vec inputs\<close>
  shows \<open>the (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N inputs) = predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m_impl N inputs\<close>
  by (simp add: assms predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m_code)

end 


ML\<open>
  val layer_config_matrix =  {
         InC    = @{const "NN_Layers.layer.In"(\<open>real Matrix.vec\<close>, \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>, \<open>real Matrix.mat\<close>)},
         OutC   = @{const "NN_Layers.layer.Out"(\<open>real Matrix.vec\<close>, \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>, \<open>real Matrix.mat\<close>)},
         DenseC = @{const "NN_Layers.layer.Dense"(\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>,\<open>real Matrix.vec\<close>, \<open>real Matrix.mat\<close>)},
         InOutRecordC = @{const "NN_Layers.InOutRecord.InOutRecord_ext"(\<open>(activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i, (real Matrix.vec, real Matrix.mat, unit)LayerRecord_ext) ActivationRecord_ext\<close>)},
         LayerRecordC = @{const "LayerRecord_ext"(\<open>real Matrix.vec\<close>, \<open>real Matrix.mat\<close>, \<open>unit\<close>)},
         ActivationRecordC = @{const "ActivationRecord_ext" (\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>,\<open>(real Matrix.vec, real Matrix.mat, unit) LayerRecord_ext\<close>)},
         biasT_conv = (fn x => @{const "vec_of_list"(\<open>real\<close>)} $ x),
         weightsT_conv = (fn x => fn dim => @{const "mat_of_cols_list"(\<open>real\<close>)} $ HOLogic.mk_number \<^typ>\<open>nat\<close> dim $ x),
         ltype = @{typ \<open>(real Matrix.vec, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i, real Matrix.mat) layer\<close>},
         activation_term = Activation_Term.MultiMatrix,
         layersT = @{typ \<open> ((real Matrix.vec, activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i, real Matrix.mat) layer) list\<close>},
         phiT    = @{typ \<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i \<Rightarrow> (real Matrix.vec \<Rightarrow> real Matrix.vec) option\<close>}, 
         layer_extC = @{const \<open>NN_Layers.neural_network_seq_layers.neural_network_seq_layers_ext\<close> (\<open>real Matrix.vec\<close>,\<open>activation\<^sub>m\<^sub>u\<^sub>l\<^sub>t\<^sub>i\<close>, \<open>real Matrix.mat\<close>, \<open>unit\<close>)},
         layer_def = @{thm neural_network_sequential_layers\<^sub>m_def},
         valid_activation_tab = @{thm valid_activation_tab\<^sub>m_def},
         locale_name = "neural_network_sequential_layers\<^sub>m" 
  }:Convert_TensorFlow_Seq_Layer.layer_config
  val _ = Theory.setup
           (Convert_TensorFlow_Symtab.add_encoding("seq_layer_matrix", 
                    Convert_TensorFlow_Seq_Layer.def_seq_layer_nn layer_config_matrix))
\<close>

end
