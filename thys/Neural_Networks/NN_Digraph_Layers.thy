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

subsection\<open>Digraphs as Layers (\thy)\<close>	
theory
  NN_Digraph_Layers
  imports   
  NN_Digraph
  "HOL-Combinatorics.Permutations" 
begin

definition layer_equiv :: "('a list \<Rightarrow> 'b list) \<Rightarrow> ('a list \<Rightarrow> 'b list) \<Rightarrow> bool" ("_ \<equiv>\<^sub>l _")
  where 
\<open>layer_equiv f g = (\<exists> p p'. \<forall> xs. f xs = permute_list p' (f (permute_list p xs)))\<close>

lemma mset_eq_layer_equiv:
  assumes \<open>mset xs = mset ys\<close>
      and \<open>mset (f xs) = mset (g ys)\<close>
    shows \<open>f \<equiv>\<^sub>l g\<close>
  unfolding layer_equiv_def using assms 
  by (metis permute_list_id) 

 

fun output_neuron where
   \<open>output_neuron (In nid) = False\<close>
 | \<open>output_neuron (Out nid) = True\<close>
 | \<open>output_neuron (Neuron n) = False\<close>

fun input_neuron where
   \<open>input_neuron (In nid) = True\<close>
 | \<open>input_neuron (Out nid) = False\<close>
 | \<open>input_neuron (Neuron n) = False\<close>

fun hidden_neuron where
   \<open>hidden_neuron (In nid) = False\<close>
 | \<open>hidden_neuron (Out nid) = False\<close>
 | \<open>hidden_neuron (Neuron n) = True\<close>

subsubsection \<open>Defining layer types as lists of edges\<close>

text \<open>This subsection details definitions which allow for the easy creation of common layer types.
The Activation and Dense layer types map to the layer types used by TensorFlow 
(see  \<^url>\<open>https://www.tensorflow.org/api_docs/python/tf/keras/layers\<close>) \<close>

paragraph \<open>Edge construction functions\<close>

definition mk_edge :: \<open>('a::{one}, 'b, 'c) neural_network \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> id \<Rightarrow> id \<Rightarrow> ('a, 'b) edge\<close> 
  where
 \<open>mk_edge N \<omega>' \<phi>' \<alpha>' \<beta>' id' nid = \<lparr> \<omega> = \<omega>', 
                                    tl =  (the_elem {n . n \<in> neurons N \<and> uid n = id'}), 
                                    hd = Neuron \<lparr> \<phi> = \<phi>', \<alpha> = \<alpha>', \<beta> = \<beta>', uid = nid \<rparr> \<rparr> \<close>

definition mk_out_edge :: \<open>('a::{one}, 'b, 'c) neural_network \<Rightarrow> id \<Rightarrow> id \<Rightarrow> ('a, 'b) edge\<close> 
  where
 \<open>mk_out_edge N id' nid' = \<lparr> \<omega> = 1, 
                             tl = (the_elem {n . n \<in> neurons N \<and> uid n = id'}),  
                             hd = Out nid' \<rparr>\<close>

definition mk_new_ids :: \<open>('a::{one}, 'b, 'c) neural_network  \<Rightarrow> nat list \<close>  
  where
 \<open>mk_new_ids N = upt (Max(uids (graph N)) + 1) 
                     (Max(uids (graph N)) + card (output_layer_ids N) + 1)\<close>

text \<open>@{const "mk_new_ids"} makes a list of new ids corresponding to the size of the current last 
layer in a given network and the current maximum id in the network. This is used in the 
activation and out functions in order to generate the new neurons in the edges. In order to help 
validate that the @{const "mk_new_ids"} returns the correct sized list and that the ids are unique 
in the network the following lemmas are needed to simplify this.\<close>

lemma new_id_len: \<open>length(mk_new_ids N) = length(sorted_list_of_set(output_layer_ids N))\<close>
  by (simp add: mk_new_ids_def)

lemma new_id_len_card: \<open>length(mk_new_ids N) = card(output_layer_ids N)\<close>
  by (simp add: mk_new_ids_def)

lemma new_id_distinct: \<open>distinct(mk_new_ids N)\<close>
  by (metis distinct_upt mk_new_ids_def)

lemma new_id_greater:
  assumes \<open>card (output_layer_ids N) > 0\<close>
  shows \<open>Min(set(mk_new_ids N)) > Max(uids (graph N))\<close>
  using assms
  by (simp add: mk_new_ids_def)

lemma new_id_sorted: 
  shows \<open>sorted (mk_new_ids N)\<close>
  by (metis mk_new_ids_def sorted_upt)

lemma new_ids_unique:
  assumes new_ids_finite:   "finite (set(mk_new_ids N))"
  and current_ids_finite:   "finite (uids (graph N))"
  and MinMax:     "Max (uids (graph N)) < Min (set(mk_new_ids N))"
  shows "uids (graph N) \<inter> set(mk_new_ids N) = {}"
  using assms
  by (metis Min_gr_iff  disjnt_def disjnt_ge_max disjoint_iff_not_equal equals0D) 

text\<open>Or by rewriting disjointness:\<close>

lemma new_ids_unique': 
  assumes new_ids_finite:   "finite (set(mk_new_ids N))"
  and current_ids_finite:   "finite (uids (graph N))"
  and MinMax:     "Max (uids (graph N)) < Min (set(mk_new_ids N))"
  shows "\<forall> x \<in> set(mk_new_ids N). x \<notin> uids (graph N)"
  using assms
  by (meson Max_ge Min_le linorder_not_le order_trans)

paragraph \<open>Template layer types as list of edges\<close>

definition dense :: \<open>('a::{one}, 'b, 'c) neural_network \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b) edge list\<close> 
  where
 \<open>dense N n \<omega>' \<phi>' \<alpha>' \<beta>' = (if length \<omega>' = n then
                            (let nids = upt (Max(uids (graph N)) + 1) (Max(uids (graph N)) + n + 1)
                             in concat(map (\<lambda> w . (concat(map 
                                           (\<lambda> b . map (\<lambda> a . mk_edge N w \<phi>' \<alpha>' \<beta>' a b ) 
                                           (sorted_list_of_set(output_layer_ids N))) nids))) \<omega>')) 
                            else [])\<close>
text \<open>In @{const "dense"} we also take a list of weights which we want our dense layer to be 
initialised with (requiring another map operator).\<close>

definition out :: \<open>('a::{one}, 'b, 'c) neural_network \<Rightarrow> ('a,'b) edge list\<close> 
  where
 \<open>out N = (let nids = mk_new_ids N;
               nedges = map (\<lambda> a . mk_out_edge N (fst a) (snd a)) 
                            (zip (sorted_list_of_set(output_layer_ids N)) nids)
            in (if distinct nedges then nedges else []))\<close>

definition activation :: \<open>('a::{one}, 'b, 'c) neural_network \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b) edge list\<close> 
  where
 \<open>activation N \<phi>' \<alpha>' \<beta>' = (let nids = mk_new_ids N;
                               nedges = map (\<lambda> a . mk_edge N 1 \<phi>' \<alpha>' \<beta>' (fst a) (snd a))
                                            (zip (sorted_list_of_set(output_layer_ids N)) nids)
                            in (if distinct nedges then nedges else []))\<close>

text \<open>here we call @{const "mk_edge"} with the weight @{term "\<omega>"} set to @{term "1"} as we do not 
    want to change the output of the previous layer (we are simply applying the activation function)\<close>

definition \<open>add_edges N edge_list = foldr (\<lambda> a b. add_nn_edge b a) edge_list (graph N)\<close>
definition \<open>add_out N = add_edges N (out N) \<close>
definition \<open>add_dense N n \<omega>' \<phi>' \<alpha>' \<beta>' = add_edges N (dense N n \<omega>' \<phi>' \<alpha>' \<beta>')\<close>
definition \<open>add_activation N \<phi>' \<alpha>' \<beta>' = add_edges N (activation N \<phi>' \<alpha>' \<beta>')\<close>

text \<open>definitions @{const "add_edges"}, @{const "add_out"}, @{const "add_dense"} and
 @{const "add_activation"} allow for easy addition of TensorFlow layer types to an existing Neural 
Network.\<close>
                                                             
subsubsection \<open>Defining Layers in the Digraph Model\<close>

fun layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h::\<open>nat \<Rightarrow> ('a::{zero,linorder,numeral}, 'b, 'c) neural_network 
                    \<Rightarrow> ('a, 'b) edge \<Rightarrow> ('a \<times>  error)\<close>
  where 
  \<open>layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h _ N (\<lparr>\<omega>=_,  tl= _, hd=In _\<rparr>)       = (0, ERROR)\<close>
| \<open>layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h _ N (\<lparr>\<omega>=_,  tl=Out _   , hd=_ \<rparr>)   = (0, ERROR)\<close>
| \<open>layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h _ N (\<lparr>\<omega>=_, tl=In uid\<^sub>i\<^sub>n , hd=_ \<rparr>)   = (0, OK)\<close>
| \<open>layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h n N e = (if 0 < n then  
                          (let 
                              tl'   = (case (tl e) of (Neuron t) \<Rightarrow> t);
                              E'    = incoming_arcs N (Neuron.uid tl');
                              lvals = ((\<lambda> e'. (case layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h (n-1) N e' of  
                                                    (_, ERROR) \<Rightarrow> ((0,0),  ERROR) 
                                                  | (v, OK)    \<Rightarrow> ((v+1 ,uid (tl e')), OK))) ` E')
                          in  
                          (Max ((\<lambda> a .fst(fst a )) ` {n. n \<in> lvals \<and> snd n = OK }) , OK))
                      else  (0, ERROR))\<close>

text \<open>Layers are defined as the path from the output node, this allows all dependencies to be 
calculated before prediction. In @{const "layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h" } the layer is calculated using the edges.\<close>

fun layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>n\<^sub>e\<^sub>u\<^sub>r\<^sub>o\<^sub>n :: \<open>nat \<Rightarrow> ('a::{zero,linorder,numeral}, 'b, 'c) neural_network 
                    \<Rightarrow> ('a, 'b) neuron \<Rightarrow> ('a \<times>  error)\<close> 
  where
  \<open>layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>n\<^sub>e\<^sub>u\<^sub>r\<^sub>o\<^sub>n _ N (In uid\<^sub>i\<^sub>n) = (0, OK)\<close>
| \<open>layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>n\<^sub>e\<^sub>u\<^sub>r\<^sub>o\<^sub>n n N (Out uid\<^sub>o\<^sub>u\<^sub>t) = (if 0 < n then 
                                         (let
                                            E' = tl ` (incoming_arcs N uid\<^sub>o\<^sub>u\<^sub>t);
                                            lvals = ((\<lambda> n' . (case layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>n\<^sub>e\<^sub>u\<^sub>r\<^sub>o\<^sub>n (n-1) N n' of
                                                           (_, ERROR) \<Rightarrow> ((0,0),  ERROR)
                                                         | (v, OK) \<Rightarrow> ((v+1, uid n'), OK))) ` E')
                                          in (Max ((\<lambda> a .fst(fst a )) ` {n. n \<in> lvals \<and> snd n = OK }) , OK))
                                       else (0, ERROR))\<close>
| \<open>layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>n\<^sub>e\<^sub>u\<^sub>r\<^sub>o\<^sub>n n N (Neuron a) = (if 0 < n then 
                                         (let
                                            E' = tl ` (incoming_arcs N (Neuron.uid a));
                                            lvals = ((\<lambda> n' . (case layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>n\<^sub>e\<^sub>u\<^sub>r\<^sub>o\<^sub>n (n-1) N n' of
                                                           (_, ERROR) \<Rightarrow> ((0,0),  ERROR)
                                                         | (v, OK) \<Rightarrow> ((v+1, uid n'), OK))) ` E')
                                          in (Max ((\<lambda> a .fst(fst a )) ` {n. n \<in> lvals \<and> snd n = OK }) , OK))
                                       else (0, ERROR))\<close>

text \<open> In @{const "layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>n\<^sub>e\<^sub>u\<^sub>r\<^sub>o\<^sub>n" } the layer is calculated using the neurons instead, this is
more intuitive as it is the neurons that are arranged in layers.\<close>

paragraph \<open>Defining the behaviour of layers \<close>

fun layers\<^sub>e\<^sub>d\<^sub>g\<^sub>e\<^sub>s :: \<open>'a \<Rightarrow> 'a \<Rightarrow> ('a::{zero,numeral,linorder}, 'b, 'c) neural_network 
                    \<Rightarrow> ('a, 'b) edge set\<close> where
   \<open>layers\<^sub>e\<^sub>d\<^sub>g\<^sub>e\<^sub>s l l' N = (let n\<^sub>a\<^sub>l\<^sub>l   = neurons N;
                             layer =  (\<lambda> n . ((layers\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>n\<^sub>e\<^sub>u\<^sub>r\<^sub>o\<^sub>n (card n\<^sub>a\<^sub>l\<^sub>l) N n), uid n)) ` n\<^sub>a\<^sub>l\<^sub>l;
                             n\<^sub>i\<^sub>n    = snd ` {n . n \<in> layer \<and> fst(fst n) = l};
                             n\<^sub>o\<^sub>u\<^sub>t   = snd ` {n . n \<in> layer \<and> fst(fst n) = l'}
                          in { e . e \<in> edges N \<and> uid (tl e) \<in> n\<^sub>i\<^sub>n \<and> uid (hd e) \<in> n\<^sub>o\<^sub>u\<^sub>t } )\<close>
text \<open>get all edges between layer n and n+1\<close>

subparagraph \<open>Predicates to distinguish different layer types\<close>

text \<open>The following for functions test whether sets of edges correspond to the correct type of 
connections for Dense, Activation, Input and Output layers.\<close>

definition isDense\<^sub>s :: \<open>('a, 'b) edge set \<Rightarrow> bool \<close> where
          \<open>isDense\<^sub>s e = ((\<forall> n' \<in>  tl ` e . \<forall> n'' \<in> hd ` e . \<exists> e' \<in> e . tl e' = n' \<and> hd e' = n''))\<close>

definition isActivation\<^sub>s :: \<open>('a, 'b) edge set \<Rightarrow> bool\<close>  where
          \<open>isActivation\<^sub>s e = ((\<forall> n' \<in>  tl ` e . \<exists>! e' \<in> e . tl e' = n') \<and> 
                              (\<forall> n'' \<in> hd ` e . \<exists>! e'' \<in> e . hd e'' = n''))\<close>

definition isInput\<^sub>s :: \<open>('a, 'b) edge set \<Rightarrow> bool\<close> where
          \<open>isInput\<^sub>s e = (isDense\<^sub>s e \<and> (\<forall> n \<in> hd ` e . input_neuron n))\<close>

definition isOutput\<^sub>s :: \<open>('a, 'b) edge set \<Rightarrow> bool\<close> where
          \<open>isOutput\<^sub>s e = (isActivation\<^sub>s e \<and> (\<forall> n''' \<in> hd ` e . output_neuron n'''))\<close>


text \<open>The following for functions test whether lists of edges correspond to the correct type of 
connections for Dense, Activation, Input and Output layers. 
We want these definitions over lists and sets in order to allow us to use whichever is more 
efficient in specific situations.\<close>

definition isDense\<^sub>l :: \<open>('a, 'b) edge list \<Rightarrow> bool\<close> where
          \<open>isDense\<^sub>l e = (let t = (map tl e); h = (map hd e) in 
                        (\<forall> n' \<in>  set t . \<forall> n'' \<in> set h . 
                         filter (\<lambda> e' . tl e' = n' \<and> hd e' = n'') e  \<noteq> [] ))\<close> 

definition isInput\<^sub>l :: \<open>('a, 'b) edge list \<Rightarrow> bool\<close> where
          \<open>isInput\<^sub>l e = (isDense\<^sub>l e  \<and> foldr (\<and>) (map input_neuron (map hd e)) True)\<close> 

definition isActivation\<^sub>l :: \<open>('a, 'b) edge list \<Rightarrow> bool\<close>  where
          \<open>isActivation\<^sub>l e = (let t = (map tl e); h = (map hd e) in 
                             distinct t \<and> distinct h \<and> length t = length h \<and> length e = length h \<and>
                             length t = length e )\<close>  

definition isOutput\<^sub>l :: \<open>('a, 'b) edge list \<Rightarrow> bool\<close> where
           \<open>isOutput\<^sub>l e = (isActivation\<^sub>l e \<and> foldr (\<and>) (map (output_neuron \<circ> hd) e) True)\<close> 

text\<open>Prove that the list and set definitions of our layers define the same behaviour, e.g. it does
not matter whether @{const "isActivation\<^sub>l"} or @{const "isActivation\<^sub>s"} is used, the same 
connections are ensured\<close>

lemma allOutput:
  shows \<open>foldr (\<and>) (map (output_neuron \<circ> hd) e) True =  (\<forall> n' \<in> hd ` set e . output_neuron n')\<close>
proof (induction "e")
  case Nil
  then show ?case by simp
next
  case (Cons a e)
  then show ?case by simp 
qed

lemma allInput:
  shows \<open>foldr (\<and>) (map (input_neuron \<circ> hd) e) True =  (\<forall> n' \<in> hd ` set e . input_neuron n')\<close>
proof (induction "e")
  case Nil
  then show ?case by simp
next
  case (Cons a e)
  then show ?case by simp
qed

lemma forAll:
  \<open>(\<forall> n'\<in> set (map tl e).\<forall> n''\<in> set(map hd e).filter(\<lambda>e'. tl e' = n' \<and> hd e' = n'') e \<noteq> []) =
   (\<forall> n'\<in> tl` set e. \<forall> n''\<in> hd ` set e . \<exists> e' \<in> set e . tl e' = n' \<and> hd e' = n'')\<close>
proof (induction "e")
  case Nil
  then show ?case by simp 
next
  case (Cons a e)
  then show ?case by (smt (verit, del_insts) empty_filter_conv list.set_map) 
qed

lemma isDense\<^sub>l_isDense\<^sub>s_equivalence: \<open>isDense\<^sub>l E = isDense\<^sub>s (set E)\<close>
  apply (safe)
  subgoal apply (simp add: isDense\<^sub>l_def isDense\<^sub>s_def)
    subgoal apply (metis (mono_tags, lifting) empty_filter_conv) done
    done
  subgoal apply (simp add: isDense\<^sub>l_def isDense\<^sub>s_def)
    subgoal apply (smt (verit, ccfv_threshold) empty_filter_conv) done
    done
  done

lemma isnput\<^sub>l_isInput\<^sub>s_equivalence: \<open>isInput\<^sub>l E = isInput\<^sub>s (set E)\<close>
  apply(safe)
  subgoal apply (simp add: isInput\<^sub>l_def isInput\<^sub>s_def)
    using allInput isDense\<^sub>l_isDense\<^sub>s_equivalence by auto
  subgoal apply (simp add: isInput\<^sub>l_def isInput\<^sub>s_def)
    using allInput isDense\<^sub>l_isDense\<^sub>s_equivalence by auto
  done

lemma isActivation\<^sub>l_isActivation\<^sub>s_equivalence: 
  assumes distinct: \<open>distinct E\<close>
  shows \<open>isActivation\<^sub>l E = isActivation\<^sub>s (set E)\<close>
  using assms
  apply(safe)
  subgoal apply(simp add: isActivation\<^sub>l_def isActivation\<^sub>s_def) 
    by (metis distinct_map inj_onD)
  subgoal apply(simp add: isActivation\<^sub>l_def isActivation\<^sub>s_def)
    using distinct_map inj_on_def by fastforce
  done

lemma isOutput\<^sub>l_isOutput\<^sub>s_equivalence:
  assumes distinct: \<open>distinct E\<close>
  shows \<open>isOutput\<^sub>l E = isOutput\<^sub>s (set E)\<close> 
  using assms
  apply (safe)
  subgoal 
    apply (simp add: isOutput\<^sub>l_def isOutput\<^sub>s_def)
    using allOutput isActivation\<^sub>l_isActivation\<^sub>s_equivalence by blast
  subgoal 
    apply (simp add: isOutput\<^sub>l_def isOutput\<^sub>s_def) 
    using allOutput isActivation\<^sub>l_isActivation\<^sub>s_equivalence by blast
  done

text \<open>We currently support the following 4 types of layers:\<close>

definition \<open>layers\<^sub>i\<^sub>n\<^sub>p\<^sub>u\<^sub>t l l' N = isInput\<^sub>s (layers\<^sub>e\<^sub>d\<^sub>g\<^sub>e\<^sub>s l l' N)\<close>
definition \<open>layers\<^sub>o\<^sub>u\<^sub>t\<^sub>p\<^sub>u\<^sub>t l l' N = isOutput\<^sub>s (layers\<^sub>e\<^sub>d\<^sub>g\<^sub>e\<^sub>s l l' N)\<close>
definition \<open>layers\<^sub>d\<^sub>e\<^sub>n\<^sub>s\<^sub>e l l' N = isDense\<^sub>s (layers\<^sub>e\<^sub>d\<^sub>g\<^sub>e\<^sub>s l l' N)\<close>
definition \<open>layers\<^sub>a\<^sub>c\<^sub>t\<^sub>i\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n l l' N = isActivation\<^sub>s (layers\<^sub>e\<^sub>d\<^sub>g\<^sub>e\<^sub>s l  l' N)\<close>
 

subsubsection \<open>Conversion of layer types\<close>

paragraph \<open>The following helper lemmas are needed to prove that tails are unique within the edge lists.\<close>

context neural_network_digraph begin

lemma "nn_pregraph (graph N)"
  by (meson neural_network_digraph_axioms neural_network_digraph_def nn_graph.axioms(1)) 

lemma uid_is_singleton: \<open>x \<in> NN_Digraph.uid ` (neurons N) 
   \<Longrightarrow> is_singleton {n \<in> neurons N. NN_Digraph.uid n = x}\<close>
  using neurons_def o_def nn_pregraph.id_vert_inj
  by (smt (verit, best) empty_iff image_iff inj_onD is_singletonI' 
      mem_Collect_eq neural_network_digraph_axioms neural_network_digraph_def nn_graph.id_vert_inj) 

lemma distinct_elem:
  assumes a1: \<open>distinct X \<close>
  and a2: \<open>set X \<subseteq> uid ` (neurons N) \<close>
shows \<open>distinct (map (\<lambda>x. the_elem {n \<in> neurons N. NN_Digraph.uid n = x}) X)\<close>
  by (smt (verit, best) a1 a2 distinct_map image_iff inj_on_def is_singleton_the_elem 
                        mem_Collect_eq subset_code(1) uid_is_singleton) 

lemma output_layer_ids_subset_neuron_ids: \<open>output_layer_ids N \<subseteq> uid ` (neurons N) \<close>
  unfolding image_def neurons_def output_layer_ids_def o_def output_layer_def output_verts_def
  by auto

end

paragraph \<open>Activation layer proofs\<close>

lemma distinct_activation_edges: \<open>distinct (activation N \<phi>' \<alpha>' \<beta>')\<close>
  apply (simp add: activation_def)
  by (smt (verit) distinct.simps(1))

lemma output_activation_layer_length_equal:
   assumes notEmptyNeurons: \<open>neurons N \<noteq> {}\<close> 
   and notEmptyActivationLayer: \<open>length(activation N \<phi>' \<alpha>' \<beta>' ) \<noteq> 0\<close>
   shows \<open>card(output_layer_ids N) = length(activation N \<phi>' \<alpha>' \<beta>')\<close>
   using assms
   apply (simp add: activation_def mk_new_ids_def mk_out_edge_def output_layer_ids_def)
   apply auto
   done

lemma new_ids_activation_layer_length_equal: 
  assumes notEmptyNeurons: \<open>neurons N \<noteq> {}\<close> 
  and notEmptyActivationLayer: \<open>length(activation N \<phi>' \<alpha>' \<beta>') \<noteq> 0\<close> 
  and notEmptyNewIds: \<open>length(mk_new_ids N) \<noteq> 0\<close>
  shows \<open>length(mk_new_ids N) = length(activation N \<phi>' \<alpha>' \<beta>')\<close>
  using assms 
  apply (simp add: out_def mk_new_ids_def)
  apply (metis assms(2) output_activation_layer_length_equal)
  done

lemma map_neuron_hd_id: 
  \<open>(map (\<lambda>x. Neuron \<lparr>\<phi> = \<phi>', \<alpha> = \<alpha>', \<beta> = \<beta>', uid = f x\<rparr>) X) =  
   (map (\<lambda>x. Neuron \<lparr>\<phi> = \<phi>', \<alpha> = \<alpha>', \<beta> = \<beta>', uid = x\<rparr>) (map f X))\<close>
  by simp 

lemma map_neuron_tl_id:
  \<open>(map (\<lambda>x. the_elem {n \<in> neurons N. NN_Digraph.uid n = f x}) X) = 
   (map (\<lambda>x. the_elem {n \<in> neurons N. NN_Digraph.uid n = x})(map f X))\<close>
  by simp


context nn_pregraph begin

lemma distinct_head_activation: \<open>distinct(map hd (activation N \<phi>' \<alpha>' \<beta>'))\<close>
  apply (simp add: activation_def Let_def mk_edge_def o_def) 
  apply (simp only: map_neuron_hd_id[of _ _ _ snd _] map_snd_zip new_id_len)
  using new_id_distinct
  apply (simp add: distinct_conv_nth)
  by auto

end 

context neural_network_digraph begin

lemma distinct_tail_activation: \<open>distinct(map tl (activation N \<phi>' \<alpha>' \<beta>'))\<close>
  apply (simp add: activation_def Let_def mk_edge_def o_def)
  apply(simp only:map_neuron_tl_id[of _ \<open>fst\<close>] map_fst_zip new_id_len)
  using distinct_elem[of \<open>sorted_list_of_set (output_layer_ids N)\<close>]
         distinct_sorted_list_of_set[of \<open>output_layer_ids N\<close>]
         output_layer_ids_subset_neuron_ids set_sorted_list_of_set
  by (metis bot.extremum set_empty sorted_list_of_set.fold_insort_key.infinite) 

lemma activation_is_activation: \<open>isActivation\<^sub>l(activation N \<phi>' \<alpha>' \<beta>')\<close>
  apply (simp add: isActivation\<^sub>l_def)
  apply (safe)
  subgoal apply (rule distinct_tail_activation) done
  subgoal apply (rule nn_pregraph.distinct_head_activation) 
          apply (rule NN_Digraph.nn_pregraph_mk ) done
  done

end 

paragraph \<open>Output layer proofs\<close>

lemma output_output_layer_length_equal:
   assumes notEmptyNeurons: \<open>neurons N \<noteq> {}\<close> 
   and notEmptyOutputLayer: \<open>length(out N) \<noteq> 0\<close>
   shows \<open>card(output_layer_ids N) = length(out N)\<close>
   using assms
   apply (simp add: out_def mk_new_ids_def mk_out_edge_def output_layer_ids_def)
   by auto

lemma new_ids_output_layer_length_equal: 
  assumes notEmptyNeurons: \<open>neurons N \<noteq> {}\<close> 
  and notEmptyOutputLayer: \<open>length(out N) \<noteq> 0\<close> 
  shows \<open>length(mk_new_ids N) = length(out N)\<close>
  using assms 
  apply (simp add: out_def)
  using output_output_layer_length_equal new_id_len 
  apply (simp add: new_id_len notEmptyNeurons out_def output_output_layer_length_equal)
  done

lemma distinct_output_edges: \<open>distinct (out N)\<close>
  apply (smt (verit, best) out_def card.empty card_distinct list.set(1) list.size(3))
  done

lemma map_out_neuron_hd_id: \<open>(map (\<lambda>x. Out (f x)) X) = (map (\<lambda>x. Out x) (map f X))\<close>
  by simp

context nn_pregraph begin 

lemma distinct_head_output: \<open>distinct(map hd (out N))\<close>
  apply (simp add: out_def Let_def mk_out_edge_def o_def) 
  apply (simp only: map_out_neuron_hd_id[of snd _] map_snd_zip new_id_len)
  using new_id_distinct
  apply (simp add: distinct_conv_nth)
  by auto

end 

lemma fold_and_map: \<open>foldr (\<and>) (map (\<lambda>x. True) X) True\<close> 
proof (induction "X")
  case Nil
  then show ?case by simp
next
  case (Cons a X)
  then show ?case by simp 
qed

lemma head_output_neurons: \<open>foldr (\<and>) (map (output_neuron \<circ> edge.hd) (out N)) True\<close> 
  apply (simp add: o_def out_def Let_def mk_out_edge_def)
  using fold_and_map 
  by(auto)

context neural_network_digraph begin 

lemma distinct_tail_output: \<open>distinct(map tl (out N))\<close>
  apply (simp add: out_def Let_def mk_out_edge_def o_def) 
  apply (simp only: map_neuron_tl_id[of _ fst _] map_fst_zip new_id_len)
  using distinct_sorted_list_of_set distinct_elem
  by (metis (mono_tags, lifting) distinct.simps(1) list.simps(8) output_layer_ids_subset_neuron_ids 
            sorted_list_of_set.fold_insort_key.infinite sorted_list_of_set.set_sorted_key_list_of_set)

lemma output_is_output:\<open>isOutput\<^sub>l(out N)\<close>
  apply (simp add: isOutput\<^sub>l_def isActivation\<^sub>l_def)
  apply (safe)
  subgoal apply (rule distinct_tail_output)  done
  subgoal apply (rule nn_pregraph.distinct_head_output) apply(rule NN_Digraph.nn_pregraph_empty) done
  subgoal apply (rule head_output_neurons) done
  done

paragraph \<open>Dense layer proofs\<close>

lemma dense_is_dense: 
  assumes neuronsNotZero: \<open>n > 0\<close>
  and weightEqualNeurons: \<open>length \<omega>' = n\<close>
  shows \<open>isDense\<^sub>s(set(dense N n \<omega>' \<phi>' \<alpha>' \<beta>'))\<close>
  using assms
  apply (safe)
  apply (simp add: isDense\<^sub>s_def dense_def activation_def)
  apply (simp add: neurons_def output_layer_ids_def output_layer_def output_verts_def mk_edge_def)
  apply (force)
  done

end
end
