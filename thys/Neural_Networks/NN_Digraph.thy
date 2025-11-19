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

section\<open>Neural Networks as Graphs\<close>
text\<open>
  In this theory, we use the AFP entry ``Graph Theory''~\<^cite>\<open>"noschinski:graph:2013"\<close>
  to model neural networks. In particular, we make use of the formalization of directed 
  graphs.
\<close>

theory NN_Digraph
imports
  Graph_Theory.Digraph
begin

definition
  pipe :: \<open>'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b\<close> (infixl \<open> \<triangleright> \<close> 70)  where
  \<open>a \<triangleright> f  = f a\<close>

text\<open>
We follow the notation used in \<^cite>\<open>"aggarwal:neural:2018"\<close>, i.e., a neural network consists
our of edges and neurons (nodes). 
\<close>

type_synonym id = nat

record ('a, 'b) Neuron  = 
  \<phi> :: 'b             \<comment> \<open>activation function\<close> 
  \<alpha> :: 'a             \<comment> \<open>learning rate\<close>
  \<beta> :: 'a             \<comment> \<open>bias\<close>
  uid :: id           \<comment> \<open>unique identifier\<close>

datatype ('a, 'b) neuron = In id | Out id | Neuron \<open>('a, 'b) Neuron\<close>

fun uid where
  \<open>uid (In nid)   = nid\<close>
| \<open>uid (Out nid)  = nid\<close>
| \<open>uid (Neuron n) = Neuron.uid n\<close>

record ('a, 'b) edge = 
  \<omega>  :: 'a            \<comment> \<open>weight input to head\<close>
  tl :: \<open>('a, 'b) neuron\<close>   \<comment> \<open>source neuron\<close>
  hd :: \<open>('a, 'b) neuron\<close>   \<comment> \<open>target neuron\<close>

type_synonym ('a, 'b) nn_pregraph = \<open>(('a, 'b) neuron, ('a, 'b) edge) pre_digraph\<close>

definition upd_edge :: \<open>('a, 'b) nn_pregraph \<Rightarrow> (('a, 'b) edge \<Rightarrow> ('a, 'b) edge)   
                        \<Rightarrow> ('a, 'b) nn_pregraph\<close> where
          \<open>upd_edge G upd   = \<lparr> 
                                             verts = verts G , 
                                             arcs = upd ` (arcs G), 
                                             tail = tail G, 
                                             head = head G
                                          \<rparr>\<close>

definition \<open>upd\<^sub>\<omega> \<omega>' hd_n\<^sub>i\<^sub>d tl_n\<^sub>i\<^sub>d a = (if uid (hd a) = hd_n\<^sub>i\<^sub>d \<and> uid (tl a) = tl_n\<^sub>i\<^sub>d 
                                      then \<lparr>\<omega> = \<omega>', tl = tl a, hd = hd a \<rparr> 
                                      else a)\<close>

definition upd_neuron :: \<open>('a, 'b) nn_pregraph \<Rightarrow> (('a, 'b) Neuron \<Rightarrow> ('a, 'b) Neuron)  
                         \<Rightarrow> ('a, 'b) nn_pregraph \<close> where
          \<open>upd_neuron G upd = (let upd_Neuron = case_neuron In Out (\<lambda> n. Neuron (upd n))
                              in           \<lparr>
                                              verts = upd_Neuron ` (verts G) , 
                                              arcs = (\<lambda> a. \<lparr> \<omega> = \<omega> a,  
                                                             tl = upd_Neuron (tl a), 
                                                             hd = upd_Neuron (hd a)\<rparr>) ` (arcs G), 
                                              tail = tail G, 
                                              head = head G
                                           \<rparr>)\<close>

definition \<open>upd\<^sub>\<phi> \<phi>' n\<^sub>i\<^sub>d n = (if Neuron.uid n = n\<^sub>i\<^sub>d 
                             then \<lparr>\<phi> = \<phi>', \<alpha> = \<alpha> n, \<beta> = \<beta> n, uid = Neuron.uid n \<rparr> 
                             else n)\<close>

definition \<open>upd\<^sub>\<beta> \<beta>' n\<^sub>i\<^sub>d n = (if Neuron.uid n = n\<^sub>i\<^sub>d 
                             then \<lparr>\<phi> = \<phi> n, \<alpha> = \<alpha> n, \<beta> = \<beta>', uid = Neuron.uid n \<rparr> 
                             else n)\<close>

definition \<open>upd\<^sub>\<alpha> \<alpha>' n\<^sub>i\<^sub>d n  = (if Neuron.uid n = n\<^sub>i\<^sub>d 
                             then \<lparr>\<phi> = \<phi> n, \<alpha> = \<alpha>', \<beta> = \<beta> n, uid = Neuron.uid n \<rparr> 
                             else n)\<close>

text\<open>
  A neural network is a directed graph without loops and without multi-edges. Moreover, 
  @{term "id"} of neurons are unique.
\<close>

definition input_verts :: \<open>(('a, 'b) neuron, ('a, 'b) edge) pre_digraph \<Rightarrow> ('a, 'b) neuron set\<close> 
  where
          \<open>input_verts G = (verts G) - (hd ` arcs G)\<close>

definition output_verts :: \<open>(('a, 'b) neuron, ('a, 'b) edge) pre_digraph \<Rightarrow> ('a, 'b) neuron set\<close> 
  where
          \<open>output_verts G = (verts G) - (tl ` arcs G)\<close>

definition internal_verts :: \<open>(('a, 'b) neuron, ('a, 'b) edge) pre_digraph \<Rightarrow> ('a, 'b) neuron set\<close>
  where
          \<open>internal_verts G = (verts G) - ((input_verts G) \<union> (output_verts G))\<close>

locale nn_pregraph = digraph G 
  for G::\<open>(('a::{comm_monoid_add,times,linorder}, 'b) neuron, ('a, 'b) edge) pre_digraph\<close> + 
  assumes id_vert_inj: \<open>inj_on uid (verts G)\<close>
  and     tail_eq_tl:  \<open>tail G = tl\<close>
  and     head_eq_hd:  \<open>head G = hd\<close>
  and     ids_growing: \<open>\<forall> e \<in> arcs G. uid (tl e) < uid (hd e)\<close> \<comment>\<open>Not strictly necessary, but simplifies termination proofs.\<close>
begin

lemma nn_pregraph: "nn_pregraph G" by intro_locales

end 

definition \<open>uids G = uid ` verts G\<close>

subsection\<open>Neurons as Vertices\<close>
context nn_pregraph
begin 
subsubsection\<open>The operation @{const \<open>add_vert\<close>} preserves neural networks\<close>

lemma nn_pregraph_add_neuron: 
  assumes \<open>uid n \<notin> (uids G) \<or> n \<in> verts G \<close> 
  shows \<open>nn_pregraph (add_vert n)\<close>
  apply standard
  subgoal by (simp add: wf_digraph.tail_in_verts wf_digraph_add_vert) 
  subgoal by (simp add: wf_digraph.head_in_verts wf_digraph_add_vert)
  subgoal by (simp add: verts_add_vert) 
  subgoal by (simp add: arcs_add_vert) 
  subgoal by (simp add: arcs_add_vert head_add_vert no_loops pre_digraph.tail_add_vert)
  subgoal by (simp add: arc_to_ends_def arcs_add_vert head_add_vert no_multi_arcs tail_add_vert) 
  subgoal proof(cases \<open>n \<in> verts G\<close>)
    case True
    then show ?thesis 
      by (simp add: id_vert_inj insert_absorb verts_add_vert)
  next
    case False
    then show ?thesis 
      using assms verts_add_vert arcs_add_vert head_add_vert no_loops apply(simp)
      using id_vert_inj uids_def image_def by blast 
  qed
  subgoal using tail_eq_tl tail_add_vert by simp 
  subgoal using head_eq_hd head_add_vert by simp 
  subgoal using arcs_add_vert ids_growing by blast 
done 


definition add_neuron::\<open>('a, 'b) neuron \<Rightarrow> ('a, 'b) nn_pregraph\<close> where
          \<open>add_neuron n = (if (uid n \<notin> (uids G) \<or> n \<in> verts G ) then add_vert n else G)\<close>

lemma nn_pregraph_add_nn_neuron:  \<open>nn_pregraph (add_neuron a)\<close>
  using add_neuron_def nn_pregraph_add_neuron nn_pregraph_axioms
  by simp
end

subsubsection\<open>The operation @{const \<open>pre_digraph.del_vert\<close>} preserves neural networks\<close>
context nn_pregraph 
begin 

lemma nn_pregraph_del_vert: \<open>nn_pregraph (del_vert n)\<close>
  apply standard
  subgoal by (simp add: wf_digraph.tail_in_verts wf_digraph_del_vert) 
  subgoal
    apply(simp add: ends_del_vert no_multi_arcs pre_digraph.arcs_del_vert inj_on_def)
    by (simp add: head_del_vert verts_del_vert)
  subgoal by (simp add: fin_digraph.finite_verts fin_digraph_del_vert)
  subgoal by (simp add: fin_digraph.finite_arcs fin_digraph_del_vert)
  subgoal by (simp add: head_del_vert no_loops pre_digraph.arcs_del_vert tail_del_vert)
  subgoal by (simp add: ends_del_vert no_multi_arcs pre_digraph.arcs_del_vert)
  subgoal 
    apply(simp add: ends_del_vert no_multi_arcs pre_digraph.arcs_del_vert inj_on_def)
    by (metis Diff_iff id_vert_inj inj_on_def verts_del_vert)
  subgoal using tail_eq_tl tail_del_vert by simp 
  subgoal using head_eq_hd head_del_vert by simp 
  subgoal using arcs_del_vert ids_growing by blast 
  done 

end 
subsection\<open>Arcs (Edges)\<close>

declare pre_digraph.add_arc_def [code]
definition \<open>add_nn_edge G a =   (if (uid (tl a) \<notin> (uids G) \<or> (tl a) \<in> verts G) 
                                  \<and> (uid (hd a) \<notin> (uids G) \<or> (hd a) \<in> verts G)
                                  \<and> uid (hd a) \<noteq> uid (tl a) 
                                  \<and> ((arc_to_ends G a) \<notin> arcs_ends G \<or> a \<in> arcs G)
                                  \<and> uid (tl a) < uid (hd a)
                               then pre_digraph.add_arc G a
                               else G)\<close>             

context nn_pregraph
begin 

subsubsection\<open>The operation @{const \<open>add_arc\<close>} preserves neural networks\<close>
lemma nn_pregraph_add_arc: 
  assumes \<open>uid (tl a) \<notin> (uids G) \<or> (tl a) \<in> verts G \<close> 
  and     \<open>uid (hd a) \<notin> (uids G) \<or> (hd a) \<in> verts G \<close> 
  and     \<open>uid (tl a) < uid (hd a)\<close>
  and     \<open>uid (hd a) \<noteq> uid (tl a)\<close> 
  and     \<open>(arc_to_ends G a) \<notin> arcs_ends G \<or> a \<in> arcs G\<close>
shows \<open>nn_pregraph (add_arc a)\<close>
  apply standard
  subgoal by (meson wf_digraph.tail_in_verts wf_digraph_add_arc) 
  subgoal by (meson wf_digraph_add_arc wf_digraph_def) 
  subgoal by (simp add: pre_digraph.verts_add_arc_conv) 
  subgoal by simp  
  subgoal using assms 
    by (metis head_add_arc head_eq_hd insert_iff no_loops pre_digraph.arcs_add_arc 
              pre_digraph.tail_add_arc tail_eq_tl)
  subgoal 
    by (metis arc_to_ends_def arcs_add_arc assms(5) insert_iff no_multi_arcs pre_digraph.head_add_arc 
              pre_digraph.tail_add_arc wf_digraph.dominatesI wf_digraph_axioms)
  subgoal  using assms
    by (smt (z3) Un_iff head_eq_hd id_vert_inj image_eqI inj_on_def insertE pre_digraph.verts_add_arc_conv
                   singletonD tail_eq_tl uids_def) 
  subgoal using tail_eq_tl by simp  
  subgoal using head_eq_hd by simp 
  subgoal by (simp add: assms(3) ids_growing) 
  done  

declare add_nn_edge_def[code]

lemma nn_pregraph_add_nn_edge: \<open>nn_pregraph (add_nn_edge G a)\<close>
  using add_nn_edge_def nn_pregraph_add_arc nn_pregraph_axioms 
  by metis 


subsubsection\<open>The operation @{const \<open>del_arc\<close>} preserves neural networks\<close>
lemma nn_pregraph_del_arc: \<open>nn_pregraph (del_arc a)\<close>
  apply standard
  subgoal by simp 
  subgoal by simp 
  subgoal by simp 
  subgoal by simp
  subgoal by (simp add: no_loops)
  subgoal by (simp add: arc_to_ends_def no_multi_arcs)
  subgoal by (simp add: id_vert_inj)
  subgoal by (simp add: tail_eq_tl) 
  subgoal by (simp add: head_eq_hd) 
  subgoal using tail_eq_tl head_eq_hd ids_growing by simp
  done


end 

subsection\<open>Updating Neurons\<close>
context nn_pregraph begin 

lemma upd\<^sub>\<phi>_nid_immutable[simp]: \<open>Neuron.uid n \<noteq> n\<^sub>i\<^sub>d \<Longrightarrow> n = (upd\<^sub>\<phi> \<phi>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<phi>_id_immutable[simp]: \<open>Neuron.uid n = Neuron.uid (upd\<^sub>\<phi> \<phi>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<phi>_\<alpha>_immutable[simp]:  \<open>\<alpha> n = \<alpha> (upd\<^sub>\<phi> \<phi>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<phi>_\<beta>_immutable[simp]:  \<open>\<beta> n = \<beta> (upd\<^sub>\<phi> \<phi>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<beta>_nid_immutable[simp]: \<open>Neuron.uid n \<noteq> n\<^sub>i\<^sub>d \<Longrightarrow> n = (upd\<^sub>\<beta> \<beta>' n\<^sub>i\<^sub>d n)\<close>  
 and  upd\<^sub>\<beta>_id_immutable[simp]: \<open>Neuron.uid n = Neuron.uid (upd\<^sub>\<beta> \<beta>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<beta>_\<phi>_immutable[simp]:  \<open>\<phi> n = \<phi> (upd\<^sub>\<beta> \<beta>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<beta>_\<alpha>_immutable[simp]:  \<open>\<alpha> n = \<alpha> (upd\<^sub>\<beta> \<beta>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<alpha>_nid_immutable[simp]: \<open>Neuron.uid n \<noteq> n\<^sub>i\<^sub>d \<Longrightarrow> n = (upd\<^sub>\<alpha> \<alpha>' n\<^sub>i\<^sub>d n)\<close>  
 and  upd\<^sub>\<alpha>_id_immutable[simp]: \<open>Neuron.uid n = Neuron.uid (upd\<^sub>\<alpha> \<alpha>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<alpha>_\<phi>_immutable[simp]:  \<open>\<phi> n = \<phi> (upd\<^sub>\<alpha> \<alpha>' n\<^sub>i\<^sub>d n)\<close>
 and  upd\<^sub>\<alpha>_\<beta>_immutable[simp]:  \<open>\<beta> n = \<beta> (upd\<^sub>\<alpha> \<alpha>' n\<^sub>i\<^sub>d n)\<close>
 by(cases "n", simp_all add:upd\<^sub>\<phi>_def upd\<^sub>\<alpha>_def upd\<^sub>\<beta>_def)+


lemma wf_digraph_update_neuron:
  assumes \<open>\<forall> n. Neuron.uid n = Neuron.uid (upd n)\<close> 
  shows\<open>wf_digraph (upd_neuron G upd )\<close>
  unfolding upd_neuron_def
  apply(simp add: wf_digraph assms image_def wf_digraph_def tail_eq_tl head_eq_hd Let_def)
  using head_eq_hd head_in_verts tail_eq_tl tail_in_verts
  by fastforce 

lemma fin_digraph_update_neuron:
  assumes \<open>\<forall> n. Neuron.uid n = Neuron.uid (upd n)\<close> 
  shows\<open>fin_digraph (upd_neuron G upd )\<close>
  apply standard 
     apply (meson assms wf_digraph.tail_in_verts wf_digraph_update_neuron)
    apply (meson assms wf_digraph.head_in_verts wf_digraph_update_neuron) 
  by(simp_all add: upd_neuron_def Let_def)


lemma nomulti_digraph_update_neuron:
  assumes \<open>\<forall> n. Neuron.uid n = Neuron.uid (upd n)\<close> 
  shows \<open>nomulti_digraph (upd_neuron G upd )\<close>
  apply standard 
  subgoal by (meson assms wf_digraph_def wf_digraph_update_neuron) 
  subgoal by (meson upd_neuron_def  assms wf_digraph_def wf_digraph_update_neuron) 
  subgoal 
    apply(simp add:image_def arc_to_ends_def upd_neuron_def Let_def id_vert_inj assms 
                        wf_digraph tail_eq_tl head_eq_hd)
    using assms head_eq_hd head_in_verts id_vert_inj inj_onD no_multi_arcs tail_eq_tl tail_in_verts     
    apply simp 
    by (smt (verit) arc_to_ends_def edge.select_convs(2,3) inj_onD neuron.simps(10,11,12) uid.elims uid.simps(3)) 
  done 

lemma loopfree_digraph_update_neuron:
  assumes \<open>\<forall> n. Neuron.uid n = Neuron.uid (upd n)\<close> 
  shows \<open>loopfree_digraph (upd_neuron G upd)\<close>
  apply standard 
  subgoal by (meson assms wf_digraph.tail_in_verts wf_digraph_update_neuron)
  subgoal by (meson assms wf_digraph.head_in_verts wf_digraph_update_neuron) 
  subgoal
    apply(simp add:image_def arc_to_ends_def Let_def upd_neuron_def id_vert_inj assms 
                        wf_digraph tail_eq_tl head_eq_hd)
    using assms ids_growing order_less_irrefl neuron.distinct(5) neuron.inject(3)
    apply simp 
    by (smt (verit) edge.select_convs(2,3) less_not_refl3 neuron.simps(10,11,12) uid.elims uid.simps(3))
  done 

lemma nn_pregraph_update_neuron: 
  assumes \<open>\<forall> n. Neuron.uid n = Neuron.uid (upd n)\<close> 
  shows\<open>nn_pregraph (upd_neuron G upd)\<close>
  apply standard 
  subgoal by (meson assms wf_digraph.tail_in_verts wf_digraph_update_neuron) 
  subgoal by (meson assms wf_digraph.head_in_verts wf_digraph_update_neuron) 
  subgoal using assms fin_digraph.finite_verts fin_digraph_update_neuron by blast 
  subgoal using assms fin_digraph.finite_arcs fin_digraph_update_neuron by blast 
  subgoal by (metis assms(1) loopfree_digraph.no_loops loopfree_digraph_update_neuron) 
  subgoal by (metis assms(1) nomulti_digraph.no_multi_arcs nomulti_digraph_update_neuron)
  subgoal apply(simp add:Let_def assms upd_neuron_def id_vert_inj image_iff inj_on_def uid.elims)
    using assms id_vert_inj inj_on_def neuron.distinct neuron.simps uid.elims by (smt (verit))
  subgoal by (simp add: tail_eq_tl upd_neuron_def Let_def) 
  subgoal by (simp add: head_eq_hd upd_neuron_def Let_def) 
  subgoal apply(simp add:  assms upd_neuron_def ids_growing Let_def) using ids_growing
    by (smt (z3) assms neuron.exhaust neuron.simps(10) neuron.simps(11) neuron.simps(12) uid.simps(3)) 
  
  done
 
lemma nn_pregraph_upd\<^sub>\<phi>[simp]: \<open>nn_pregraph (upd_neuron G (upd\<^sub>\<phi> \<phi>' n\<^sub>i\<^sub>d))\<close>
 and  nn_pregraph_upd\<^sub>\<beta>[simp]: \<open>nn_pregraph (upd_neuron G (upd\<^sub>\<beta> \<beta>' n\<^sub>i\<^sub>d))\<close>
 and  nn_pregraph_upd\<^sub>\<alpha>[simp]: \<open>nn_pregraph (upd_neuron G (upd\<^sub>\<alpha> \<alpha>' n\<^sub>i\<^sub>d))\<close>
  using nn_pregraph_update_neuron by simp_all

end

subsection\<open>Updating arcs (edges)\<close>

context nn_pregraph begin 

lemma upd\<^sub>\<omega>_tl_immutable[simp]: \<open>(tl a = tl (upd\<^sub>\<omega>  \<omega>' n\<^sub>h\<^sub>d n\<^sub>t\<^sub>l a))\<close>
and   upd\<^sub>\<omega>_hd_immutable[simp]: \<open>(hd a = hd (upd\<^sub>\<omega>  \<omega>' n\<^sub>h\<^sub>d n\<^sub>t\<^sub>l a))\<close>
 by(auto simp: upd\<^sub>\<omega>_def split: if_split) 

lemma upd\<^sub>\<omega>_ends_immutable[simp]: \<open>(arc_to_ends G a = arc_to_ends G (upd\<^sub>\<omega>  \<omega>' n\<^sub>h\<^sub>d n\<^sub>t\<^sub>l a))\<close>
  by (auto simp add: arc_to_ends_def head_eq_hd tail_eq_tl) 

lemma upd_edge_tail_immutable: 
  \<open>tail (upd_edge G upd) = tail G \<close> 
  by (simp add: upd_edge_def) 

lemma upd_edge_head_immutable: 
  \<open>head (upd_edge G upd)  = head G  \<close> 
  by (simp add: upd_edge_def) 

lemma upd_edge_vert_immutable: \<open>verts (upd_edge G upd) = verts G\<close>
  by(simp add: upd_edge_def)


lemma upd_edge_arcs: \<open>a \<in> arcs (upd_edge G upd)  \<Longrightarrow> \<exists> x \<in> arcs G. a = upd x\<close>
  by (auto simp: upd_edge_def)


lemma wf_digraph_update_edge: 
  assumes \<open>\<forall> a \<in> arcs G. (arc_to_ends G a = arc_to_ends G (upd a ))\<close>
  shows  \<open>wf_digraph (upd_edge G upd )\<close>
  apply unfold_locales
  subgoal  
    using assms upd_edge_vert_immutable upd_edge_tail_immutable 
    apply(simp add:upd_edge_def arc_to_ends_def image_def) 
     using tail_in_verts by auto
  subgoal 
    using assms upd_edge_vert_immutable upd_edge_tail_immutable 
    apply(simp add:upd_edge_def arc_to_ends_def image_def) 
     using head_in_verts by auto
   done

lemma fin_digraph_update_edge:  
  assumes \<open>\<forall> a \<in> arcs G. (arc_to_ends G a = arc_to_ends G (upd a ))\<close>
  shows  \<open>fin_digraph (upd_edge G upd )\<close> 
  by (metis fin_digraph_axioms fin_digraph_axioms_def fin_digraph_def finite_imageI 
            pre_digraph.select_convs(1) pre_digraph.select_convs(2) upd_edge_def 
            wf_digraph_update_edge assms)  

lemma nomulti_digraph_update_edge:  
  assumes \<open>\<forall> a \<in> arcs G. (arc_to_ends G a = arc_to_ends G (upd a ))\<close>
  shows  \<open>nomulti_digraph (upd_edge G upd )\<close>
  apply standard 
  subgoal using assms by (meson wf_digraph_def wf_digraph_update_edge) 
  subgoal using assms by (meson wf_digraph_def wf_digraph_update_edge)
  subgoal  using assms 
    by (metis arc_to_ends_def local.upd_edge_arcs  nn_pregraph.upd_edge_head_immutable 
              nn_pregraph.upd_edge_tail_immutable nn_pregraph_axioms no_multi_arcs)
  done 

lemma loopfree_digraph_update_edge:
  assumes \<open>\<forall> a \<in> arcs G. (arc_to_ends G a = arc_to_ends G (upd a ))\<close>
  shows  \<open>loopfree_digraph (upd_edge G upd)\<close>
  apply standard 
  subgoal using assms by (simp add: wf_digraph.tail_in_verts wf_digraph_update_edge) 
  subgoal using assms by (simp add: wf_digraph.head_in_verts wf_digraph_update_edge) 
  subgoal using assms by (metis adj_not_same arc_to_ends_def dominatesI local.upd_edge_arcs 
                                upd_edge_head_immutable upd_edge_tail_immutable) 
  done


lemma nn_pregraph_update_edge:
  assumes \<open>\<forall> a \<in> arcs G. (arc_to_ends G a = arc_to_ends G (upd a ))\<close>
  and     \<open>\<forall> a \<in> arcs G. uid (tl (upd a )) < uid (hd (upd a ))\<close> 
shows  \<open>nn_pregraph (upd_edge G upd )\<close> 
  apply(simp add: digraph_def fin_digraph_update_edge head_eq_hd id_vert_inj loopfree_digraph_update_edge 
            nn_pregraph_axioms_def nn_pregraph_def nomulti_digraph_update_edge 
            tail_eq_tl upd_edge_def assms upd_edge_arcs nn_pregraph_axioms.intro 
            upd_edge_head_immutable upd_edge_tail_immutable upd_edge_vert_immutable)
  by (metis assms(1) fin_digraph_update_edge head_eq_hd loopfree_digraph_update_edge 
            nomulti_digraph_update_edge tail_eq_tl upd_edge_def)

lemma nn_pregraph_upd\<^sub>\<omega>[simp]: \<open>nn_pregraph (upd_edge G (upd\<^sub>\<omega> \<omega>' n\<^sub>h\<^sub>d n\<^sub>t\<^sub>l))\<close>
  using nn_pregraph_update_edge
  by (metis (no_types, lifting) ids_growing upd\<^sub>\<omega>_ends_immutable upd\<^sub>\<omega>_hd_immutable upd\<^sub>\<omega>_tl_immutable) 

end


record ('a, 'b, 'c) neural_network = 
  graph :: "(('a, 'b) neuron, ('a, 'b) edge) pre_digraph"
  activation_tab :: \<open>'b \<Rightarrow> 'c option\<close>

definition upd_edge' :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> (('a, 'b) edge \<Rightarrow> ('a, 'b) edge)
                        \<Rightarrow> ('a, 'b, 'c) neural_network\<close> where
          \<open>upd_edge' N upd   = \<lparr> 
                                 graph = upd_edge (graph N) upd,
                                 activation_tab = activation_tab N
                              \<rparr>\<close>

definition upd_neuron' :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> (('a, 'b) Neuron \<Rightarrow> ('a, 'b) Neuron)  
                         \<Rightarrow> ('a, 'b, 'c) neural_network\<close> where
          \<open>upd_neuron' N upd = \<lparr> 
                                  graph = upd_neuron (graph N) upd,
                                  activation_tab = activation_tab N
                               \<rparr>\<close>

definition input_layer :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> ('a, 'b) neuron set\<close> where
          \<open>input_layer N = input_verts (graph N)\<close>

definition arity :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> nat\<close> where
          \<open>arity N = card (input_layer N)\<close>

definition input_layer_ids :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> id set\<close> where
          \<open>input_layer_ids N = uid ` (input_layer N)\<close>

definition output_layer :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> ('a, 'b) neuron set\<close> where
          \<open>output_layer N = output_verts (graph N)\<close>

definition output_layer_ids :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> id set\<close> where
          \<open>output_layer_ids N = uid ` (output_layer N)\<close>

definition incoming_arcs :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> id \<Rightarrow> ('a, 'b) edge set\<close> where

           \<open>incoming_arcs N n\<^sub>i\<^sub>d = {a . a \<in> arcs (graph N) \<and> uid (hd a) = n\<^sub>i\<^sub>d}\<close>

definition \<open>sorted_list_of_set' \<equiv> map_fun id id (folding_on.F (insort_key (\<lambda> x. uid (tl x)))) []\<close>

definition incoming_arcs_l :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> id \<Rightarrow> ('a, 'b) edge list\<close> where
           \<open>incoming_arcs_l N n\<^sub>i\<^sub>d = sorted_list_of_set' (incoming_arcs N n\<^sub>i\<^sub>d)\<close>

context nn_pregraph begin 
lemma incoming_arcs_l_eq_incoming_arcs: \<open>set (incoming_arcs_l N n\<^sub>i\<^sub>d)= (incoming_arcs N n\<^sub>i\<^sub>d)\<close>
  unfolding incoming_arcs_l_def  sorted_list_of_set'_def
  oops

lemma incoming_arcs_l_alt_def: \<open> (incoming_arcs_l N n\<^sub>i\<^sub>d)
= (sorted_key_list_of_set (\<lambda> x. uid (tl x)) (incoming_arcs N n\<^sub>i\<^sub>d))\<close>
  unfolding incoming_arcs_l_def sorted_list_of_set'_def incoming_arcs_def
  by (simp add: sorted_key_list_of_set_def)

lemma insert_key_comm: "inj f  \<Longrightarrow> (insort_key f y \<circ> insort_key f x) = (insort_key f x \<circ> insort_key f y)"
  apply (cases "x = y") 
  by (auto intro: insort_key_left_comm simp add: inj_def inj_on_def fun_eq_iff)

lemma tl_subset_verts: \<open>tl ` (arcs G) \<subseteq> verts G \<close>
  using tail_eq_tl tail_in_verts by force 

lemma hd_subset_verts: \<open>hd ` (arcs G) \<subseteq> verts G \<close>
  using head_eq_hd head_in_verts by force 

lemma inj_on_tl: \<open>inj_on uid (tl ` (arcs G)) \<close>
using id_vert_inj tl_subset_verts
  by (meson inj_on_subset)

end



definition outgoing_arcs :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> id \<Rightarrow> ('a, 'b) edge set\<close> where
           \<open>outgoing_arcs N n\<^sub>i\<^sub>d = {a . a \<in> arcs (graph N) \<and> uid (tl a) = n\<^sub>i\<^sub>d}\<close>

definition neurons :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> ('a, 'b) neuron set\<close> where
  \<open>neurons = verts o graph\<close>

definition edges :: \<open>('a, 'b, 'c) neural_network \<Rightarrow> ('a, 'b) edge set\<close> where
  \<open>edges = arcs o graph\<close>


locale nn_graph = nn_pregraph + 
  assumes id_vert_inj: \<open>inj_on uid (verts G)\<close>
  and     inputs_In:   
            \<open>input_verts G = Set.filter (\<lambda> v. (case v of In _ \<Rightarrow> True | _ \<Rightarrow> False)) (verts G) \<close>
  and     outputs_Out: 
            \<open>output_verts G = Set.filter (\<lambda> v. (case v of Out _ \<Rightarrow> True | _ \<Rightarrow> False)) (verts G) \<close>
  and     internal_Neuron: 
            \<open>internal_verts G = Set.filter (\<lambda> v. (case v of Neuron _ \<Rightarrow> True | _ \<Rightarrow> False)) (verts G) \<close>
begin

lemma nn_graph: "nn_graph G" by intro_locales
end 


locale neural_network_digraph = 
  fixes N::\<open>('a::{comm_monoid_add,times,linorder,one}, 'b, 'c) neural_network\<close> 
  assumes \<open>nn_graph (graph N)\<close>
  and \<open>\<phi> ` {n . Neuron n \<in> (verts (graph N)) }  \<subseteq> dom (activation_tab N)\<close> 

subsection\<open>The empty neural network\<close>

definition empty:: \<open>('a, 'b) nn_pregraph\<close> where
          \<open>empty = \<lparr> verts={}, arcs = {}, tail = edge.tl, head = edge.hd \<rparr> \<close>

lemma nn_pregraph_empty[simp]: \<open>nn_pregraph (empty)\<close>
  unfolding empty_def apply standard
  by(auto simp add: input_verts_def output_verts_def internal_verts_def)

lemma nn_graph_empty[simp]: \<open>nn_graph (empty)\<close>
  unfolding empty_def apply standard
  by(auto simp add: input_verts_def output_verts_def internal_verts_def)

lemma fold_inv: "P e \<Longrightarrow> (\<forall> e' x. P e' \<longrightarrow> P (f x e')) \<Longrightarrow> P (fold f xs e)"
  by (simp add: fold_invariant)


lemma nn_pregraph_fold: \<open>nn_pregraph G \<Longrightarrow> nn_pregraph (foldr (\<lambda> a b. add_nn_edge b a) edge_list G)\<close>
proof(induction "edge_list")
  case Nil
  then show ?case by (simp add:nn_graph.axioms)  
next
  case (Cons a edge_list) note * = this
  then show ?case 
    using fold_inv[of nn_pregraph G "(\<lambda>x s. add_nn_edge s x)" edge_list]
    by (simp add: fold_inv nn_pregraph.nn_pregraph_add_nn_edge) 
  qed

definition 
\<open>mk_nn_pregraph edge_list = foldr (\<lambda> a b. add_nn_edge b a) edge_list empty\<close>

lemma nn_pregraph_mk: \<open>nn_pregraph(mk_nn_pregraph edge_list)\<close>
  using mk_nn_pregraph_def nn_pregraph_fold
  by (metis nn_graph.axioms(1) nn_graph_empty)
 
lemma verts_subseteq_add_edge: "nn_pregraph G \<Longrightarrow> verts G \<subseteq> verts (add_nn_edge G a)"
  unfolding add_nn_edge_def pre_digraph.add_arc_def 
  by auto

subsection\<open>Computing Predictions of Neural Networks\<close>
datatype error = OK | ERROR

locale neural_network_digraph_single = neural_network_digraph N
  for N::\<open>('a::{comm_monoid_add,times,linorder,one}, 'b, 'a \<Rightarrow> 'a) neural_network\<close> 


function (sequential, domintros) predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e'::\<open>nat
                                 \<Rightarrow> ('a::{comm_monoid_add,times,linorder,one}, 'b, 'a \<Rightarrow> 'a) neural_network 
                                 \<Rightarrow> (id \<rightharpoonup> 'a) \<Rightarrow> ('a, 'b) edge  \<Rightarrow> ('a \<times>  error)\<close>
  where 
  \<open>predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' _ N inputs (\<lparr>\<omega>=_,  tl= _, hd=In _\<rparr>)       = (0, ERROR)\<close>
| \<open>predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' _ N inputs (\<lparr>\<omega>=_,  tl=Out _ , hd=_ \<rparr>)     = (0, ERROR)\<close>
| \<open>predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' _ N inputs (\<lparr>\<omega>=\<omega>', tl=In uid\<^sub>i\<^sub>n, hd=_ \<rparr>)   = (case inputs uid\<^sub>i\<^sub>n of 
                                                                None   \<Rightarrow> (0, ERROR)  
                                                              | Some v \<Rightarrow> (v * \<omega>',  OK))\<close>
| \<open>predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' n N inputs e = (if 0 < n then  
                  (let 
                      \<omega>'    = \<omega> e;
                      tl' = (case (tl e) of (Neuron t) \<Rightarrow> t); 
                      E'    = incoming_arcs N (Neuron.uid tl');
                      lvals = ((\<lambda> e'. (case predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (n-1)  N inputs e' of  
                                            (_, ERROR) \<Rightarrow> ((0,0),  ERROR)  
                                          | (v, OK)   \<Rightarrow> ((v ,uid (tl e')), OK))) ` E')
                  in  
                  (  case (activation_tab N) (\<phi> tl') of 
                         Some f \<Rightarrow> (\<omega>' *(  f((\<Sum> v \<in> lvals.  (fst (fst v))) + (\<beta> tl'))),  OK)
                       | None  \<Rightarrow> (0, ERROR)))
 else  (0, ERROR) )\<close>
  apply pat_completeness                                                                 
  by(simp_all) 

termination 
  by(size_change)

definition
\<open>predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e N inputs e = (case predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e' (card (edges N)) N inputs e of 
                                        (r, OK) \<Rightarrow> Some r
                                      | (_, ERROR) \<Rightarrow> None)\<close> 

definition
  \<open>get_input_neuron_ids_l N = sorted_list_of_set (uid ` (input_verts (graph N)))\<close>
definition 
  \<open>mk_input_map N vs = map_of (rev (zip (get_input_neuron_ids_l N) vs))\<close>
definition 
  \<open>get_output_edge_ids_l N = sorted_list_of_set (uid ` (output_verts (graph N)))\<close>
definition 
  \<open>get_output_edge_l N = map the_elem (map (\<lambda> i. {e . e \<in> edges N \<and> i = uid (hd e)})  (get_output_edge_ids_l N))\<close>
definition 
  \<open> predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e_\<^sub>l\<^sub>i\<^sub>s\<^sub>t N inputs' = those (map (\<lambda> e.  predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h\<^sub>_\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>e N (mk_input_map N inputs') e) (get_output_edge_l N))\<close>


context neural_network_digraph_single begin

lemma ids_growing':  \<open>neural_network_digraph N \<Longrightarrow> e \<in> edges N \<Longrightarrow> uid (tl e) < uid (hd e)\<close>
  by (metis comp_def edges_def neural_network_digraph_def nn_graph.axioms(1) nn_pregraph.ids_growing) 

end

context neural_network_digraph begin
fun (sequential) predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h::\<open>(id \<rightharpoonup> 'a) list \<Rightarrow> ('a, 'b) edge list \<Rightarrow> ('a list \<times> error)\<close>
  where 
  \<open>predict\<^sub>d\<^sub>i\<^sub>g\<^sub>r\<^sub>a\<^sub>p\<^sub>h  _ _ = ([], ERROR)\<close>
end

record 'a data =
  inputs::\<open>id \<rightharpoonup> 'a\<close> 
  outputs::\<open>id \<rightharpoonup> 'a\<close> 

end
