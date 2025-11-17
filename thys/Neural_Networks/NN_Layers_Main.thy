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

section\<open>Main Theory (Layers)\<close>
theory
  NN_Layers_Main
  imports
   NN_Common 
   Activation_Functions
   NN_Digraph_Layers
   NN_Layers_List_Main
   NN_Layers_Matrix_Main

begin
text\<open>\label{thy:NN_Layers_Main}\<close>

subsection\<open>Converting between List-based and Matrix-based Sequential Layer Models \<close>
fun layer_list_to_matrix::\<open>('a list, 'b, 'a list list) layer \<Rightarrow> ('a Matrix.vec, 'b, 'a Matrix.mat) layer\<close>
  where 
    \<open>layer_list_to_matrix (In l)  = (In l)\<close>
  | \<open>layer_list_to_matrix (Out l) = (Out l)\<close>
  | \<open>layer_list_to_matrix (Activation l) = (Activation \<lparr>name = name l, units = units l, \<phi> = \<phi> l\<rparr>)\<close>
  | \<open>layer_list_to_matrix (Dense l) = (let dimc = length (List.hd (\<omega> l)) in 
                                     (Dense \<lparr>name = name l, units = units l, \<phi> = \<phi> l, 
                                     \<beta> = vec_of_list (\<beta> l), \<omega> = transpose_mat (mat_of_rows_list dimc (\<omega> l)) \<rparr>))\<close>

fun 
  layer_matrix_to_list::\<open>('a Matrix.vec, 'b, 'a Matrix.mat) layer \<Rightarrow> ('a list, 'b, 'a list list) layer\<close>
  where 
    \<open>layer_matrix_to_list (In l)  = (In l)\<close>
  | \<open>layer_matrix_to_list (Out l) = (Out l)\<close>
  | \<open>layer_matrix_to_list (Activation l) = (Activation \<lparr>name = name l, units = units l, \<phi> = \<phi> l\<rparr>)\<close>
  | \<open>layer_matrix_to_list (Dense l) = (Dense \<lparr>name = name l, units = units l, \<phi> = \<phi> l, 
                                     \<beta> = list_of_vec (\<beta> l), \<omega> = mat_to_list (transpose_mat  (\<omega> l)) \<rparr>)\<close>


definition activation_list_to_matrix:: \<open>('b \<Rightarrow> (('a list \<Rightarrow> 'a list ) option)) \<Rightarrow> ('b \<Rightarrow> (('a Matrix.vec \<Rightarrow> 'a Matrix.vec ) option))\<close>
  where 
    "activation_list_to_matrix a = map_option (\<lambda> f . vec_of_list \<circ> f \<circ> list_of_vec ) \<circ> a"

definition activation_matrix_to_list:: \<open>('b \<Rightarrow> (('a Matrix.vec \<Rightarrow> 'a Matrix.vec ) option)) \<Rightarrow> ('b \<Rightarrow> (('a list \<Rightarrow> 'a list ) option))\<close>
  where 
    "activation_matrix_to_list a = map_option (\<lambda> f . list_of_vec \<circ> f \<circ> vec_of_list ) \<circ> a"

definition 
  nn_list_to_matrix::"('a list, 'b, 'a list list) neural_network_seq_layers \<Rightarrow> ('a Matrix.vec, 'b, 'a mat) neural_network_seq_layers"
  where
    \<open>nn_list_to_matrix N = \<lparr>layers = map layer_list_to_matrix (layers N),
                          activation_tab = activation_list_to_matrix (activation_tab N)\<rparr>\<close>

definition 
  nn_matrix_to_list::"('a Matrix.vec, 'b, 'a mat) neural_network_seq_layers \<Rightarrow> ('a list, 'b, 'a list list) neural_network_seq_layers"
  where
    \<open>nn_matrix_to_list N = \<lparr>layers = map layer_matrix_to_list (layers N),
                          activation_tab = activation_matrix_to_list (activation_tab N)\<rparr>\<close>

subsection\<open>Converting Between List/Matrix-based Representations Preserves Consistency\<close>

lemma layer_list_matrix_inverse: 
  \<open>layer_consistent\<^sub>l N n  l \<Longrightarrow> layer_matrix_to_list (layer_list_to_matrix l) = l\<close>
proof(induction "l")
  case (In x)
  then show ?case by simp 
next
  case (Out x)
  then show ?case by simp
next
  case (Dense x)  note i = this
  then show ?case  
    apply(simp add:list_vec)
    apply(subst mat_list[of "\<omega> x"]) 
     apply (metis empty_iff list.set(1) list.set_sel(1)) 
    by(simp)
next
  case (Activation x)
  then show ?case by simp
qed

lemma layer_list_list_inverse: 
  \<open>layer_consistent\<^sub>m N n  l \<Longrightarrow> layer_list_to_matrix (layer_matrix_to_list l) = l\<close>
proof(induction "l")
  case (In x)
  then show ?case by simp
next
  case (Out x)
  then show ?case by simp
next
  case (Dense x)  note ii = this                          
  then show ?case 
  proof(cases "\<forall> c \<in> set (mat_to_list (\<omega> x)\<^sup>T). dim_row (\<omega> x) = (length c)")
    case True note i = this 
    then show ?thesis proof(cases "mat_to_list (\<omega> x)\<^sup>T = []")
      case True
      then show ?thesis using i ii  apply(simp add:vec_list Let_def)
        by (metis dim_row_list index_transpose_mat(2) less_nat_zero_code list.size(3))
    next
      case False
      then have \<open>dim_row (\<omega> x) = length (List.hd (mat_to_list (\<omega> x)\<^sup>T))\<close> using i by simp  
      then show ?thesis  using i  
        using i list_mat_transpose_transpose list_mat index_transpose_mat Matrix.transpose_transpose
          list_mat_transpose_transpose[of "\<omega> x", simplified]
        by(simp  add:vec_list)
    qed
  next
    case False
    then show ?thesis  
      by (metis dim_col_mat_list index_transpose_mat(3))
  qed
next
  case (Activation x)
  then show ?case by simp
qed



lemma activation_list_inverse: \<open>activation_matrix_to_list (activation_list_to_matrix a) x = a x\<close>
proof(cases "a x = None")
  case True
  then show ?thesis 
    unfolding activation_list_to_matrix_def activation_matrix_to_list_def o_def
    by simp
next
  case False
  then show ?thesis 
    unfolding activation_list_to_matrix_def activation_matrix_to_list_def o_def
    by(auto simp add:list_vec)
qed

lemma activation_list_inverse': \<open>activation_matrix_to_list (activation_list_to_matrix a) =a\<close>
  by(rule ext, metis activation_list_inverse)


lemma activation_matrix_inverse: \<open>activation_list_to_matrix (activation_matrix_to_list a) x = a x\<close>
proof(cases "a x = None")
  case True
  then show ?thesis 
    unfolding activation_list_to_matrix_def activation_matrix_to_list_def o_def
    by simp
next
  case False
  then show ?thesis 
    unfolding activation_list_to_matrix_def activation_matrix_to_list_def o_def
    by(auto simp add:vec_list)
qed

lemma activation_matrix_inverse': \<open>activation_list_to_matrix (activation_matrix_to_list a) = a\<close>
  by(rule ext, metis activation_matrix_inverse)

lemma is_In_seq_l_eq_m:
  assumes \<open>(layers N) \<noteq> []\<close> 
  shows \<open>isIn (List.hd (layers N)) = isIn (List.hd (layers (nn_list_to_matrix N)))\<close>
proof(cases "N")
  case (fields layers activation_tab) note i = this
  then show ?thesis 
  proof(cases layers)
    case Nil
    then show ?thesis using assms i  by simp
  next
    case (Cons a list)
    then show ?thesis 
      using assms i 
      unfolding nn_list_to_matrix_def  
      by(cases a, simp_all)
  qed 
qed

lemma is_Out_seq_l_eq_m:
  assumes \<open>(layers N) \<noteq> []\<close> 
  shows \<open>isOut (last (layers N)) = isOut (last (layers (nn_list_to_matrix N)))\<close>
proof(cases "N")
  case (fields layers activation_tab) note i = this
  then show ?thesis
     using assms unfolding fields
   proof(induction layers)
     case Nil
     then show ?case by simp
   next
     case (Cons a layers)
     then show ?case 
    unfolding nn_list_to_matrix_def  
      by(cases a, simp_all)
    qed
  qed

lemma is_Internal_seq_l_eq_m:
  assumes \<open>(layers N) \<noteq> []\<close> 
  shows \<open>list_all isInternal ((List.tl o butlast) (layers N)) = list_all isInternal ((List.tl o butlast) (layers (nn_list_to_matrix N)))\<close>
proof(cases "N")
  case (fields layers activation_tab) note i = this
  then show ?thesis
     using assms unfolding fields
   proof(induction layers)
     case Nil
     then show ?case by simp
   next
     case (Cons x xs)
      
     then show ?case proof(induction xs)
       case Nil
       then show ?case  
         unfolding nn_list_to_matrix_def 
         by simp
     next
       case (Cons a xs)
       then show ?case 
         unfolding nn_list_to_matrix_def  
         by(cases a,  auto split:if_splits)
     qed
   qed
 qed 

lemma valid_activation_tab_seq_l_imp_m:
  \<open>valid_activation_tab\<^sub>l (activation_tab N) \<Longrightarrow>  valid_activation_tab\<^sub>m (activation_tab (nn_list_to_matrix N))\<close>
  unfolding valid_activation_tab\<^sub>l_def valid_activation_tab\<^sub>m_def nn_list_to_matrix_def activation_list_to_matrix_def o_def
  by (simp, smt (verit, del_insts) length_list_of_vec list_vec map_option_eq_Some mem_Collect_eq ran_def) 

lemma layers_consistent_seq_l_imp_m:
  assumes \<open>layers_consistent\<^sub>l N n  (layers N)\<close> 
  shows \<open>layers_consistent\<^sub>m (nn_list_to_matrix N) n  (layers (nn_list_to_matrix N)) \<close>
proof(cases "N")
  case (fields layers activation_tab) note i = this
  then show ?thesis 
    unfolding fields 
  proof(insert assms[simplified fields, simplified], induction "layers" arbitrary:n activation_tab)
    case Nil
    then show ?case   
      unfolding nn_list_to_matrix_def valid_activation_tab\<^sub>l_def valid_activation_tab\<^sub>m_def activation_list_to_matrix_def o_def
      by simp   next
    case (Cons a layers)
    then show ?case proof(cases "a") 
      case (In x1) note iii = this
      then show ?thesis   using Cons 
        unfolding In nn_list_to_matrix_def valid_activation_tab\<^sub>l_def valid_activation_tab\<^sub>m_def activation_list_to_matrix_def o_def
        apply(simp add: Cons iii nn_list_to_matrix_def activation_list_to_matrix_def o_def)
        using  iii Cons layers_consistent\<^sub>l_activation_tab_const 
          layers_consistent\<^sub>m_activation_tab_const neural_network_seq_layers.select_convs(2)
        by metis 
    next
      case (Out x2)
      then show ?thesis using Cons 
        unfolding nn_list_to_matrix_def valid_activation_tab\<^sub>l_def valid_activation_tab\<^sub>m_def activation_list_to_matrix_def o_def
        by (simp, metis (mono_tags, lifting) layers_consistent\<^sub>l_activation_tab_const 
            layers_consistent\<^sub>m_activation_tab_const neural_network_seq_layers.select_convs(2))
    next
      case (Dense x3) note iii = this
      then show ?thesis 
      proof(cases x3) 
        case (fields name units \<phi> \<beta> \<omega>) 
        then show ?thesis using Cons 
          apply(simp add: nn_list_to_matrix_def, safe) 
          subgoal 
            unfolding nn_list_to_matrix_def nn_list_to_matrix_def
            apply(simp add: i Cons iii dim_col_list dim_col_mat_of_row_list dim_row_mat_of_row_list 
                nn_list_to_matrix_def)
            by (smt (verit, ccfv_SIG) activation_list_to_matrix_def list.set_sel(1) list.size(3) not_less_iff_gr_or_eq o_def option.map(2)) 
          subgoal    
            unfolding nn_list_to_matrix_def nn_list_to_matrix_def
            apply(simp add: i Cons iii dim_col_list dim_col_mat_of_row_list dim_row_mat_of_row_list 
                nn_list_to_matrix_def) 
            by (metis  layers_consistent\<^sub>l_activation_tab_const layers_consistent\<^sub>m_activation_tab_const 
                neural_network_seq_layers.select_convs(2)) 
          done 
      qed
    next
      case (Activation x4) note iii = this
      then show ?thesis using Cons 
        apply(simp add: nn_list_to_matrix_def) 
        unfolding nn_list_to_matrix_def nn_list_to_matrix_def
        apply(simp add: i  iii dim_col_list dim_col_mat_of_row_list dim_row_mat_of_row_list 
            nn_list_to_matrix_def) 
        by (metis (mono_tags, lifting) activation_list_to_matrix_def layers_consistent\<^sub>l_activation_tab_const 
            layers_consistent\<^sub>m_activation_tab_const neural_network_seq_layers.select_convs(2) o_def option.map(2)) 
    qed
  qed
qed

lemma  in_deg_seq_l_eq_m: \<open>in_deg_NN N = (in_deg_NN (nn_list_to_matrix N))\<close>
proof(cases "layers N")
  case Nil
  then show ?thesis 
    unfolding in_deg_NN_def nn_list_to_matrix_def by simp
next
  case (Cons a list)
  then show ?thesis 
    unfolding in_deg_NN_def nn_list_to_matrix_def o_def 
    by(cases a, auto split:if_splits)
qed

lemma is_In_seq_m_eq_l:
  assumes \<open>(layers N) \<noteq> []\<close> 
  shows \<open>isIn (List.hd (layers N)) = isIn (List.hd (layers (nn_matrix_to_list N)))\<close>
proof(cases "N")
  case (fields layers activation_tab)
  then show ?thesis  
  proof(insert assms, cases layers)
    case Nil
    then show ?thesis using assms unfolding fields by simp  
  next
    case (Cons a list)
    then show ?thesis 
      using assms fields
      unfolding nn_matrix_to_list_def  
      by(cases a, simp_all)
  qed 
qed

lemma is_Out_seq_m_eq_l:
  assumes \<open>(layers N) \<noteq> []\<close> 
  shows \<open>isOut (last (layers N)) = isOut (last (layers (nn_matrix_to_list N)))\<close>
proof(cases "N")
  case (fields layers activation_tab) note i = this
  then show ?thesis unfolding fields 
  proof(insert assms[simplified fields], induction layers)
    case Nil
    then show ?case by simp 
  next
    case (Cons a layers)
    then show ?case 
      unfolding nn_matrix_to_list_def  
      by(cases a, simp_all)    
  qed
qed

lemma is_Internal_seq_m_eq_l:
  assumes \<open>(layers N) \<noteq> []\<close> 
  shows \<open>list_all isInternal ((List.tl o butlast) (layers N)) = list_all isInternal ((List.tl o butlast) (layers (nn_matrix_to_list N)))\<close>
proof(cases "N")
  case (fields layers activation_tab) note i = this
  then show ?thesis unfolding fields
  proof(insert assms[simplified fields], induction layers)
    case Nil
    then show ?case using Cons unfolding nn_matrix_to_list_def by simp 
  next
    case (Cons x xs)
    then show ?case
    proof(induction xs)
      case Nil
      then show ?case using Cons unfolding nn_matrix_to_list_def by simp 
    next
      case (Cons a xs)
      then show ?case using Cons unfolding nn_matrix_to_list_def by (cases a, auto split:if_splits) 
    qed
  qed
qed

lemma valid_activation_tab_seq_m_imp_l:
  \<open>valid_activation_tab\<^sub>m (activation_tab N) \<Longrightarrow>  valid_activation_tab\<^sub>l (activation_tab (nn_matrix_to_list N))\<close>
  unfolding valid_activation_tab\<^sub>l_def valid_activation_tab\<^sub>m_def nn_matrix_to_list_def activation_matrix_to_list_def o_def
  by (simp, smt (verit, del_insts) length_list_of_vec list_vec map_option_eq_Some mem_Collect_eq ran_def) 

lemma layers_consistent_seq_m_imp_l:
  assumes \<open>layers_consistent\<^sub>m N n  (layers N)\<close>
  shows \<open>  layers_consistent\<^sub>l (nn_matrix_to_list N) n  (layers (nn_matrix_to_list N)) \<close>
proof(cases "N")
  case (fields layers activation_tab) note i = this
  then show ?thesis 
    unfolding fields nn_matrix_to_list_def activation_matrix_to_list_def
  proof(insert assms[simplified fields], induction "layers" arbitrary:n activation_tab)
    case Nil
    then show ?case   
      unfolding nn_matrix_to_list_def valid_activation_tab\<^sub>l_def valid_activation_tab\<^sub>m_def activation_matrix_to_list_def o_def
      by simp   next
    case (Cons a layers) note ii = this
    then show ?case proof(cases "a") 
      case (In x1) note iii = this
      then show ?thesis using Cons   
        unfolding nn_matrix_to_list_def valid_activation_tab\<^sub>l_def valid_activation_tab\<^sub>m_def activation_matrix_to_list_def o_def
        by (simp, metis (mono_tags, lifting) layers_consistent\<^sub>l_activation_tab_const
            layers_consistent\<^sub>m_activation_tab_const neural_network_seq_layers.select_convs(2))
    next
      case (Out x2)
      then show ?thesis using Cons
        unfolding nn_matrix_to_list_def valid_activation_tab\<^sub>l_def valid_activation_tab\<^sub>m_def activation_matrix_to_list_def o_def
        by (simp, metis (mono_tags, lifting) layers_consistent\<^sub>l_activation_tab_const 
            layers_consistent\<^sub>m_activation_tab_const neural_network_seq_layers.select_convs(2))
    next
      case (Dense x3) note iii = this
      then show ?thesis 
      proof(cases x3) 
        case (fields name units \<phi> \<beta> \<omega>) 
        then show ?thesis using Cons
          apply(simp add: nn_matrix_to_list_def, safe) 
          subgoal 
            unfolding nn_matrix_to_list_def nn_matrix_to_list_def
            apply(simp add: i ii iii dim_col_list dim_col_mat_of_row_list dim_row_mat_of_row_list 
                nn_matrix_to_list_def) 
            by (metis dim_row_list index_transpose_mat(2))
          subgoal    
            unfolding nn_matrix_to_list_def nn_matrix_to_list_def
            apply(simp add: i ii iii dim_col_list dim_col_mat_of_row_list dim_row_mat_of_row_list 
                nn_matrix_to_list_def) 
            by (metis layers_consistent\<^sub>l_activation_tab_const layers_consistent\<^sub>m_activation_tab_const 
                neural_network_seq_layers.select_convs(2)) 
          done 
      qed
    next
      case (Activation x4) note iii = this
      then show ?thesis  using Cons
        apply(simp add: nn_matrix_to_list_def) 
        unfolding nn_matrix_to_list_def nn_matrix_to_list_def
        apply(simp add: i ii iii dim_col_list dim_col_mat_of_row_list dim_row_mat_of_row_list 
            nn_matrix_to_list_def) 
        by (metis layers_consistent\<^sub>l_activation_tab_const layers_consistent\<^sub>m_activation_tab_const 
            neural_network_seq_layers.select_convs(2))
    qed
  qed
qed

lemma  in_deg_seq_m_eq_l: \<open>in_deg_NN N = (in_deg_NN (nn_matrix_to_list N))\<close>
proof(cases "layers N")
  case Nil
  then show ?thesis 
    unfolding in_deg_NN_def nn_matrix_to_list_def by simp
next
  case (Cons a list)
  then show ?thesis 
    unfolding in_deg_NN_def nn_matrix_to_list_def o_def 
    by(cases a, auto split:if_splits)
qed

theorem neural_network_sequential_l_m: 
  \<open>neural_network_sequential_layers\<^sub>l N \<Longrightarrow> neural_network_sequential_layers\<^sub>m (nn_list_to_matrix N)\<close>
  unfolding neural_network_sequential_layers\<^sub>l_def neural_network_sequential_layers\<^sub>m_def
  apply(safe)[1]
  subgoal by (metis hd_Nil_eq_last isIn.elims(2) isOut.simps(2) is_In_seq_l_eq_m) 
  subgoal by (metis hd_Nil_eq_last isIn.elims(2) isOut.simps(2) is_Out_seq_l_eq_m) 
  subgoal by (metis hd_Nil_eq_last isIn.elims(2) isOut.simps(2) is_Internal_seq_l_eq_m) 
  subgoal using valid_activation_tab_seq_l_imp_m by blast
  subgoal using layers_consistent_seq_l_imp_m in_deg_seq_l_eq_m by metis
  done 

theorem neural_network_sequential_m_l: 
  \<open>neural_network_sequential_layers\<^sub>m N \<Longrightarrow> neural_network_sequential_layers\<^sub>l (nn_matrix_to_list N)\<close>
  unfolding neural_network_sequential_layers\<^sub>l_def neural_network_sequential_layers\<^sub>m_def
  apply(safe)[1]
  subgoal by (metis hd_Nil_eq_last isIn.elims(2) isOut.simps(2) is_In_seq_m_eq_l)
  subgoal by (metis hd_Nil_eq_last isIn.elims(2) isOut.simps(2) is_Out_seq_m_eq_l) 
  subgoal by (metis hd_Nil_eq_last isIn.elims(2) isOut.simps(2) is_Internal_seq_m_eq_l) 
  subgoal using valid_activation_tab_seq_m_imp_l by blast
  subgoal using layers_consistent_seq_m_imp_l in_deg_seq_m_eq_l by metis
  done 

lemma matrix_list_inverse:
  assumes \<open>layers_consistent\<^sub>l N n (layers N)\<close> 
  shows \<open>nn_matrix_to_list (nn_list_to_matrix N) = N\<close>
proof(cases "N") 
  case (fields layers activation_tab) note i = this
  then show ?thesis 
    unfolding nn_matrix_to_list_def nn_list_to_matrix_def 
    apply(simp add: o_def activation_list_inverse')
    using assms layers_consistent\<^sub>lAll layer_list_matrix_inverse
    by (metis (no_types, lifting) list.map_ident_strong neural_network_seq_layers.select_convs(1)) 
qed  


lemma list_matrix_inverse:
  assumes \<open>layers_consistent\<^sub>m N n (layers N)\<close> 
  shows \<open>nn_list_to_matrix (nn_matrix_to_list N) = N\<close>
proof(cases "N") 
  case (fields layers activation_tab) note i = this
  then show ?thesis 
    unfolding nn_matrix_to_list_def nn_list_to_matrix_def 
    apply(simp add: o_def activation_matrix_inverse')
    using assms layers_consistent\<^sub>mAll 
    by (metis (no_types, lifting) layer_list_list_inverse list.map_ident_strong neural_network_seq_layers.select_convs(1)) 
qed  

lemma square_nth_nth_id:\<open>
    \<forall> w \<in> set ws. length w = length ws \<Longrightarrow>
    (map (\<lambda>i. (map (\<lambda>ia. ws ! i ! ia ) [0..<length ws])) [0..<length ws]) = ws
\<close> 
  by (smt (verit, del_insts) in_set_conv_nth length_map map_cong map_nth nth_map) 

lemma nth_map_f: \<open>map ((\<lambda> i. f(xs ! i))) [0..<length xs] = map f xs\<close>
  by (smt (verit) add_0 diff_zero length_map map_upt_eqI nth_map) 


lemma square_nth_nth_id_f:\<open>
    \<forall> w \<in> set ws. length w = length ws \<Longrightarrow>
    (map (\<lambda>i. (map (\<lambda>ia. f (ws ! i ! ia) ) [0..<length ws])) [0..<length ws]) = map (map f) ws\<close> 
  using add_0 diff_zero length_map map_upt_eqI nth_map map_eq_conv map_nth nth_map_f[of "map f" ws] square_nth_nth_id[of ws]
  by(smt)

lemma F:\<open> length (ws::'a::{comm_ring} list) = length Inputs \<Longrightarrow> map (\<lambda>ia. ws ! ia * Inputs ! ia) [0..<length Inputs] = map2 (*) Inputs ws\<close>
  by (simp add: map_equality_iff mult.commute) 

lemma list_singleton: \<open>length xs = 1 \<Longrightarrow> \<exists> e. xs = [e] \<close>
  by (simp add: length_Suc_conv) 


lemma activation_list_to_matrix_eq:
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some (vs::'a::comm_ring list)) (Activation pl) = 
    map_option list_of_vec (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) ((layer_list_to_matrix (Activation pl)))) \<close>
  unfolding nn_list_to_matrix_def activation_list_to_matrix_def  
  by(auto simp add: vec_list list_vec split:option.split)

lemma layers_matrix_to_list: 
  \<open>(layers (nn_matrix_to_list N)) = map layer_matrix_to_list (layers N)\<close>
  unfolding nn_matrix_to_list_def 
  by(simp)

lemma layers_list_to_matrix: 
  \<open>(layers (nn_list_to_matrix N)) = map layer_list_to_matrix (layers N)\<close>
  unfolding nn_list_to_matrix_def 
  by(simp)

lemma layers_list_to_matrix': 
  \<open>layers N = l#ls \<Longrightarrow> (layers (nn_list_to_matrix N)) = (layer_list_to_matrix l)#(map layer_list_to_matrix ls)\<close>
  unfolding nn_list_to_matrix_def 
  by(simp)

lemma layers_list_to_matrix'':
  \<open>(layers (nn_list_to_matrix \<lparr>layers = l # ls, activation_tab = a\<rparr>)) = ((layer_list_to_matrix l)#(map layer_list_to_matrix ls))\<close>
  by (simp add: layers_list_to_matrix') 

lemma layers_list_to_matrix_none: 
  \<open>activation_tab N p = None \<Longrightarrow> (activation_tab (nn_list_to_matrix N)) p  = None\<close>
  unfolding nn_list_to_matrix_def activation_list_to_matrix_def o_def
  by(simp)

lemma layers_list_to_matrix_some: 
  \<open>activation_tab N p = Some f \<Longrightarrow> (activation_tab (nn_list_to_matrix N)) p  = Some (\<lambda>x. vec_of_list (f (list_of_vec x))) \<close>
  unfolding nn_list_to_matrix_def activation_list_to_matrix_def o_def
  by(simp)

lemma activation_list_to_matrix: 
  \<open>(activation_tab (nn_list_to_matrix N))  = (activation_list_to_matrix (activation_tab N)) \<close>
  unfolding nn_list_to_matrix_def activation_list_to_matrix_def o_def
  by(simp)

lemma vec_add_list: 
  assumes \<open>dim_vec M = length bs\<close>
  shows \<open>M + vec_of_list bs = vec_of_list (map2 (+) (list_of_vec M) bs)\<close>
  using assms unfolding plus_vec_def
  apply(simp) 
  by (smt (verit, del_insts) dim_vec dim_vec_of_list eq_vecI index_add_vec(1) index_add_vec(2) index_vec vec_add_list' vec_list vec_of_list_map)

lemma vec_add_list': 
  assumes \<open>dim_vec M = dim_vec bs\<close>
  shows \<open>M + bs = vec_of_list (map2 (+) (list_of_vec M) (list_of_vec bs))\<close>
  using assms unfolding plus_vec_def
  apply(simp) 
  by (smt (verit, del_insts) dim_vec dim_vec_of_list eq_vecI index_add_vec(1) index_add_vec(2) index_vec vec_add_list' vec_list vec_of_list_map)


lemma list_of_vec_map':
  \<open>v = vec_of_list (map ((vec_index) v) [0..<dim_vec v])\<close>
  by (metis list_of_vec_map vec_list) 

lemma mat_list_transpose: 
  assumes \<open>0 < dim_row M\<close> and \<open>0 < dim_col M\<close>  
  shows \<open>(mat_to_list M\<^sup>T) = List.transpose (mat_to_list M)\<close>
  using assms 
  unfolding transpose_mat_def mat_to_list_def 
  apply(simp)
  unfolding index_mat_def o_def map_fun_def id_def mat_def mk_mat_def
  apply(subst Abs_mat_inverse)
  unfolding mk_mat_def apply(blast)
  by(subst transpose_rectangle, auto)

lemma dim_row_mat_not_zero:
  assumes \<open>dim_row M \<noteq> 0\<close> 
  shows \<open>mat_to_list M \<noteq> []\<close>
  by (metis assms dim_row_list list.size(3)) 

lemma map2_to_map_idx_eq: \<open>length xs = length ys \<Longrightarrow> (map2 (*) xs (ys)) = map (\<lambda> i. xs!i * ys!i) [0..< length xs]\<close>
  using map2_map_map map_nth
  by metis 

lemma map2_to_map_idx: \<open>(map2 (*) xs (ys)) = map (\<lambda> i. xs!i * ys!i) [0..< min (length xs) (length ys)]\<close>
  by (rule nth_equalityI, auto)

lemma length_list_transpose_mat: \<open>0 < dim_row M \<Longrightarrow> 0 < dim_col M  \<Longrightarrow> length (List.transpose (mat_to_list M)) = dim_col M\<close>
  apply(simp only: mat_list_transpose[symmetric] dim_row_list[symmetric])
  by simp

lemma map_sum_list_idx: \<open>
   map (\<lambda>m. sum_list (map2 (*) m (list_of_vec v))) (List.transpose (mat_to_list M))
 = map (\<lambda>i. sum_list (map2 (*) ((List.transpose (mat_to_list M))!i) (list_of_vec v))) [0..<length (List.transpose (mat_to_list M))]\<close>
  by (smt (verit, best) map_cong nth_map_f) 

lemma  vec_mult_mat_list: 
  assumes \<open>\<forall>as\<in>set (mat_to_list M). length as = dim_col M\<close>
    and \<open>dim_vec v = dim_row M\<close>
    and \<open>dim_col M \<noteq> 0\<close> 
    and \<open>dim_row M \<noteq> 0\<close> 
  shows \<open>  (v::'a::comm_ring vec)  \<^sub>v* M = vec_of_list (map (\<lambda>m. sum_list (map2 (*) m (list_of_vec v))) (mat_to_list M\<^sup>T))\<close>
  apply(insert dim_row_mat_not_zero[of M])
  apply(rule list_of_vec_ext)
  apply(subst vec_list[of v, symmetric])
  apply(subst list_mat[of M, symmetric])
  unfolding mult_vec_mat_def scalar_prod_def
  apply(simp only:vec_of_list_index)
  apply(simp only:vec_list)
  apply(subst col_of_rows_list')
  using assms apply(simp)
  using assms apply(simp)

  unfolding sum_def
  apply(subst comm_monoid_list_set.distinct_set_conv_list[of "(+)" "0" "[0..<dim_vec v]", simplified])
  using sum.comm_monoid_list_set_axioms apply blast
  apply(simp only:sum_list_def[symmetric])
  apply(simp only: list_vec)
  apply(simp only:vec_of_list_index)
  apply(simp add:dim_col_mat_of_row_list)
  using  assms dim_row_list  length_0_conv  
  apply(simp only: map_sum_list_idx)
  apply(subst  map2_to_map_idx)

  apply (rule nth_equalityI)
   apply (simp add: mat_to_list_def)

  apply(simp only: mat_list_transpose)
  using assms length_list_transpose_mat[of M] nth_transpose[of _ "(mat_to_list M)", simplified]
  apply(simp)
  by (simp add: dim_row_list) 

lemma hd_length_inputs: \<open>0 < units x3 \<Longrightarrow>
    length (\<beta> x3) = units x3 \<Longrightarrow> length (\<omega> x3) = units x3 \<Longrightarrow> \<forall>r\<in>set (\<omega> x3). length r = length Inputs \<Longrightarrow> length Inputs = length (List.hd (\<omega> x3))\<close>
  by (metis length_greater_0_conv list.set_sel(1)) 


subsection\<open>Semantic Equivalence of List-based and Matrix-based Models\<close>
lemma In_l_to_m_eq:
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (In l)  = map_option list_of_vec (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) (layer_list_to_matrix (In l)))\<close> 
  by(simp add:list_vec)

lemma In_l_to_m_eq':
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) (layer_list_to_matrix (In l)) = map_option vec_of_list  (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (In l)) \<close> 
  by(simp add:list_vec)

lemma Out_l_to_m_eq:
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (Out l) = map_option list_of_vec (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) (layer_list_to_matrix (Out l)))\<close> 
  by(simp add:list_vec)

lemma Out_l_to_m_eq':
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) (layer_list_to_matrix (Out l)) = map_option vec_of_list (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (Out l))\<close> 
  by(simp add:list_vec)

lemma Dense_l_to_m_eq:
  assumes \<open>layer_consistent\<^sub>l N (length vs) (Dense l)\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some (vs::'a::comm_ring list)) (Dense l) 
    = map_option list_of_vec (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) (layer_list_to_matrix (Dense l)))\<close> 
proof(cases " activation_tab N (\<phi> l) = None")
  case True
  then show ?thesis by(auto simp add: nn_list_to_matrix_def activation_list_to_matrix_def o_def )
next
  case False
  then show ?thesis 
    using assms
    apply(simp add: nn_list_to_matrix_def activation_list_to_matrix_def o_def)[1]
    apply (simp add: dim_mult_vec_mat dim_row_mat_of_row_list) 
    apply(subst vec_mult_mat_list)
    subgoal by(simp add: dim_col_list)
    subgoal by (simp add: dim_col_mat_of_row_list hd_length_inputs) 
    subgoal by(simp add: dim_row_mat_of_row_list)
    subgoal by(simp add: dim_col_mat_of_row_list, metis gr_implies_not0 hd_in_set length_0_conv)
    subgoal apply(clarsimp simp add:list_vec)
      subgoal apply(subst mat_list)
        subgoal by(metis length_greater_0_conv list.set_sel(1))
        subgoal using list_vec map2_mult_commute map_eq_conv vec_of_list_map 
          apply(clarsimp simp add:o_def)  
          using Matrix_Utils.vec_add_list length_map map2_mult_commute map_eq_conv vec_of_list_map        
          by (smt (verit) dim_col_mat_of_row_list hd_length_inputs) 
        done          
      done 
    done
qed

lemma Dense_l_to_m_eq':
  assumes \<open>layer_consistent\<^sub>l N (length vs) (Dense l)\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) (layer_list_to_matrix (Dense l))
       = map_option vec_of_list (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some (vs::'a::comm_ring list)) (Dense l))\<close> 
  using Dense_l_to_m_eq
  by (smt (verit) assms not_Some_eq option.simps(8) option.simps(9) vec_list) 




lemma Activation_l_to_m_eq:
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (Activation l) 
 = map_option list_of_vec (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) (layer_list_to_matrix (Activation l)))\<close> 
proof(cases " activation_tab N (\<phi> l) = None")
  case True
  then show ?thesis by(auto simp add: nn_list_to_matrix_def activation_list_to_matrix_def o_def )
next
  case False
  then show ?thesis 
    apply(simp add:list_vec nn_list_to_matrix_def activation_list_to_matrix_def)
    by(simp add: vec_list list_vec split:option.splits)
qed

lemma Activation_l_to_m_eq':
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix N) (Some (vec_of_list vs)) (layer_list_to_matrix (Activation l))
 = map_option vec_of_list (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l N (Some vs) (Activation l))\<close>
  by (smt (verit, del_insts) Activation_l_to_m_eq option.exhaust_sel option.map_disc_iff option.map_sel vec_list) 


lemma aux1: \<open>
\<And>y. l = Dense x3 \<Longrightarrow>
         (\<And>Inputs.
             layers_consistent\<^sub>l \<lparr>layers = l0, activation_tab = activation_tab'\<rparr> (length Inputs) layers' \<Longrightarrow>
             foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = l1, activation_tab = activation_tab'\<rparr>) (Some Inputs) layers' =
             map_option list_of_vec (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix \<lparr>layers = l2, activation_tab = activation_tab'\<rparr>)) (Some (vec_of_list Inputs)) (layers (nn_list_to_matrix \<lparr>layers = layers', activation_tab = a2\<rparr>)))) \<Longrightarrow>
         valid_activation_tab\<^sub>l activation_tab' \<Longrightarrow>
         0 < units x3 \<Longrightarrow>
         Inputs \<noteq> [] \<Longrightarrow>
         length (LayerRecord.\<beta> x3) = units x3 \<Longrightarrow>
         length (LayerRecord.\<omega> x3) = units x3 \<Longrightarrow>
         \<forall>r\<in>set (LayerRecord.\<omega> x3). length r = length Inputs \<Longrightarrow>
         layers_consistent\<^sub>l \<lparr>layers = l0, activation_tab = activation_tab'\<rparr> (units x3) layers' \<Longrightarrow>
         activation_tab' (ActivationRecord.\<phi> x3) = Some y \<Longrightarrow>
         foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = l1, activation_tab = activation_tab'\<rparr>) (Some (y (map2 (+) (map ((\<lambda>vs'. \<Sum>(x, y)\<leftarrow>vs'. x * y) \<circ> zip Inputs) (LayerRecord.\<omega> x3)) (LayerRecord.\<beta> x3)))) layers' =
         map_option list_of_vec
          (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix \<lparr>layers = l2, activation_tab = activation_tab'\<rparr>)) (Some (vec_of_list (y (map2 (+) (map ((\<lambda>vs'. \<Sum>(x, y)\<leftarrow>vs'. x * y) \<circ> zip Inputs) (LayerRecord.\<omega> x3)) (LayerRecord.\<beta> x3)))))
            (map layer_list_to_matrix layers')) \<close>
    proof -
      fix y :: "'a list \<Rightarrow> 'a list"
      assume a1: "valid_activation_tab\<^sub>l activation_tab'"
      assume a2: "length (\<beta> x3) = units x3"
      assume a3: "length (\<omega> x3) = units x3"
      assume a4: "activation_tab' (\<phi> x3) = Some y"
      assume a5: "layers_consistent\<^sub>l \<lparr>layers = l0, activation_tab = activation_tab'\<rparr> (units x3) layers'"
      assume a6: "\<And>Inputs. layers_consistent\<^sub>l \<lparr>layers = l0, activation_tab = activation_tab'\<rparr> (length Inputs) layers' 
      \<Longrightarrow> foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = l1, activation_tab = activation_tab'\<rparr>) (Some Inputs) layers' = map_option list_of_vec (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix \<lparr>layers = l2, activation_tab = activation_tab'\<rparr>)) (Some (vec_of_list Inputs)) (layers (nn_list_to_matrix \<lparr>layers = layers', activation_tab = a2\<rparr>)))"
      have "\<And>as. length (y as) = length as"
        using a4 a1 by (metis (no_types) NN_Layers_List_Main.valid_activation_preserves_length)
      then show "foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = l1, activation_tab = activation_tab'\<rparr>) (Some (y (map2 (+) (map ((\<lambda>ps. \<Sum>(x, y)\<leftarrow>ps. x * y) \<circ> zip Inputs) (\<omega> x3)) (\<beta> x3)))) layers' = map_option list_of_vec (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix \<lparr>layers = l2, activation_tab = activation_tab'\<rparr>)) (Some (vec_of_list (y (map2 (+) (map ((\<lambda>ps. \<Sum>(x, y)\<leftarrow>ps. x * y) \<circ> zip Inputs) (\<omega> x3)) (\<beta> x3))))) (map layer_list_to_matrix layers'))"
        using a6 a5 a3 a2 by (simp add: nn_list_to_matrix_def)
    qed

lemma precdict_seq_l_eq_m':
  assumes \<open>layers_consistent\<^sub>l \<lparr>layers = l0, activation_tab = activation_tab'\<rparr> (length (Inputs::'a::comm_ring list)) layers'\<close>
    and \<open>valid_activation_tab\<^sub>l activation_tab'\<close>
  shows \<open>foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l \<lparr>layers = l1, activation_tab = activation_tab'\<rparr>) (Some (Inputs)) (layers \<lparr>layers = layers', activation_tab =a1\<rparr>) =
    map_option list_of_vec
     (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m (nn_list_to_matrix \<lparr>layers = l2, activation_tab = activation_tab'\<rparr>)) (Some (vec_of_list Inputs))
       (layers (nn_list_to_matrix \<lparr>layers = layers', activation_tab = a2\<rparr>)))\<close>
proof(insert assms, induction "layers'" arbitrary: Inputs)
  case Nil then show ?case 
    unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def 
      nn_list_to_matrix_def o_def activation_list_to_matrix_def in_deg_NN_def
    by(simp add:list_vec)
next
  case (Cons l layers')
  then show ?case 
  proof(cases l)
    case (In x1)      
    then show ?thesis
      apply(simp add:Cons)
      using Cons
      by ( simp add: layers_list_to_matrix list_vec  fold_predict_l_strict fold_predict_m_strict)
  next
    case (Out x2)
    then show ?thesis
      using Cons
      by ( simp add: layers_list_to_matrix list_vec  fold_predict_l_strict fold_predict_m_strict)
  next
    case (Dense x3) note i = this
    then show ?thesis 
      apply(predict_layer add:layers_list_to_matrix)
      apply(subst Dense_l_to_m_eq')
      using Cons.prems(1) layers_consistent\<^sub>l.simps(2) apply(simp)  
      using Cons.IH  Cons.prems(1) assms(2) 
      apply(simp) 
      using aux1  
      by (smt (verit) F NN_Layers_List_Main.valid_activation_preserves_length layers_list_to_matrix length_map length_upt list.map_comp
          neural_network_seq_layers.simps(1) option.simps(5,9) verit_minus_simplify(2))
  next
    case (Activation x4)
    then show ?thesis 
      apply(predict_layer add:layers_list_to_matrix)
      apply(subst Activation_l_to_m_eq')
      using Cons.IH Cons.prems(1) assms(2) 
      apply(simp)
      by (metis (mono_tags, lifting) NN_Layers_List_Main.valid_activation_preserves_length layers_list_to_matrix
          neural_network_seq_layers.select_convs(1) option.simps(5,9))
  qed
qed


theorem precdict_seq_l_eq_m:
  assumes \<open>layers_consistent\<^sub>l N (length Inputs) (layers N)\<close> 
    and \<open>valid_activation_tab\<^sub>l (activation_tab N)\<close>
  shows \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l  N (Inputs::'a::comm_ring list) = predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m' (nn_list_to_matrix N) Inputs\<close>
proof(cases "N")
  case (fields layers activation_tab)
  then show ?thesis 
    using assms
    apply(simp)
    unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def
    by(subst precdict_seq_l_eq_m', simp_all)
qed

lemma In_m_to_l_eq:
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (In l)  = map_option vec_of_list (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list N) (Some (list_of_vec vs)) (layer_matrix_to_list (In l)))\<close> 
  by(simp add:vec_list)

lemma In_m_to_l_eq':
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list N) (Some (list_of_vec vs)) (layer_matrix_to_list (In l)) = map_option list_of_vec  (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (In l)) \<close> 
  by(simp add:vec_list)

lemma Out_m_to_l_eq:
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (Out l)  = map_option vec_of_list (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list N) (Some (list_of_vec vs)) (layer_matrix_to_list (Out l)))\<close> 
  by(simp add:vec_list)

lemma Out_m_to_l_eq':
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list N) (Some (list_of_vec vs)) (layer_matrix_to_list (In l)) = map_option list_of_vec  (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (Out l)) \<close> 
  by(simp add:vec_list)

lemma Dense_m_to_l_eq:
  assumes \<open>layer_consistent\<^sub>m N (dim_vec vs) (Dense l)\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some (vs::'a::comm_ring Matrix.vec)) (Dense l) 
    = map_option vec_of_list (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list N) (Some (list_of_vec vs)) (layer_matrix_to_list (Dense l)))\<close> 
proof(cases " activation_tab N (\<phi> l) = None")
  case True
  then show ?thesis by(auto simp add: nn_matrix_to_list_def activation_matrix_to_list_def o_def )
next
  case False
  then show ?thesis 
    apply(clarsimp simp add: nn_matrix_to_list_def activation_matrix_to_list_def o_def)[1]
    subgoal using assms
      apply(simp add: nn_matrix_to_list_def activation_matrix_to_list_def o_def)[1]
      apply(subst vec_add_list')
       apply (simp add: dim_mult_vec_mat dim_row_mat_of_row_list) 
      apply(simp)
      apply(subst vec_mult_mat_list)
      subgoal by(simp add: dim_col_list)
      subgoal by(simp add: dim_col_mat_of_row_list hd_length_inputs)
      subgoal by(simp add: dim_row_mat_of_row_list)
      subgoal by(auto simp add: dim_col_mat_of_row_list)
      subgoal apply(simp add:list_vec map2_mult_commute vec_list list_mat_transpose_transpose)         
        by (smt (z3) Matrix_Utils.vec_add_list dim_col_mat_list dim_vec_of_list index_map_vec(2) index_transpose_mat(3)
            length_list_transpose_mat mat_list_transpose nat_neq_iff vec_list vec_of_dim_0 vec_of_list_map zero_vec_zero)  
      done
    done 
qed

lemma Dense_m_to_l_eq':
  assumes \<open>layer_consistent\<^sub>m N (dim_vec vs) (Dense l)\<close>
  shows \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list N) (Some (list_of_vec vs)) (layer_matrix_to_list (Dense l))
       = map_option list_of_vec (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some (vs::'a::comm_ring Matrix.vec)) (Dense l))\<close> 
  using Dense_m_to_l_eq
  by (smt (verit) assms not_Some_eq option.simps(8) option.simps(9) list_vec) 

lemma Activation_m_to_l_eq:
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (Activation l) 
 = map_option vec_of_list (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list N) (Some (list_of_vec vs)) (layer_matrix_to_list (Activation l)))\<close> 
proof(cases " activation_tab N (\<phi> l) = None")
  case True
  then show ?thesis by(auto simp add: nn_matrix_to_list_def activation_matrix_to_list_def o_def )
next
  case False
  then show ?thesis 
    apply(simp add:list_vec nn_matrix_to_list_def activation_matrix_to_list_def)
    by(simp add: vec_list list_vec split:option.splits)
qed

lemma Activation_m_to_l_eq':
  \<open>predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list N) (Some (list_of_vec vs)) (layer_matrix_to_list (Activation l))
 = map_option list_of_vec (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m N (Some vs) (Activation l))\<close>
  by (smt (verit, del_insts) Activation_m_to_l_eq option.exhaust_sel option.map_disc_iff option.map_sel list_vec) 

lemma precdict_seq_m_eq_l':
  assumes \<open>layers_consistent\<^sub>m \<lparr>layers = l0, activation_tab = activation_tab'\<rparr> (dim_vec (Inputs::'a::comm_ring Matrix.vec)) layers'\<close>
    and \<open>valid_activation_tab\<^sub>m activation_tab'\<close>
  shows \<open>foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>m \<lparr>layers = l1, activation_tab = activation_tab'\<rparr>) (Some (Inputs)) (layers \<lparr>layers = layers', activation_tab =a1\<rparr>) =
    map_option vec_of_list
     (foldl (predict\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>l (nn_matrix_to_list \<lparr>layers = l2, activation_tab = activation_tab'\<rparr>)) (Some (list_of_vec Inputs))
       (layers (nn_matrix_to_list \<lparr>layers = layers', activation_tab = a2\<rparr>)))\<close>
proof(insert assms, induction "layers'" arbitrary: Inputs a)
  case Nil then show ?case 
    unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def 
      nn_matrix_to_list_def o_def activation_matrix_to_list_def in_deg_NN_def
    by(simp add:vec_list)
next
  case (Cons l layers')
  then show ?case 
  proof(cases l)
    case (In x1)      
    then show ?thesis
      using Cons
      by (auto simp add: layers_matrix_to_list vec_list   fold_predict_l_strict fold_predict_m_strict)
  next
    case (Out x2)
    then show ?thesis
      using Cons
      by (auto simp add: layers_matrix_to_list vec_list  fold_predict_l_strict fold_predict_m_strict)
  next
    case (Dense x3) note i = this
    then show ?thesis 
      apply(predict_layer add:layers_matrix_to_list)
      apply(subst Dense_m_to_l_eq')
      using Cons.prems(1) layers_consistent\<^sub>m.simps(2) apply(simp)  
      using Cons.IH  Cons.prems(1) assms(2) 
      apply(clarsimp)[1] 
      by (metis (no_types, lifting) index_add_vec(2) layers_matrix_to_list 
          neural_network_seq_layers.select_convs(1) valid_activation_preserves_dim)
  next
    case (Activation x4)
    then show ?thesis 
      apply(predict_layer add:layers_matrix_to_list)
      apply(subst Activation_m_to_l_eq')
      using Cons.IH Cons.prems(1) assms(2) 
      apply(clarsimp)[1]
      by (metis (no_types, lifting) layers_matrix_to_list neural_network_seq_layers.select_convs(1) 
          valid_activation_preserves_dim)
  qed
qed

theorem precdict_seq_m_eq_l:
  assumes \<open>layers_consistent\<^sub>m N (length Inputs) (layers N)\<close> 
    and \<open>valid_activation_tab\<^sub>m (activation_tab N)\<close>
  shows \<open>predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'  N (Inputs::'a::comm_ring list) = predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l (nn_matrix_to_list N) Inputs\<close>
proof(cases "N")
  case (fields layers activation_tab)
  then show ?thesis 
    using assms
    apply(simp)
    unfolding predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'_def predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m_def
    apply(subst precdict_seq_m_eq_l', simp_all) 
    by (smt (verit, ccfv_threshold) assms(1) layers_consistent_seq_m_imp_l layers_matrix_to_list 
        length_list_of_vec list_matrix_inverse list_vec neural_network_seq_layers.select_convs(2) 
        nn_matrix_to_list_def precdict_seq_l_eq_m' precdict_seq_m_eq_l' valid_activation_tab_seq_m_imp_l) 
qed

corollary precdict_seq_m_eq_l2:
  assumes \<open>layers_consistent\<^sub>m N (dim_vec Inputs) (layers N)\<close> 
    and \<open>valid_activation_tab\<^sub>m (activation_tab N)\<close>
  shows \<open>map_option list_of_vec (predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m N Inputs) = predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r_\<^sub>l (nn_matrix_to_list N) (list_of_vec Inputs)\<close>
  using precdict_seq_m_eq_l predict\<^sub>s\<^sub>e\<^sub>q\<^sub>_\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>r\<^sub>_\<^sub>m'_def dim_vec_of_list 
  by (metis assms(1) assms(2) vec_list) 
end
