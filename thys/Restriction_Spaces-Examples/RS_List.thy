(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Benjamin Puyobro, Université Paris-Saclay,
           IRT SystemX, CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
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


section \<open>Lists\<close>

(*<*)
theory RS_List
  imports Restriction_Spaces "HOL-Library.Prefix_Order"
begin
  (*>*)

text \<open>List is a restriction space using \<^const>\<open>take\<close> as the restriction function\<close>

instantiation list :: (type) restriction
begin

definition restriction_list :: \<open>'a list \<Rightarrow> nat \<Rightarrow> 'a list\<close> 
  where \<open>L \<down> n \<equiv> take n L\<close>

instance by intro_classes (simp add: restriction_list_def min.commute)

end


instance list :: (type) order_restriction_space
proof intro_classes
  show \<open>L \<down> 0 \<le> M \<down> 0\<close> for L M :: \<open>'a list\<close>
    by (simp add: restriction_list_def)
next
  show \<open>L \<le> M \<Longrightarrow> L \<down> n \<le> M \<down> n\<close> for L M :: \<open>'a list\<close> and n
    unfolding restriction_list_def
    by (metis less_eq_list_def prefix_def take_append)
next
  show \<open>\<not> L \<le> M \<Longrightarrow> \<exists>n. \<not> L \<down> n \<le> M \<down> n\<close> for M L :: \<open>'a list\<close>
    unfolding restriction_list_def
    by (metis linorder_linear take_all_iff)
qed


lemma \<open>OFCLASS('a list, restriction_space_class)\<close> ..



text \<open>Of course, this space is not complete. We prove this with by exhibiting a counter-example.\<close>

notepad begin
  define \<sigma> :: \<open>nat \<Rightarrow> 'a list\<close>
    where \<open>\<sigma> n = replicate n undefined\<close> for n

  have \<open>chain\<^sub>\<down> \<sigma>\<close>
    by (intro restriction_chainI ext)
      (simp add: \<sigma>_def restriction_list_def flip: replicate_append_same)

  hence \<open>\<nexists>\<Sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
    by (metis \<sigma>_def convergent_restriction_chain_imp_ex1 length_replicate
        lessI nat_less_le restriction_convergentI restriction_list_def take_all)

end

(*<*)
end
  (*>*)
