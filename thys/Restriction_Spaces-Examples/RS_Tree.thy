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


section \<open>Binary Trees\<close>

(*<*)
theory RS_Tree
  imports Restriction_Spaces
begin
  (*>*)


datatype 'a ex_tree = tip | node \<open>'a ex_tree\<close> 'a \<open>'a ex_tree\<close>


instantiation ex_tree :: (type) restriction
begin

fun restriction_ex_tree :: \<open>'a ex_tree \<Rightarrow> nat \<Rightarrow> 'a ex_tree\<close>
  where \<open>tip \<down> n = tip\<close>
  |     \<open>(node l val r) \<down> 0 = tip\<close>
  |     \<open>(node l val r) \<down> Suc n = node (l \<down> n) val (r \<down> n)\<close>


lemma restriction_ex_tree_0_is_tip [simp] : \<open>T \<down> 0 = tip\<close>
  using restriction_ex_tree.elims by blast

instance
proof intro_classes
  show \<open>T \<down> n \<down> m = T \<down> min n m\<close> for T :: \<open>'a ex_tree\<close> and n m
  proof (induct n arbitrary: T m)
    show \<open>T \<down> 0 \<down> m = T \<down> min 0 m\<close> for T :: \<open>'a ex_tree\<close> and m by simp
  next
    fix T :: \<open>'a ex_tree\<close> and m n assume hyp : \<open>T \<down> n \<down> m = T \<down> min n m\<close> for T :: \<open>'a ex_tree\<close> and m
    show \<open>T \<down> Suc n \<down> m = T \<down> min (Suc n) m\<close>
      by (cases T; cases m, simp_all add: hyp)
  qed
qed


end


lemma size_le_imp_restriction_ex_tree_eq_self :
  \<open>size x \<le> n \<Longrightarrow> x \<down> n = x\<close> for x :: \<open>'a ex_tree\<close>
  by (induct rule: restriction_ex_tree.induct) simp_all

lemma restriction_ex_tree_eqI :
  \<open>(\<And>i. x \<down> i =  y \<down> i) \<Longrightarrow> x = y\<close> for x y :: \<open>'a ex_tree\<close>
  by (metis linorder_linear size_le_imp_restriction_ex_tree_eq_self)

lemma restriction_ex_tree_eqI_optimized :
  \<open>(\<And>i. i \<le> max (size x) (size y) \<Longrightarrow> x \<down> i =  y \<down> i) \<Longrightarrow> x = y\<close> for x y :: \<open>'a ex_tree\<close>
  by (metis max.cobounded1 max.cobounded2 order_eq_refl size_le_imp_restriction_ex_tree_eq_self)


instance ex_tree :: (type) restriction_space
  by (intro_classes, simp)
    (use restriction_ex_tree_eqI_optimized in blast)


(*<*)
end
  (*>*)