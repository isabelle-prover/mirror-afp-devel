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


section \<open>Naturals\<close>

(*<*)
theory RS_Nat
  imports Restriction_Spaces
begin
  (*>*)

text \<open>Restriction instance for \<^typ>\<open>nat\<close>.\<close>

instantiation nat :: restriction
begin

definition restriction_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>x \<down> n \<equiv> if x \<le> n then x else n\<close>

instance by intro_classes (simp add: restriction_nat_def)

end


lemma restriction_nat_0_is_0 [simp] : \<open>x \<down> 0 = (0 :: nat)\<close>
  by (simp add: restriction_nat_def)


text \<open>Restriction Space instance for \<^typ>\<open>nat\<close>.\<close>

instance nat :: restriction_space
  by intro_classes (use nat_le_linear in \<open>auto simp add: restriction_nat_def\<close>)



text \<open>Constructive Suc\<close>

lemma constructive_Suc : \<open>constructive Suc\<close>
proof (rule constructiveI)
  show \<open>x \<down> n = y \<down> n \<Longrightarrow> Suc x \<down> Suc n = Suc y \<down> Suc n\<close> for x y n
    by (simp add: restriction_nat_def split: if_split_asm)
qed


text \<open>Non too destructive pred\<close>

lemma non_too_destructive_pred : \<open>non_too_destructive nat.pred\<close>
proof (rule non_too_destructiveI)
  show \<open>x \<down> Suc n = y \<down> Suc n \<Longrightarrow> nat.pred x \<down> n = nat.pred y \<down> n\<close> for x y n
    by (cases x; cases y) (simp_all add: restriction_nat_def split: if_split_asm)
qed


text \<open>Restriction shift plus\<close>

lemma restriction_shift_plus : \<open>restriction_shift (\<lambda>x. x + k) (int k)\<close>
proof (intro restriction_shiftI)
  show \<open>x \<down> n = y \<down> n \<Longrightarrow> x + k \<down> nat (int n + int k) = y + k \<down> nat (int n + int k)\<close> for x y n
    by (simp add: restriction_nat_def nat_int_add split: if_split_asm)
qed

lemma \<open>restriction_shift (\<lambda>x. k + x) (int k)\<close>
  by (simp add: add.commute restriction_shift_plus)

\<comment> \<open>In particular, constructive if \<^term>\<open>1 < k\<close>.\<close>



(*<*)
end
  (*>*)
