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


section \<open>Integers\<close>

(*<*)
theory RS_Int
  imports Restriction_Spaces
begin
  (*>*)

instantiation int :: restriction
begin

definition restriction_int :: \<open>int \<Rightarrow> nat \<Rightarrow> int\<close>
  where \<open>x \<down> n \<equiv> if \<bar>x\<bar> \<le> int n then x else if 0 \<le> x then int n else - int n\<close>

instance by intro_classes (simp add: restriction_int_def min_def)

end


instance int :: restriction_space
  by (intro_classes, simp_all add: restriction_int_def)
    (metis le_eq_less_or_eq linorder_not_less nat_le_iff)



lemma restriction_int_0_is_0 [simp] : \<open>x \<down> 0 = (0 :: int)\<close>
  by (simp add: restriction_int_def)


text \<open>Restriction shift plus\<close>

lemma restriction_shift_on_pos_plus : \<open>restriction_shift_on (\<lambda>x. x + k) k {x. 0 \<le> x}\<close>
  by (intro restriction_shift_onI)
    (simp add: restriction_int_def split: if_split_asm)

lemma restriction_shift_on_neg_minus : \<open>restriction_shift_on (\<lambda>x. x - k) k {x. x \<le> 0}\<close>
  by (intro restriction_shift_onI)
    (simp add: restriction_int_def split: if_split_asm)



(*<*)
end
  (*>*)
