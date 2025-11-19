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


section \<open>Decimals of a Number\<close>

(*<*)
theory RS_Decimals
  imports Restriction_Spaces
begin
  (*>*)

typedef (overloaded) 'a :: zero decimals = \<open>{\<sigma> :: nat \<Rightarrow> 'a. \<sigma> 0 = 0}\<close>
  morphisms from_decimals to_decimals by auto

setup_lifting type_definition_decimals


declare from_decimals [simp] to_decimals_cases[simp]
  to_decimals_inject[simp] to_decimals_inverse [simp]


declare from_decimals_inject  [simp]
  from_decimals_inverse [simp]

lemmas to_decimals_inject_simplified [simp] = to_decimals_inject [simplified]
  and to_decimals_inverse_simplified[simp] = to_decimals_inverse[simplified]

(* useful ? *)
lemmas to_decimals_induct_simplified = to_decimals_induct[simplified]
  and to_decimals_cases_simplified  = to_decimals_cases [simplified]
  and from_decimals_induct_simplified = from_decimals_induct[simplified]
  and from_decimals_cases_simplified  = from_decimals_cases [simplified]



instantiation decimals :: (zero) restriction
begin

lift_definition restriction_decimals :: \<open>'a decimals \<Rightarrow> nat \<Rightarrow> 'a decimals\<close> 
  is \<open>\<lambda>\<sigma> m n. if n \<le> m then \<sigma> n else 0\<close> by simp

instance by (intro_classes, transfer, rule ext, simp)

end


instance decimals :: (zero) restriction_space
  by (intro_classes; transfer, auto)
    (metis (no_types, lifting) ext order_refl)


lemma restriction_decimals_eq_iff :
  \<open>x \<down> n = y \<down> n \<longleftrightarrow> (\<forall>i\<le>n. from_decimals x i = from_decimals y i)\<close>
  by transfer meson


lemma restriction_decimals_eqI :
  \<open>(\<And>i. i \<le> n \<Longrightarrow> from_decimals x i = from_decimals y i) \<Longrightarrow> x \<down> n = y \<down> n\<close>
  by (simp add: restriction_decimals_eq_iff)

lemma restriction_decimals_eqD :
  \<open>x \<down> n = y \<down> n \<Longrightarrow> i \<le> n \<Longrightarrow> from_decimals x i = from_decimals y i\<close>
  by (simp add: restriction_decimals_eq_iff)


text \<open>This space is actually complete.\<close>

instance decimals :: (zero) complete_restriction_space
proof (intro_classes, rule restriction_convergentI)
  fix \<sigma> :: \<open>nat \<Rightarrow> 'a decimals\<close> assume \<open>chain\<^sub>\<down> \<sigma>\<close>
  let ?\<Sigma> = \<open>to_decimals (\<lambda>n. from_decimals (\<sigma> n) n)\<close>
  have \<open>?\<Sigma> \<down> n = \<sigma> n\<close> for n
  proof (subst restricted_restriction_chain_is[OF \<open>chain\<^sub>\<down> \<sigma>\<close>, symmetric],
      rule restriction_decimals_eqI)
    fix i assume \<open>i \<le> n\<close>
    from restriction_chain_def_ter
      [THEN iffD1, OF \<open>restriction_chain \<sigma>\<close>, rule_format, OF \<open>i \<le> n\<close>]
    show \<open>from_decimals ?\<Sigma> i = from_decimals (\<sigma> n) i\<close>
      by (subst to_decimals_inverse_simplified, use from_decimals in blast)
        (metis dual_order.refl restriction_decimals.rep_eq)
  qed
  thus \<open>restriction_chain \<sigma> \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> ?\<Sigma>\<close> 
  proof -
    have \<open>(\<down>) (to_decimals (\<lambda>n. from_decimals (\<sigma> n) n)) = \<sigma>\<close>
      using \<open>\<And>n. to_decimals (\<lambda>n. from_decimals (\<sigma> n) n) \<down> n = \<sigma> n\<close> by force
    then show ?thesis
      by (metis restriction_tendsto_restrictions)
  qed
qed




typedef nat_0_9 = \<open>{0.. 9::nat}\<close>
  morphisms from_nat_0_9 to_nat_0_9 by auto


setup_lifting type_definition_nat_0_9


instantiation nat_0_9 :: zero
begin

lift_definition zero_nat_0_9 :: nat_0_9 is 0 by simp

instance ..

end

instantiation nat_0_9 :: one
begin

lift_definition one_nat_0_9 :: nat_0_9 is 1 by simp

instance ..

end


lift_definition update_nth_decimal :: \<open>[nat_0_9 decimals, nat, nat] \<Rightarrow> nat_0_9 decimals\<close>
  is \<open>\<lambda>s index value.   if index = 0 \<or> 9 < value then from_decimals s
                      else (from_decimals s)(index := to_nat_0_9 value)\<close>
  using from_decimals by auto


lemma no_update_nth_decimal [simp] :
  \<open>index = 0 \<Longrightarrow> update_nth_decimal s index val = s\<close>
  \<open>9 < val   \<Longrightarrow> update_nth_decimal s index val = s\<close>
  by (simp_all add: update_nth_decimal.abs_eq)


lemma non_destructive_update_nth_decimal : \<open>non_destructive update_nth_decimal\<close>
proof (rule non_destructiveI)
  show \<open>update_nth_decimal x \<down> n = update_nth_decimal y \<down> n\<close> if \<open>x \<down> n = y \<down> n\<close> for x y n
  proof (unfold restriction_fun_def, intro ext restriction_decimals_eqI)
    fix index val i assume \<open>i \<le> n\<close>
    from restriction_decimals_eqD[OF \<open>x \<down> n = y \<down> n\<close> \<open>i \<le> n\<close>]
    show \<open>from_decimals (update_nth_decimal x index val) i =
          from_decimals (update_nth_decimal y index val) i\<close>
      by (simp add: update_nth_decimal.rep_eq)
  qed
qed


lift_definition shift_decimal_right :: \<open>nat_0_9 decimals \<Rightarrow> nat_0_9 decimals\<close>
  is \<open>\<lambda>s n. case n of 0 \<Rightarrow> to_nat_0_9 0 | Suc n' \<Rightarrow> from_decimals s n'\<close>
  by (simp add: zero_nat_0_9_def)


lemma constructive_shift_decimal_right : \<open>constructive shift_decimal_right\<close>
proof (rule constructiveI)
  show \<open>shift_decimal_right x \<down> Suc n = shift_decimal_right y \<down> Suc n\<close> if \<open>x \<down> n = y \<down> n\<close> for x y n
  proof (intro restriction_decimals_eqI)
    fix index val i assume \<open>i \<le> Suc n\<close>
    hence \<open>i - 1 \<le> n\<close> by simp
    from restriction_decimals_eqD[OF \<open>x \<down> n = y \<down> n\<close> \<open>i - 1 \<le> n\<close>]
    show \<open>from_decimals (shift_decimal_right x) i = from_decimals (shift_decimal_right y) i\<close>
      by (simp add: shift_decimal_right.rep_eq Nitpick.case_nat_unfold)
  qed
qed


lift_definition shift_decimal_left :: \<open>nat_0_9 decimals \<Rightarrow> nat_0_9 decimals\<close>
  is \<open>\<lambda>s n. if n = 0 then to_nat_0_9 0 else from_decimals s (Suc n)\<close>
  by (simp add: zero_nat_0_9_def)

lemma non_too_destructive_shift_decimal_left : \<open>non_too_destructive shift_decimal_left\<close>
proof (rule non_too_destructiveI)
  show \<open>shift_decimal_left x \<down> n = shift_decimal_left y \<down> n\<close> if \<open>x \<down> Suc n = y \<down> Suc n\<close> for x y n
  proof (intro restriction_decimals_eqI)
    fix index val i assume \<open>i \<le> n\<close>
    hence \<open>Suc i \<le> Suc n\<close> by simp
    from restriction_decimals_eqD[OF \<open>x \<down> Suc n = y \<down> Suc n\<close> \<open>Suc i \<le> Suc n\<close>]
    show \<open>from_decimals (shift_decimal_left x) i = from_decimals (shift_decimal_left y) i\<close>
      by (simp add: shift_decimal_left.rep_eq)
  qed
qed



lemma restriction_fix_shift_decimal_right : \<open>(\<upsilon> x. shift_decimal_right x) = to_decimals (\<lambda>_. 0)\<close>
proof (rule restriction_fix_unique)
  show \<open>constructive shift_decimal_right\<close> 
    by (fact constructive_shift_decimal_right)
next
  show \<open>shift_decimal_right (to_decimals (\<lambda>_. 0)) = to_decimals (\<lambda>_. 0)\<close>
    by (simp add: shift_decimal_right.abs_eq)
      (metis nat.case_eq_if to_decimals_inverse_simplified zero_nat_0_9_def)
qed



text \<open>Example of a predicate that is not admissible.\<close>

lemma one_in_decimals_not_admissible :
  defines P_def: \<open>P \<equiv> \<lambda>x. (1 :: nat_0_9) \<in> range (from_decimals x)\<close>
  shows \<open>\<not> adm\<^sub>\<down> P\<close>
proof (rule ccontr)
  assume * : \<open>\<not> \<not> adm\<^sub>\<down> P\<close>

  define x where \<open>x \<equiv> to_decimals (\<lambda>n. if n = 0 then 0 else 1 :: nat_0_9)\<close>

  have \<open>P (\<upsilon> x. shift_decimal_right x)\<close>
  proof (induct rule: restriction_fix_ind)
    show \<open>constructive shift_decimal_right\<close> by (fact constructive_shift_decimal_right)
  next
    from "*" show \<open>adm\<^sub>\<down> P\<close> by simp
  next
    show \<open>P x\<close> by (auto simp add: P_def x_def image_iff)
  next
    show \<open>P x \<Longrightarrow> P (shift_decimal_right x)\<close> for x
      by (simp add: P_def image_def shift_decimal_right.rep_eq)
        (metis old.nat.simps(5))
  qed
  moreover have \<open>\<not> P (\<upsilon> x. shift_decimal_right x)\<close>
    by (simp add: P_def restriction_fix_shift_decimal_right)
      (transfer, simp)
  ultimately show False by blast
qed

(*<*)
end
  (*>*)