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

(*<*)
theory Restriction_Spaces
  imports Restriction_Spaces_Induction
begin
  (*>*)

section \<open>Entry Point\<close>

text \<open>This is the file \<^session>\<open>Restriction_Spaces\<close> should be imported from.\<close>

declare
  restriction_shift_introset [intro!]
  restriction_shift_simpset  [simp  ]
  restriction_cont_simpset   [simp  ]
  restriction_adm_simpset    [simp  ]





text \<open>We already have @{thm non_destructive_id(2)}, and can easily notice
      \<^term>\<open>non_destructive (\<lambda>f. f x)\<close>, but also \<^term>\<open>non_destructive (\<lambda>f. f x y)\<close>, etc.
      We add a \<^theory_text>\<open>simproc_setup\<close> to enable the simplifier to automatically handle goals
      of this form, regardless of the number of arguments on which the function is applied.\<close>


simproc_setup apply_non_destructiveness (\<open>non_destructive (\<lambda>f. E f)\<close>) = \<open>
  fn _ => fn ctxt => fn lhs =>
    (case Thm.term_of lhs of _ $ foo =>
          case foo of Abs (_, _, expr) =>
               if case strip_comb expr of (f, args) =>
                       f = Bound 0 andalso not (exists Term.is_dependent args)
                  (* since \<open>\<lambda>f. E f\<close> is too permissive, we ensure here that the term
                     is of the form \<open>\<lambda>f. f \<dots>\<close>, with \<open>f\<close> no longer appearing in \<open>\<dots>\<close> *)
               then
                 let
                   val tac = Metis_Tactic.metis_tac ["no_types"] "combs" ctxt
                              @{thms non_destructive_fun_iff non_destructive_id(2)}
                   val thm =
                     Goal.prove_internal ctxt [] \<^instantiate>\<open>lhs in cprop \<open>lhs = True\<close>\<close>
                       (fn _ => tac 1)
                 in SOME (mk_meta_eq thm) end
               else NONE
           | _ => NONE)
\<close>



lemma \<open>non_destructive (\<lambda>f. f a b c d e f' g h i j k l m n o' p q r s t u v w x y z)\<close>
  using [[simp_trace]] by simp \<comment> \<open>test\<close>


(*<*)
end
  (*>*)
