(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
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

section \<open>Non Destructiveness of Renaming\<close>

(*<*)
theory Renaming_Non_Destructive
  imports Process_Restriction_Space "HOL-CSPM"
begin
  (*>*)


subsection \<open>Equality\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming:
  \<open>Renaming P f g \<down> n = Renaming (P \<down> n) f g\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (auto simp add: Renaming_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (metis append.right_neutral ftF_Nil tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff,
        use ftF_append in blast)
next
  show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (auto simp add: Renaming_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        ftF_append tF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
next
  fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
  then obtain u where \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>
    by (simp add: Renaming_projs restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) blast
  thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (auto simp add: F_Renaming F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
  then obtain u where \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<down> n)\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>
    unfolding Renaming_projs by blast
  from \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<down> n)\<close>
  consider \<open>u \<in> \<D> (P \<down> n)\<close> | \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close>
    unfolding restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    assume \<open>u \<in> \<D> (P \<down> n)\<close>
    hence \<open>t \<in> \<D> ?rhs\<close>
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      from \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> show \<open>u \<in> \<D> P \<Longrightarrow> t \<in> \<D> ?rhs\<close>
        by (cases \<open>tF u\<close>, simp_all add: D_Renaming D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          (use ftF_Nil in blast,
            metis D_imp_ftF butlast_snoc div_butlast_when_non_tF_iff
            ftF_iff_tF_butlast ftF_single map_append
            ftF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff not_tF_and_ftF)
    next
      show \<open>\<lbrakk>u = v @ w; v \<in> \<T> P; length v = n; tF v; ftF w\<rbrakk> \<Longrightarrow> t \<in> \<D> ?rhs\<close> for v w
        by (simp add: D_Renaming D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>)
          (use ftF_Nil ftF_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff in blast)
    qed
    with \<open>t \<notin> \<D> ?rhs\<close> have False ..
    thus \<open>(t, X) \<in> \<F> ?lhs\<close> ..
  next
    show \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P \<Longrightarrow> (t, X) \<in> \<F> (Renaming P f g \<down> n)\<close>
      by (auto simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_Renaming \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>)
  qed
qed



subsection \<open>Non Destructiveness\<close>

lemma Renaming_non_destructive [simp] :
  \<open>non_destructive (\<lambda>P. Renaming P f g)\<close>
  by (auto intro: non_destructiveI simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming)


(*<*)
end
  (*>*)