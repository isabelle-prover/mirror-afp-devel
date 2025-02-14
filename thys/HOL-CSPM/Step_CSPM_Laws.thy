(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Step Laws
 *
 * Copyright (c) 2025 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

section\<open> The Step-Laws \<close>

(*<*)
theory Step_CSPM_Laws                                            
  imports Global_Deterministic_Choice Multi_Synchronization_Product
    Multi_Sequential_Composition Interrupt Throw
begin 
  (*>*)

text \<open>The step-laws describe the behaviour of the operators wrt. the multi-prefix choice.\<close>

subsection \<open>The Throw Operator\<close>

lemma Throw_Mprefix: 
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<Theta> b \<in> B. Q b =
    \<box>a \<in> A \<rightarrow> (if a \<in> B then Q a else P a \<Theta> b \<in> B. Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then consider t1 t2 where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> (\<box>a \<in> A \<rightarrow> P a)\<close> \<open>tF t1\<close> 
    \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
  | t1 b t2 where \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)\<close>
    \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close>
    by (simp add: D_Throw) blast
  thus \<open>s \<in> \<D> ?rhs\<close>
  proof cases
    fix t1 t2 assume * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> (\<box>a\<in>A \<rightarrow> P a)\<close> \<open>tF t1\<close> 
      \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
    from "*"(2) obtain a t1' where ** : \<open>t1 = ev a # t1'\<close> \<open>a \<in> A\<close> \<open>t1' \<in> \<D> (P a)\<close>
      by (auto simp add: D_Mprefix)
    from "*"(4) "**"(1) have *** : \<open>a \<notin> B\<close> by (simp add: image_iff)
    have \<open>t1' @ t2 \<in> \<D> (Throw (P a) B Q)\<close>
      using "*"(3, 4, 5) "**"(1, 3) by (auto simp add: D_Throw)
    with "***" show \<open>s \<in> \<D> ?rhs\<close>
      by (simp add: D_Mprefix "*"(1) "**"(1, 2))
  next
    fix t1 b t2 assume * : \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)\<close>
      \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close>
    show \<open>s \<in> \<D> ?rhs\<close>
    proof (cases \<open>t1\<close>)
      from "*"(2) show \<open>t1 = [] \<Longrightarrow> s \<in> \<D> ?rhs\<close>
        by (simp add: D_Mprefix T_Mprefix "*"(1, 4, 5))
    next
      fix a t1'
      assume \<open>t1 = a # t1'\<close>
      then obtain a' where \<open>t1 = ev a' # t1'\<close> (* a = ev a' *)
        by (metis "*"(2) append_Cons append_Nil append_T_imp_tickFree
            event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust non_tickFree_tick not_Cons_self tickFree_append_iff)
      with "*"(2, 3, 4, 5) show \<open>s \<in> \<D> ?rhs\<close>
        by (auto simp add: "*"(1) D_Mprefix T_Mprefix D_Throw)
    qed
  qed
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then obtain a s' where * : \<open>a \<in> A\<close> \<open>s = ev a # s'\<close>
    \<open>s' \<in> \<D> (if a \<in> B then Q a else Throw (P a) B Q)\<close> 
    by (auto simp add: D_Mprefix)
  show \<open>s \<in> \<D> ?lhs\<close>
  proof (cases \<open>a \<in> B\<close>)
    assume \<open>a \<in> B\<close>
    hence ** :  \<open>[] @ [ev a] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a) \<and> set [] \<inter> ev ` B = {} \<and> s' \<in> \<D> (Q a)\<close>
      using "*"(3) by (simp add: T_Mprefix "*"(1))
    show \<open>s \<in> \<D> ?lhs\<close> 
      by (simp add: D_Throw) (metis "*"(2) "**" \<open>a \<in> B\<close> append_Nil)
  next
    assume \<open>a \<notin> B\<close>
    with "*"(2, 3)
    consider t1 t2 where \<open>s = ev a # t1 @ t2\<close> \<open>t1 \<in> \<D> (P a)\<close> \<open>tF t1\<close>
      \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
    | t1 b t2 where \<open>s = ev a # t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
      \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close>
      by (simp add: D_Throw) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
    proof cases
      fix t1 t2 assume ** : \<open>s = ev a # t1 @ t2\<close> \<open>t1 \<in> \<D> (P a)\<close> \<open>tF t1\<close>
        \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
      have *** : \<open>ev a # t1 \<in> \<D> (\<box>a\<in>A \<rightarrow> P a) \<and> tickFree (ev a # t1) \<and>
                  set (ev a # t1) \<inter> ev ` B = {}\<close>
        by (simp add: D_Mprefix image_iff "*"(1) "**"(2, 3, 4) \<open>a \<notin> B\<close>)
      show \<open>s \<in> \<D> ?lhs\<close>
        by (simp add: D_Throw) (metis "**"(1, 5) "***" append_Cons)
    next
      fix t1 b t2
      assume ** :  \<open>s = ev a # t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
        \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close>
      have *** : \<open>(ev a # t1) @ [ev b] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a) \<and> set (ev a # t1) \<inter> ev ` B = {}\<close>
        by (simp add: T_Mprefix image_iff "*"(1) "**"(2, 3) \<open>a \<notin> B\<close>)
      show \<open>s \<in> \<D> ?lhs\<close>
        by (simp add: D_Throw) (metis "**"(1, 4, 5) "***" append_Cons)
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>(s, X) \<in> \<F> (\<box>a\<in>A \<rightarrow> P a)\<close> \<open>set s \<inter> ev ` B = {}\<close>
    | \<open>s \<in> \<D> ?lhs\<close>
    | t1 b t2 where \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)\<close>
      \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
    by (simp add: F_Throw D_Throw) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    show \<open>(s, X) \<in> \<F> (\<box>a\<in>A \<rightarrow> P a) \<Longrightarrow> set s \<inter> ev ` B = {} \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Mprefix F_Throw)
        (metis image_eqI insert_disjoint(1) list.simps(15))
  next
    show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      using same_div D_F by blast
  next
    fix t1 b t2 assume * : \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)\<close>
      \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
    show \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof (cases t1) 
      from "*"(2) show \<open>t1 = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Mprefix T_Mprefix F_Throw "*"(1, 4, 5))
    next
      fix a t1'
      assume \<open>t1 = a # t1'\<close>
      then obtain a' where \<open>t1 = ev a' # t1'\<close> (* a = ev a' *)
        by (metis "*"(2) append_Cons append_Nil append_T_imp_tickFree
            event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust non_tickFree_tick not_Cons_self tickFree_append_iff)
      with "*"(2, 3, 5) show \<open>(s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Mprefix T_Mprefix F_Throw "*"(1, 4))
    qed
  qed
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
  proof (cases s)
    show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Mprefix F_Throw)
  next
    fix a s'
    assume assms : \<open>s = a # s'\<close> \<open>(s, X) \<in> \<F> ?rhs\<close>
    from assms(2) obtain a'
      where * : \<open>a' \<in> A\<close> \<open>s = ev a' # s'\<close>
        \<open>(s', X) \<in> \<F> (if a' \<in> B then Q a' else Throw (P a') B Q)\<close>
      by (simp add: assms(1) F_Mprefix) blast
    show \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof (cases \<open>a' \<in> B\<close>) 
      assume \<open>a' \<in> B\<close>
      hence ** : \<open>[] @ [ev a'] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a) \<and>
                 set [] \<inter> ev ` B = {} \<and> (s', X) \<in> \<F> (Q a')\<close>
        using "*"(3) by (simp add: T_Mprefix "*"(1))
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Throw) (metis "*"(2) "**" \<open>a' \<in> B\<close> append_Nil)
    next
      assume \<open>a' \<notin> B\<close>
      then consider  \<open>(s', X) \<in> \<F> (P a')\<close> \<open>set s' \<inter> ev ` B = {}\<close>
        | t1 t2   where \<open>s' = t1 @ t2\<close> \<open>t1 \<in> \<D> (P a')\<close> \<open>tF t1\<close>
          \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
        | t1 b t2 where \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a')\<close>
          \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
        using "*"(3) by (simp add: F_Throw D_Throw) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        show \<open>(s', X) \<in> \<F> (P a') \<Longrightarrow> set s' \<inter> ev ` B = {} \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Mprefix F_Throw "*"(1, 2) \<open>a' \<notin> B\<close> image_iff)
      next
        fix t1 t2 assume ** : \<open>s' = t1 @ t2\<close> \<open>t1 \<in> \<D> (P a')\<close> \<open>tF t1\<close>
          \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
        have *** : \<open>s = (ev a' # t1) @ t2 \<and> ev a' # t1 \<in> \<D> (\<box>a\<in>A \<rightarrow> P a) \<and>
                    tickFree (ev a' # t1) \<and> set (ev a' # t1) \<inter> ev ` B = {}\<close>
          by (simp add: D_Mprefix \<open>a' \<notin> B\<close> image_iff "*"(1, 2) "**"(1, 2, 3, 4))
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Throw F_Mprefix) (metis "**"(5) "***")
      next
        fix t1 b t2
        assume ** : \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a')\<close>
          \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
        have *** : \<open>s = (ev a' # t1) @ ev b # t2 \<and> set (ev a' # t1) \<inter> ev ` B = {} \<and>
                    (ev a' # t1) @ [ev b] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)\<close>
          by (simp add: T_Mprefix \<open>a' \<notin> B\<close> image_iff "*"(1, 2) "**"(1, 2, 3))
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Throw F_Mprefix) (metis "**"(4, 5) "***")
      qed
    qed
  qed
qed



subsection \<open>The Interrupt Operator\<close>

lemma Interrupt_Mprefix:
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<triangle> Q = Q \<box> (\<box>a \<in> A \<rightarrow> P a \<triangle> Q)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then consider \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a)\<close>
    | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (\<box>a \<in> A \<rightarrow> P a) \<and> tF t1 \<and> t2 \<in> \<D> Q\<close>
    by (simp add: D_Interrupt) blast
  thus \<open>s \<in> \<D> ?rhs\<close>
  proof cases
    show \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a) \<Longrightarrow> s \<in> \<D> ?rhs\<close>
      by (auto simp add: D_Det D_Mprefix D_Interrupt)
  next
    assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (\<box>a \<in> A \<rightarrow> P a) \<and> tF t1 \<and> t2 \<in> \<D> Q\<close>
    then obtain t1 t2
      where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> (\<box>a \<in> A \<rightarrow> P a)\<close> \<open>tF t1\<close> \<open>t2 \<in> \<D> Q\<close> by blast
    thus \<open>s \<in> \<D> ?rhs\<close> by (fastforce simp add: D_Det Mprefix_projs D_Interrupt)
  qed
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then consider \<open>s \<in> \<D> Q\<close> | a s' where \<open>s = ev a # s'\<close> \<open>a \<in> A\<close> \<open>s' \<in> \<D> (P a \<triangle> Q)\<close>
    by (auto simp add: D_Det D_Mprefix image_iff)
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> ?lhs\<close>
      by (simp add: D_Interrupt) (use Nil_elem_T tickFree_Nil in blast)
  next
    fix a s' assume \<open>s = ev a # s'\<close> \<open>a \<in> A\<close> \<open>s' \<in> \<D> (P a \<triangle> Q)\<close>
    from this(3) consider \<open>s' \<in> \<D> (P a)\<close>
      | t1 t2 where \<open>s' = t1 @ t2\<close> \<open>t1 \<in> \<T> (P a)\<close> \<open>tF t1\<close> \<open>t2 \<in> \<D> Q\<close>
      by (auto simp add: D_Interrupt)
    thus \<open>s \<in> \<D> ?lhs\<close>
    proof cases
      show \<open>s' \<in> \<D> (P a) \<Longrightarrow> s \<in> \<D> ?lhs\<close>
        by (simp add: D_Interrupt D_Mprefix \<open>a \<in> A\<close> \<open>s = ev a # s'\<close>)
    next
      show \<open>\<lbrakk>s' = t1 @ t2; t1 \<in> \<T> (P a); tF t1; t2 \<in> \<D> Q\<rbrakk> \<Longrightarrow> s \<in> \<D> ?lhs\<close> for t1 t2
        by (simp add: \<open>s = ev a # s'\<close> D_Interrupt T_Mprefix)
          (metis Cons_eq_appendI \<open>a \<in> A\<close> event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close> 
    | t1 r where \<open>s = t1 @ [\<checkmark>(r)]\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> (Mprefix A P)\<close>
    | r where \<open>s @ [\<checkmark>(r)] \<in> \<T> (Mprefix A P)\<close> \<open>\<checkmark>(r) \<notin> X\<close>
    | \<open>(s, X) \<in> \<F> (Mprefix A P)\<close> \<open>tickFree s\<close> \<open>([], X) \<in> \<F> Q\<close>
    | t1 t2 where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> (Mprefix A P)\<close> \<open>tickFree t1\<close> \<open>(t2, X) \<in> \<F> Q\<close> \<open>t2 \<noteq> []\<close>
    | r where \<open>s \<in> \<T> (Mprefix A P)\<close> \<open>tickFree s\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close> \<open>\<checkmark>(r) \<notin> X\<close>
    by (simp add: F_Interrupt D_Interrupt) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    show \<open>s = t1 @ [\<checkmark>(r)] \<Longrightarrow> t1 @ [\<checkmark>(r)] \<in> \<T> (Mprefix A P) \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for t1 r
      by (simp add: F_Det T_Mprefix F_Mprefix F_Interrupt image_iff)
        (metis append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) list.inject list.sel(3) tl_append2)
  next
    show \<open>s @ [\<checkmark>(r)] \<in> \<T> (Mprefix A P) \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for r
      by (simp add: F_Det T_Mprefix F_Mprefix F_Interrupt image_iff)
        (metis (no_types, opaque_lifting) Diff_insert_absorb append_Nil
          event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) hd_append2 list.sel(1, 3) neq_Nil_conv tl_append2)
  next
    show \<open>(s, X) \<in> \<F> (Mprefix A P) \<Longrightarrow> tickFree s \<Longrightarrow> ([], X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Det F_Mprefix F_Interrupt image_iff) (metis tickFree_Cons_iff)
  next
    show \<open>s = t1 @ t2 \<Longrightarrow> t1 \<in> \<T> (Mprefix A P) \<Longrightarrow> tickFree t1 \<Longrightarrow> (t2, X) \<in> \<F> Q \<Longrightarrow>
          t2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for t1 t2
      by (simp add: F_Det T_Mprefix F_Mprefix F_Interrupt image_iff)
        (metis append_Cons append_Nil tickFree_Cons_iff)
  next
    show \<open>s \<in> \<T> (Mprefix A P) \<Longrightarrow> tickFree s \<Longrightarrow> [\<checkmark>(r)] \<in> \<T> Q \<Longrightarrow>
          \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for r
      by (simp add: F_Det T_Mprefix F_Mprefix F_Interrupt image_iff)
        (metis Diff_insert_absorb tickFree_Cons_iff)
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume assm : \<open>(s, X) \<in> \<F> ?rhs\<close>
  show \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof (cases \<open>s = []\<close>)
    from assm show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Det F_Mprefix F_Interrupt) blast
  next 
    assume \<open>s \<noteq> []\<close>
    with assm consider \<open>(s, X) \<in> \<F> Q\<close>
      | \<open>\<exists>a s'. s = ev a # s' \<and> a \<in> A \<and> (s', X) \<in> \<F> (P a \<triangle> Q)\<close>
      by (auto simp add: F_Det F_Mprefix image_iff)
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      show \<open>(s, X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Interrupt)
          (metis Nil_elem_T \<open>s \<noteq> []\<close> append_Nil tickFree_Nil)
    next
      assume \<open>\<exists>a s'. s = ev a # s' \<and> a \<in> A \<and> (s', X) \<in> \<F> (P a \<triangle> Q)\<close>
      then obtain a s'
        where * : \<open>s = ev a # s'\<close> \<open>a \<in> A\<close> \<open>(s', X) \<in> \<F> (P a \<triangle> Q)\<close> by blast
      from "*"(3) consider \<open>s' \<in> \<D> (P a \<triangle> Q)\<close>
        | t1 r where \<open>s' = t1 @ [\<checkmark>(r)]\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> (P a)\<close>
        | r where \<open>s' @ [\<checkmark>(r)] \<in> \<T> (P a)\<close> \<open>\<checkmark>(r) \<notin> X\<close>
        | \<open>(s', X) \<in> \<F> (P a)\<close> \<open>tickFree s'\<close> \<open>([], X) \<in> \<F> Q\<close>
        | t1 t2 where \<open>s' = t1 @ t2\<close> \<open>t1 \<in> \<T> (P a)\<close> \<open>tickFree t1\<close> \<open>(t2, X) \<in> \<F> Q\<close> \<open>t2 \<noteq> []\<close>
        | r where \<open>s' \<in> \<T> (P a)\<close> \<open>tickFree s'\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close> \<open>\<checkmark>(r) \<notin> X\<close>
        by (simp add: F_Interrupt D_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s' \<in> \<D> (P a \<triangle> Q)\<close>
        hence \<open>s \<in> \<D> ?lhs\<close>
          apply (simp add: D_Interrupt D_Mprefix T_Mprefix "*"(1, 2) image_iff)
          apply (elim disjE exE conjE; simp)
          by (metis "*"(2) Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
        with D_F same_div show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast 
      next
        show \<open>s' = t1 @ [\<checkmark>(r)] \<Longrightarrow> t1 @ [\<checkmark>(r)] \<in> \<T> (P a) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for t1 r
          by (simp add: "*"(1, 2) F_Interrupt T_Mprefix)
      next
        show \<open>s' @ [\<checkmark>(r)] \<in> \<T> (P a) \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for r
          by (simp add: "*"(1, 2) F_Interrupt T_Mprefix) blast
      next
        show \<open>(s', X) \<in> \<F> (P a) \<Longrightarrow> tickFree s' \<Longrightarrow> ([], X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: "*"(1, 2) F_Interrupt F_Mprefix image_iff)
      next
        show \<open>s' = t1 @ t2 \<Longrightarrow> t1 \<in> \<T> (P a) \<Longrightarrow> tickFree t1 \<Longrightarrow> (t2, X) \<in> \<F> Q \<Longrightarrow>
              t2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for t1 t2
          apply (simp add: F_Interrupt T_Mprefix "*"(1))
          by (metis (no_types, lifting) "*"(1, 2) Cons_eq_appendI F_imp_front_tickFree
              append_is_Nil_conv assm front_tickFree_Cons_iff tickFree_Cons_iff)
      next
        show \<open>s' \<in> \<T> (P a) \<Longrightarrow> tickFree s' \<Longrightarrow> [\<checkmark>(r)] \<in> \<T> Q \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for r
          by (simp add: F_Interrupt T_Mprefix "*"(1, 2) image_iff) blast
      qed
    qed
  qed
qed



subsection \<open>Global Deterministic Choice\<close>

lemma GlobalDet_Mprefix :
  \<open>(\<box>a \<in> A. \<box>b \<in> B a \<rightarrow> P a b) =
   \<box>b \<in> (\<Union>a \<in> A. B a) \<rightarrow> \<sqinter>a \<in> {a \<in> A. b \<in> B a}. P a b\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Mprefix D_GlobalDet D_GlobalNdet)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (simp add: F_Mprefix F_GlobalDet F_GlobalNdet D_Mprefix) blast
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (auto simp add: F_Mprefix F_GlobalDet F_GlobalNdet split: if_split_asm)
qed



subsection \<open>Multiple Synchronization Product\<close>

lemma MultiSync_Mprefix_pseudo_distrib:
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> B \<in># M. \<box> x \<in> B \<rightarrow> P B x) =
   \<box> x \<in> (\<Inter>B \<in> set_mset M. B) \<rightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> B \<in># M. P B x)\<close>
  if nonempty: \<open>M \<noteq> {#}\<close> and hyp: \<open>\<And>B. B \<in># M \<Longrightarrow> B \<subseteq> S\<close>
proof-
  from nonempty obtain b M' where \<open>b \<in># M - M'\<close>
    \<open> M = add_mset b M'\<close> \<open>M' \<subseteq># M\<close>
    by (metis add_diff_cancel_left' diff_subset_eq_self insert_DiffM
        insert_DiffM2 multi_member_last multiset_nonemptyE)
  show ?thesis
    apply (subst (1 2 3) \<open>M = add_mset b M'\<close>)
    using \<open>b \<in># M - M'\<close> \<open>M' \<subseteq># M\<close>
  proof (induct rule: msubset_induct_singleton')
    case m_singleton show ?case by fastforce
  next
    case (add x F) show ?case
      apply (simp, subst Mprefix_Sync_Mprefix_subset[symmetric])
      apply (meson add.hyps(1) hyp in_diffD,
          metis \<open>b \<in># M - M'\<close> hyp in_diffD le_infI1)
      using add.hyps(3) by fastforce
  qed
qed


lemmas MultiPar_Mprefix_pseudo_distrib =
  MultiSync_Mprefix_pseudo_distrib[where S = \<open>UNIV\<close>, simplified]





(*<*)
end
  (*>*)