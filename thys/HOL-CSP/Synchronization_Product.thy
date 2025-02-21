(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Synchronization product
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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

chapter \<open> The Synchronization Product \<close>

(*<*)
theory  Synchronization_Product
  imports Process 
begin
  (*>*)

section\<open>Basic Concepts\<close>

fun setinterleaving :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<times> ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<times> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where

si_empty1: \<open>setinterleaving ([], X, []) = {[]}\<close>
| si_empty2: \<open>setinterleaving ([], X, y # t) = 
               (if y \<in> X
                then {} 
                else {z. \<exists>u. z = y # u \<and> u \<in> setinterleaving ([], X, t)})\<close>
| si_empty3: \<open>setinterleaving ((x # s), X, []) = 
               (if x \<in> X 
                then {} 
                else {z. \<exists> u. z = x # u \<and> u \<in> setinterleaving (s, X, [])})\<close>

| si_neq   : \<open>setinterleaving (x # s, X, y # t) = 
               (if x \<in> X 
                then if y \<in> X
                     then if x = y
                          then {z. \<exists>u. z = x # u \<and> u \<in> setinterleaving (s, X, t)}
                          else {}
                     else {z. \<exists>u. z = y # u \<and> u \<in> setinterleaving (x # s, X, t)}
                else if y \<notin> X
                     then {z. \<exists>u. z = x # u \<and> u \<in> setinterleaving (s, X, y # t)} \<union>
                          {z. \<exists>u. z = y # u \<and> u \<in> setinterleaving (x # s, X, t)} 
                     else {z. \<exists>u. z = x # u \<and> u \<in> setinterleaving (s, X, y # t)})\<close>

fun setinterleavingList :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<times> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set \<times> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list\<close>
  where

si_empty1l: \<open>setinterleavingList ([], X, []) = [[]]\<close>
| si_empty2l: \<open>setinterleavingList ([], X, (y # t)) = 
               (if y \<in> X
                then [] 
                else [y # z. z \<leftarrow> setinterleavingList ([], X, t)])\<close>
| si_empty3l: \<open>setinterleavingList (x # s, X, []) = 
               (if x \<in> X
                then [] 
                else [x # z. z \<leftarrow> setinterleavingList (s, X, [])])\<close>

| si_neql   : \<open>setinterleavingList ((x # s), X, (y # t)) = 
               (if x \<in> X 
                then if y \<in> X
                     then if x = y
                          then [x # z. z \<leftarrow> setinterleavingList (s, X, t)]
                          else []
                     else [y # z. z \<leftarrow> setinterleavingList (x # s, X, t)]
                else if y \<notin> X
                     then [x # z. z \<leftarrow> setinterleavingList (s, X, y # t)] @
                          [y # z. z \<leftarrow> setinterleavingList (x # s, X, t)]
                     else [x # z. z \<leftarrow> setinterleavingList (s, X, y # t)])\<close>


lemma finiteSetinterleavingList: "finite (set (setinterleavingList (s, X, t)))" 
  by auto

lemma setinterleaving_sym : \<open>setinterleaving (s, X, t) = setinterleaving(t, X, s)\<close>
  by (rule setinterleaving.induct[of \<open>\<lambda>(s, X, t). setinterleaving (s, X, t) =
           setinterleaving (t, X, s)\<close> \<open>(s, X, t)\<close>, simplified]) auto



abbreviation "setinterleaves_syntax"  ("_ setinterleaves '(()'(_, _')(), _')" [60,0,0,0]70)
  where      "u setinterleaves ((s, t), X) == (u \<in> setinterleaving(s, X, t))"


section\<open>Consequences\<close>

lemma emptyLeftProperty: \<open>s setinterleaves (([], t :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k), A) \<Longrightarrow> s = t\<close>
  by (induct \<open>([] :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, A, t)\<close> arbitrary: s t rule: setinterleaving.induct)
    (auto split: if_split_asm)

lemma emptyRightProperty: \<open>s setinterleaves ((t, []), A) \<Longrightarrow> s = t\<close>
  by (simp add: setinterleaving_sym emptyLeftProperty)

lemma emptyLeftSelf: \<open>\<forall>t1. t1 \<in> set t \<longrightarrow> t1 \<notin> A \<Longrightarrow> t setinterleaves (([], t), A)\<close>
  by (induct t) auto

lemma empty_setinterleaving : "[] setinterleaves ((t, u), A) \<Longrightarrow> t = []"  
  by (cases t; cases u) (simp_all split: if_split_asm) 


lemma emptyLeftNonSync: \<open>s setinterleaves (([], t), A) \<Longrightarrow> \<forall>a \<in> set t. a \<notin> A\<close>
proof (induct t arbitrary: s)
  case Nil
  show ?case by simp
next
  case (Cons a t)
  thus ?case by (cases s; simp split: if_split_asm)
qed


lemma ftf_Sync1: \<open>\<lbrakk>a \<notin> set u; a \<notin> set t; s setinterleaves ((t, u), A)\<rbrakk> \<Longrightarrow> a \<notin> set s\<close>
  by (induct \<open>(t, A, u)\<close> arbitrary: s t u rule: setinterleaving.induct)
    (auto intro: emptyLeftProperty emptyRightProperty split: if_split_asm)


lemma addNonSync:
  \<open>sa setinterleaves ((t, u), A) \<Longrightarrow> y1 \<notin> A \<Longrightarrow>
   (sa @ [y1]) setinterleaves ((t @ [y1], u), A) \<and> (sa @ [y1]) setinterleaves ((t, u @ [y1]), A)\<close>
  by (induct \<open>(t, A, u)\<close> arbitrary: sa t u rule: setinterleaving.induct)
    (auto split: if_split_asm)


lemma addSync:\<open>sa setinterleaves ((t, u), A) \<Longrightarrow> y1 \<in> A \<Longrightarrow>
               (sa @ [y1]) setinterleaves ((t @ [y1], u @ [y1]), A)\<close>
  by (induct \<open>(t, A, u)\<close> arbitrary: sa t u rule: setinterleaving.induct)
    (auto split: if_split_asm)


lemma doubleReverse: \<open>s1 setinterleaves ((t, u), A) \<Longrightarrow> rev s1 setinterleaves ((rev t, rev u), A)\<close>
  by (induct \<open>(t, A, u)\<close> arbitrary: s1 t u rule: setinterleaving.induct; simp split: if_split_asm)
    (metis [[metis_verbose = false]] addNonSync addSync rev.simps(2))+


(* from CSP_Laws, better to have it here ? *)
lemma SyncTlEmpty: \<open>a setinterleaves (([], u), A) \<Longrightarrow> tl a setinterleaves (([], tl u), A)\<close>
  by (cases u; cases a) (simp_all split: if_splits)

lemma SyncHd_Tl: 
  \<open>a setinterleaves ((t, u), A) \<Longrightarrow> hd t \<in> A \<Longrightarrow> hd u \<notin> A
    \<Longrightarrow> hd a = hd u \<and> tl a setinterleaves ((t, tl u), A)\<close>
  by (cases u; cases t) (auto split: if_split_asm)

lemma SyncHdAddEmpty: 
  "(tl a) setinterleaves (([], u), A) \<Longrightarrow> hd a \<notin> A \<Longrightarrow> a \<noteq> []
    \<Longrightarrow> a setinterleaves (([], hd a # u), A)"
  by (cases a) simp_all

lemma SyncHdAdd: 
  "(tl a) setinterleaves ((t, u), A) \<Longrightarrow> hd a \<notin> A \<Longrightarrow> hd t \<in> A \<Longrightarrow> a \<noteq> []
   \<Longrightarrow> a setinterleaves ((t, hd a # u), A)" 
  by (cases a, simp, cases t, auto) 

lemmas SyncHdAdd1 = SyncHdAdd[of "a # r", simplified] for a r

lemma SyncSameHdTl:
  "a setinterleaves ((t, u), A) \<Longrightarrow> hd t \<in> A \<Longrightarrow> hd u \<in> A
   \<Longrightarrow> hd t = hd u \<and> hd a = hd t \<and> (tl a) setinterleaves ((tl t, tl u), A)"
  by (cases u) (cases t, auto split:if_splits)+

lemma SyncSingleHeadAdd: 
  "a setinterleaves ((t, u), A) \<Longrightarrow> h \<notin> A
    \<Longrightarrow> (h # a) setinterleaves ((h # t, u), A)"
  by (cases u, auto split:if_splits)

lemma TickLeftSync:
  \<open>\<lbrakk>tick r \<in> A; front_tickFree t; s setinterleaves (([tick r], t :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k), A)\<rbrakk> \<Longrightarrow> s = t \<and> last t = tick r\<close>
  apply (induct \<open>([tick r] :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, A, t)\<close> arbitrary: s t rule: setinterleaving.induct)
   apply (simp_all add: front_tickFree_Cons_iff split: if_split_asm)
  by force (metis distinct.simps(1) distinct_length_2_or_more emptyRightProperty front_tickFree_Nil)


lemma EmptyLeftSync: \<open>s setinterleaves (([], t), A) \<Longrightarrow> s = t \<and> set t \<inter> A = {}\<close>
  by (meson Int_emptyI emptyLeftNonSync emptyLeftProperty)

lemma EmptyRightSync: \<open>s setinterleaves ((t, []), A) \<Longrightarrow> s = t \<and> set t \<inter> A = {}\<close>
  by (simp add: EmptyLeftSync setinterleaving_sym)


(* lemma event_set: \<open>(e::('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<in> range tick \<union> range ev\<close>
  by (metis UnCI event.exhaust rangeI) *)






lemma ftf_Sync21: \<open>a \<in> set u \<and> a \<notin> set t \<or> a \<in> set t \<and> a \<notin> set u \<Longrightarrow> a \<in> A \<Longrightarrow>
                   setinterleaving (u, A, t) = {}\<close>
  by (induct \<open>(t, A, u)\<close> arbitrary: t u rule: setinterleaving.induct)
    (auto split: if_split_asm)


lemma ftf_Sync32:
  assumes \<open>t = t1 @ [tick r]\<close> and \<open>u = u1 @ [tick r]\<close> 
    and \<open>s setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
  shows \<open>\<exists>s1. s1 setinterleaves ((t1, u1), range tick \<union> ev ` A) \<and> s = s1 @ [tick r]\<close>
proof -
  from assms(1) have b : \<open>rev t = tick r # rev t1\<close> by auto
  from assms(2) have a : \<open>rev u = tick r # rev u1\<close> by auto
  from assms have ab: \<open>(rev s) setinterleaves ((tick r # rev t1, tick r # rev u1), range tick \<union> ev ` A)\<close>
    using doubleReverse by fastforce
  from ab have c: \<open>tl (rev s) setinterleaves ((rev t1, rev u1), range tick \<union> ev ` A)\<close> by auto 
  hence d: \<open>(rev (tl (rev s))) setinterleaves ((t1,  u1), range tick \<union> ev ` A)\<close>
    using doubleReverse by fastforce
  from ab append_Cons_eq_iff c have \<open>rev s = tick r # tl (rev s)\<close> by auto
  with d show ?thesis by blast
qed


lemma SyncWithTick_imp_NTF:
  assumes \<open>(s @ [tick r]) setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
    and \<open>front_tickFree t\<close> and \<open>front_tickFree u\<close>
  shows \<open>\<exists>t1 u1. t = t1 @ [tick r] \<and> u = u1 @ [tick r] \<and> s setinterleaves ((t1, u1), range tick \<union> ev ` A)\<close>
proof-
  from assms(1) have a: \<open>(tick r # rev s) setinterleaves ((rev t, rev u), range tick \<union> ev ` A)\<close>
    using doubleReverse by fastforce
  from assms(1)[THEN doubleReverse] obtain tt uu where b: \<open>t = tt @ [tick r]\<close> \<open>u = uu @ [tick r]\<close>
    apply (cases t rule: rev_cases; cases u rule: rev_cases; simp add: image_iff)
    by ((split if_split_asm, safe)+, auto)+ (* ??? *)
  from ftf_Sync32[OF this assms(1)] have \<open>s setinterleaves ((tt, uu), range tick \<union> ev ` A)\<close> by blast
  with b show ?thesis by blast
qed 



lemma suffix_tick_le_ftf_imp_eq: \<open>front_tickFree t \<Longrightarrow> s @ [tick r] \<le> t \<Longrightarrow> s @ [tick r] = t\<close>
  by (metis prefixE append_Nil2 front_tickFree_nonempty_append_imp non_tickFree_tick tickFree_append_iff)




lemma synPrefix: \<open>(s @ t) setinterleaves ((ta, u), A) \<Longrightarrow> \<exists>t1 u1. t1 \<le> ta \<and> u1 \<le> u \<and> s setinterleaves ((t1, u1), A)\<close>
proof (induct \<open>(ta, A, u)\<close> arbitrary: s t ta u rule: setinterleaving.induct)
  case 1
  thus ?case by simp
next
  { case (2 y u)
    thus ?case
      by (cases s; simp split: if_split_asm)
        (metis si_empty1 insertI1 nil_le,
          metis (no_types) "2.prems" emptyLeftNonSync emptyLeftProperty
          emptyLeftSelf less_eq_list_def prefix_def set_ConsD)
  } note * = this

  case (3 x ta)
  thus ?case by (metis (full_types) "*" setinterleaving_sym)
next
  case (4 x ta y u)
  show ?case
  proof (cases s)
    show \<open>s = [] \<Longrightarrow> ?case\<close> by (metis si_empty1 insertI1 nil_le)
  next
    fix a s'
    assume \<open>s = a # s'\<close>
    consider \<open>x \<in> A\<close> \<open>y \<in> A\<close> | \<open>x \<in> A\<close> \<open>y \<notin> A\<close> | \<open>x \<notin> A\<close> \<open>y \<in> A\<close> | \<open>x \<notin> A\<close> \<open>y \<notin> A\<close> by blast
    thus ?case
    proof cases
      assume \<open>x \<in> A\<close> \<open>y \<in> A\<close>
      with "4.prems" have \<open>x = y\<close> \<open>a = y\<close> \<open>(s' @ t) setinterleaves ((ta, u), A)\<close>
        by (simp_all add: \<open>s = a # s'\<close> split: if_split_asm)
      from "4.hyps"(1)[OF \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x = y\<close> this(3)] obtain t1 u1
        where \<open>t1 \<le> ta\<close> \<open>u1 \<le> u \<and> s' setinterleaves ((t1, u1), A)\<close> by blast
      hence \<open>x # t1 \<le> x # ta \<and> y # u1 \<le> y # u \<and> s setinterleaves ((x # t1, y # u1), A)\<close>
        by (simp add: \<open>s = a # s'\<close> \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x = y\<close> \<open>a = y\<close>)
      thus ?case by blast
    next
      { fix x y ta u s a s'
        assume \<open>x \<in> A\<close> \<open>y \<notin> A\<close> \<open>s = a # s'\<close>
          and prems: \<open>(s @ t) setinterleaves ((x # ta, y # u), A)\<close>
        assume hyps: \<open>x \<in> A \<Longrightarrow> y \<notin> A \<Longrightarrow> (s @ t) setinterleaves ((x # ta, u), A) \<Longrightarrow>
                      \<exists>t1 u1. t1 \<le> x # ta \<and> u1 \<le> u \<and> s setinterleaves ((t1, u1), A)\<close> for s t
        from \<open>x \<in> A\<close> \<open>y \<notin> A\<close> \<open>s = a # s'\<close> prems
        have \<open>a = y\<close> \<open>(s' @ t) setinterleaves ((x # ta, u), A)\<close>
          by (simp_all add: \<open>s = a # s'\<close> split: if_split_asm)
        from hyps[OF \<open>x \<in> A\<close> \<open>y \<notin> A\<close> this(2)] obtain t1 u1
          where \<open>t1 \<le> x # ta\<close> \<open>u1 \<le> u\<close> \<open>s' setinterleaves ((t1, u1), A)\<close> by blast
        hence \<open>t1 \<le> x # ta \<and> y # u1 \<le> y # u \<and> s setinterleaves ((t1, y # u1), A)\<close>
          by (cases t1; simp add: \<open>s = a # s'\<close> \<open>y \<notin> A\<close> \<open>a = y\<close>)
        hence \<open>\<exists>t1 u1. t1 \<le> x # ta \<and> u1 \<le> y # u \<and> s setinterleaves ((t1, u1), A)\<close> by blast
      } note * = this

      show \<open>?case\<close> if \<open>x \<in> A\<close> and \<open>y \<notin> A\<close>
        using "*"[OF \<open>x \<in> A\<close> \<open>y \<notin> A\<close> \<open>s = a # s'\<close> "4.prems" "4.hyps"(2)] by simp

      show \<open>?case\<close> if \<open>x \<notin> A\<close> and \<open>y \<in> A\<close>
        by (metis "*"[OF \<open>y \<in> A\<close> \<open>x \<notin> A\<close> \<open>s = a # s'\<close>, of u ta]
            "4.hyps"(5) "4.prems" setinterleaving_sym)
    next
      assume \<open>x \<notin> A\<close> and \<open>y \<notin> A\<close>
      with "4.prems" have \<open>a = x \<and> (s' @ t) setinterleaves ((ta, y # u), A) \<or>
                           a = y \<and> (s' @ t) setinterleaves ((x # ta, u), A)\<close> (is \<open>?c \<or> _\<close>)
        by (simp add: \<open>s = a # s'\<close> split: if_split_asm)
      thus ?case 
      proof (elim disjE conjE)
        assume \<open>a = x\<close> \<open>(s' @ t) setinterleaves ((ta, y # u), A)\<close>
        from "4.hyps"(3)[OF \<open>x \<notin> A\<close> \<open>y \<notin> A\<close> this(2)] obtain t1 u1
          where \<open>t1 \<le> ta\<close> \<open>u1 \<le> y # u\<close> \<open>s' setinterleaves ((t1, u1), A)\<close> by blast
        hence \<open>x # t1 \<le> x # ta \<and> u1 \<le> y # u \<and> s setinterleaves ((x # t1, u1), A)\<close>
          by (cases u1; simp add: \<open>s = a # s'\<close> \<open>a = x\<close> \<open>x \<notin> A\<close>)
        thus ?case by blast
      next
        assume \<open>a = y\<close> \<open>(s' @ t) setinterleaves ((x # ta, u), A)\<close>
        from "4.hyps"(4)[OF \<open>x \<notin> A\<close> \<open>y \<notin> A\<close> this(2)] obtain t1 u1
          where \<open>t1 \<le> x # ta\<close> \<open>u1 \<le> u\<close> \<open>s' setinterleaves ((t1, u1), A)\<close> by blast
        hence \<open>t1 \<le> x # ta \<and> y # u1 \<le> y # u \<and> s setinterleaves ((t1, y # u1), A)\<close>
          by (cases t1; simp add: \<open>s = a # s'\<close> \<open>a = y\<close> \<open>y \<notin> A\<close>)
        thus ?case by blast
      qed
    qed
  qed
qed


lemma interleave_less_left :
  \<open>s setinterleaves ((t, u), A) \<Longrightarrow> t1 < t \<Longrightarrow>
   \<exists>u1 s1. u1 \<le> u \<and> s1 < s \<and> s1 setinterleaves ((t1, u1), A)\<close>
proof (induct \<open>(t, A, u)\<close> arbitrary: s t u t1 rule: setinterleaving.induct)
  case 1
  thus ?case by simp
next
  case (2 y u)
  hence False by simp
  thus ?case by simp
next
  case (3 x t)
  thus ?case by (metis (no_types, lifting) emptyRightProperty less_eq_list_def prefix_def
        nil_le2 order_less_imp_le synPrefix)
next
  case (4 x t y u)
  show ?case
  proof (cases \<open>t1 = []\<close>)
    show \<open>t1 = [] \<Longrightarrow> ?case\<close>
      by (metis "4.prems"(1) si_empty1 empty_setinterleaving insertI1
          list.distinct(1) nil_le order_le_imp_less_or_eq)
  next
    assume \<open>t1 \<noteq> []\<close>
    with \<open>t1 < x # t\<close> obtain t1' where \<open>t1 = x # t1'\<close> \<open>t1' < t\<close>
      by (metis hd_append2 less_eq_list_def prefix_def less_list_def less_tail list.exhaust_sel list.sel(1, 3))
    consider \<open>x \<in> A\<close> \<open>y \<in> A\<close> | \<open>x \<in> A\<close> \<open>y \<notin> A\<close> | \<open>x \<notin> A\<close> \<open>y \<in> A\<close> | \<open>x \<notin> A\<close> \<open>y \<notin> A\<close> by blast
    thus ?case
    proof cases
      assume \<open>x \<in> A\<close> \<open>y \<in> A\<close>
      with "4.prems"(1) obtain s' where \<open>x = y\<close> \<open>s = y # s'\<close> \<open>s' setinterleaves ((t, u), A)\<close>
        by (simp split: if_split_asm) blast
      from "4.hyps"(1)[OF \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x = y\<close> this(3) \<open>t1' < t\<close>]
      obtain u1 s1 where \<open>u1 \<le> u\<close> \<open>s1 < s'\<close> \<open>s1 setinterleaves ((t1', u1), A)\<close> by blast
      hence \<open>y # u1 \<le> y # u \<and> y # s1 < s \<and> (y # s1) setinterleaves ((t1, y # u1), A)\<close>
        by (simp add: \<open>t1 = x # t1'\<close> \<open>x = y\<close> \<open>y \<in> A\<close> \<open>s = y # s'\<close>)
      thus ?case by blast
    next
      assume \<open>x \<in> A\<close> \<open>y \<notin> A\<close>
      with "4.prems"(1) obtain s' where \<open>s = y # s'\<close> \<open>s' setinterleaves ((x # t, u), A)\<close>
        by (simp split: if_split_asm) blast
      from "4.hyps"(2)[OF \<open>x \<in> A\<close> \<open>y \<notin> A\<close> this(2) less_cons[THEN iffD2, OF \<open>t1' < t\<close>]]
      obtain u1 s1 where \<open>u1 \<le> u\<close> \<open>s1 < s'\<close> \<open>s1 setinterleaves ((x # t1', u1), A)\<close> by blast
      hence \<open>y # u1 \<le> y # u \<and> y # s1 < s \<and> (y # s1) setinterleaves ((t1, y # u1), A)\<close>
        by (simp add: \<open>t1 = x # t1'\<close> \<open>y \<notin> A\<close> \<open>s = y # s'\<close>)
      thus ?case by blast
    next
      assume \<open>x \<notin> A\<close> \<open>y \<in> A\<close>
      with "4.prems"(1) obtain s' where \<open>s = x # s'\<close> \<open>s' setinterleaves ((t, y # u), A)\<close>
        by (simp split: if_split_asm) blast
      from "4.hyps"(5)[OF \<open>x \<notin> A\<close> _ this(2) \<open>t1' < t\<close>] \<open>y \<in> A\<close>
      obtain u1 s1 where \<open>u1 \<le> y # u\<close> \<open>s1 < s'\<close> \<open>s1 setinterleaves ((t1', u1), A)\<close> by blast
      hence \<open>u1 \<le> y # u \<and> x # s1 < s \<and> (x # s1) setinterleaves ((t1, u1), A)\<close>
        by (cases u1; simp add: \<open>t1 = x # t1'\<close> \<open>x \<notin> A\<close> \<open>s = x # s'\<close>)
      thus ?case by blast
    next
      assume \<open>x \<notin> A\<close> \<open>y \<notin> A\<close>
      with "4.prems"(1) obtain s'
        where \<open>s = x # s' \<and> s' setinterleaves ((t, y # u), A) \<or>
               s = y # s' \<and> s' setinterleaves ((x # t, u), A)\<close>
        by (simp split: if_split_asm) blast
      thus ?case
      proof (elim disjE conjE)
        assume \<open>s = x # s'\<close> \<open>s' setinterleaves ((t, y # u), A)\<close> 
        from "4.hyps"(3)[OF \<open>x \<notin> A\<close> \<open>y \<notin> A\<close> this(2) \<open>t1' < t\<close>]
        obtain u1 s1 where \<open>u1 \<le> y # u\<close> \<open>s1 < s'\<close> \<open>s1 setinterleaves ((t1', u1), A)\<close> by blast
        hence \<open>u1 \<le> y # u \<and> x # s1 < s \<and> (x # s1) setinterleaves ((t1, u1), A)\<close>
          by (cases u1; simp add: \<open>t1 = x # t1'\<close> \<open>x \<notin> A\<close> \<open>s = x # s'\<close>)
        thus ?case by blast
      next
        assume \<open>s = y # s'\<close> \<open>s' setinterleaves ((x # t, u), A)\<close> 
        from "4.hyps"(4)[OF \<open>x \<notin> A\<close> \<open>y \<notin> A\<close> this(2) less_cons[THEN iffD2, OF \<open>t1' < t\<close>]]
        obtain u1 s1 where \<open>u1 \<le> u\<close> \<open>s1 < s'\<close> \<open>s1 setinterleaves ((x # t1', u1), A)\<close> by blast
        hence \<open>y # u1 \<le> y # u \<and> y # s1 < s \<and> (y # s1) setinterleaves ((t1, y # u1), A)\<close>
          by (simp add: \<open>t1 = x # t1'\<close> \<open>y \<notin> A\<close> \<open>s = y # s'\<close>)
        thus ?case by blast
      qed
    qed
  qed
qed

lemma interleave_less_right :
  \<open>s setinterleaves ((t, u), A) \<Longrightarrow> u1 < u \<Longrightarrow>
   \<exists>t1 s1. t1 \<le> t \<and> s1 < s \<and> s1 setinterleaves ((t1, u1), A)\<close>
  by (metis (no_types) interleave_less_left setinterleaving_sym)


lemma interleave_le_left :
  \<open>s setinterleaves ((t, u), A) \<Longrightarrow> t1 \<le> t \<Longrightarrow>
   \<exists>u1 s1. u1 \<le> u \<and> s1 \<le> s \<and> s1 setinterleaves ((t1, u1), A)\<close>
  by (metis interleave_less_left order_le_less)

lemma interleave_le_right :
  \<open>s setinterleaves ((t, u), A) \<Longrightarrow> u1 \<le> u \<Longrightarrow>
   \<exists>t1 s1. t1 \<le> t \<and> s1 \<le> s \<and> s1 setinterleaves ((t1, u1), A)\<close>
  by (metis (no_types) interleave_le_left setinterleaving_sym)

(*   assumes \<open>(s @ [tick r]) setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
      and \<open>t \<in> \<T> P\<close> and \<open>u \<in> \<T> Q\<close>
    shows \<open>\<exists>t_P t_Q X_P X_Q. (t_P, X_P) \<in> \<F> P \<and> (t_Q, X_Q) \<in> \<F> Q \<and>
                             s setinterleaves ((t_P, t_Q), range tick \<union> ev ` A) \<and>
                             X_P - {tick r} = (X_P \<union> X_Q) \<inter> range tick \<union> ev ` A \<union> X_P \<inter> X_Q\<close>
 *)


lemma SyncWithTick_imp_NTF1:
  assumes \<open>(s @ [tick r]) setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
    and \<open>t \<in> \<T> P\<close> and \<open>u \<in> \<T> Q\<close>
  shows \<open>\<exists>t u X_P X_Q. (t, X_P) \<in> \<F> P \<and> (u, X_Q) \<in> \<F> Q \<and>
                         s setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                         X - {tick r} = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q\<close>
proof -
  from SyncWithTick_imp_NTF[OF assms(1)] assms(2, 3) is_processT2_TR
  obtain t1 u1 
    where * : \<open>t = t1 @ [tick r]\<close> \<open>u = u1 @ [tick r]\<close>
      \<open>s setinterleaves ((t1, u1), range tick \<union> ev ` A)\<close> by blast
  from "*"(1, 2) assms(2, 3) have E: \<open>(t1, X - {tick r}) \<in> \<F> P\<close> \<open>(u1, X - {tick r}) \<in> \<F> Q\<close>
    by (simp_all add: T_F process_charn)
  with "*"(3) show ?thesis by blast
qed


lemma interleave_size: 
  \<open>s setinterleaves ((t, u), C) \<Longrightarrow> length s = length t + length u - length (filter (\<lambda>x. x \<in> C) t)\<close>
  apply (induct \<open>(t, C, u)\<close> arbitrary: t u s rule: setinterleaving.induct)
     apply (simp; fail)
    apply (metis add_diff_cancel_left' emptyLeftProperty filter.simps(1))
   apply (metis add_diff_cancel_right' emptyLeftNonSync
      emptyRightProperty filter_False setinterleaving_sym)
  by (simp split: if_split_asm;
      metis (no_types) [[metis_verbose = false]] Suc_diff_le add_Suc_right
      length_Cons length_filter_le trans_le_add1)

lemma interleave_eq_size: 
  \<open>s setinterleaves ((t, u), C) \<Longrightarrow> s' setinterleaves ((t, u), C) \<Longrightarrow> length s = length s'\<close>
  by (simp add: interleave_size)


lemma ftf_Sync:
  assumes \<open>front_tickFree t\<close> and \<open>front_tickFree u\<close>
    and \<open>s setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
  shows \<open>front_tickFree s\<close>
proof (cases \<open>tickFree s\<close>)
  show \<open>tickFree s \<Longrightarrow> front_tickFree s\<close> by (fact tickFree_imp_front_tickFree)
next
  assume \<open>\<not> tickFree s\<close>
  hence \<open>\<exists>s1 s2 r. tickFree s1 \<and> s = (s1 @ [tick r]) @ s2\<close>
  proof (induct s rule: rev_induct)
    case Nil thus ?case by simp
  next
    case (snoc a s)
    from \<open>\<not> tickFree (s @ [a])\<close> consider r where \<open>tickFree s\<close> \<open>a = tick r\<close> | \<open>\<not> tickFree s\<close>
      by (auto simp add: tickFree_def)
    thus ?case
    proof cases
      show \<open>tickFree s \<Longrightarrow> a = tick r \<Longrightarrow>
            \<exists>s1 s2 r. tickFree s1 \<and> s @ [a] = (s1 @ [tick r]) @ s2\<close> for r by blast
    next
      assume \<open>\<not> tickFree s\<close>
      with snoc.hyps obtain s1 s2 r where \<open>tickFree s1\<close> \<open>s = (s1 @ [tick r]) @ s2\<close> by blast
      hence \<open>tickFree s1 \<and> s @ [a] = (s1 @ [tick r]) @ (s2 @ [a])\<close> by simp
      thus ?case by blast
    qed
  qed
  then obtain s1 s2 r where \<open>tickFree s1\<close> \<open>s = (s1 @ [tick r]) @ s2\<close> by blast
  from synPrefix[of \<open>s1 @ [tick r]\<close> s2, folded \<open>s = (s1 @ [tick r]) @ s2\<close>, OF assms(3)]
  obtain t1 u1
    where * : \<open>t1 \<le> t\<close> \<open>u1 \<le> u\<close>
      \<open>(s1 @ [tick r]) setinterleaves ((t1, u1), range tick \<union> ev ` A)\<close> by blast
  from "*"(1, 2) assms(1, 2) have \<open>front_tickFree t1\<close> \<open>front_tickFree u1\<close>
    by (metis prefixE front_tickFree_dw_closed)+
  from SyncWithTick_imp_NTF[OF "*"(3) this]
  obtain t2 u2 where \<open>t1 = t2 @ [tick r]\<close> \<open>u1 = u2 @ [tick r]\<close>
    \<open>s1 setinterleaves ((t2, u2), range tick \<union> ev ` A)\<close> by blast
  from \<open>t1 \<le> t\<close> \<open>t1 = t2 @ [tick r]\<close> assms(1) suffix_tick_le_ftf_imp_eq have \<open>t = t1\<close> by metis
  from \<open>u1 \<le> u\<close> \<open>u1 = u2 @ [tick r]\<close> assms(2) suffix_tick_le_ftf_imp_eq have \<open>u = u1\<close> by metis
  have \<open>(s1 @ [tick r]) setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
    by (simp add: "*"(3) \<open>t = t1\<close> \<open>u = u1\<close>)
  with assms(3) interleave_eq_size have \<open>length s = length (s1 @ [tick r])\<close> by blast
  with \<open>s = (s1 @ [tick r]) @ s2\<close> have \<open>s = s1 @ [tick r]\<close> by simp
  thus \<open>front_tickFree s\<close> by (simp add: \<open>tickFree s1\<close> front_tickFree_append)
qed



section\<open>The Sync Operator Definition\<close>

lift_definition Sync :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(3(_ \<lbrakk>_\<rbrakk>/ _))\<close> [70, 0, 71] 70)
  is \<open>\<lambda>P A Q. ({(s, R). \<exists>t u X Y. (t, X) \<in> \<F> P \<and> (u, Y) \<in> \<F> Q \<and>
                                  s setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                                  R = (X \<union> Y) \<inter> (range tick \<union> ev ` A) \<union> X \<inter> Y} \<union>
               {(s, R). \<exists>t u r v. ftF v \<and> (tF r \<or> v = []) \<and> s = r @ v \<and>
                                  r setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                                  (t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P)},
               {s. \<exists>t u r v. ftF v \<and> (tF r \<or> v = []) \<and> s = r @ v \<and>
                             r setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                             (t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P)})\<close>
proof -
  show \<open>?thesis P A Q\<close> (is \<open>is_process(?f, ?d P Q)\<close>) for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and A
  proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv, intro conjI impI allI)
    show \<open>([], {}) \<in> ?f\<close>
      by simp (metis Int_commute Int_empty_right si_empty1
          Un_empty insert_iff is_processT1) 
  next 
    show \<open>(s, X) \<in> ?f \<Longrightarrow> ftF s\<close> for s X
      apply (simp, elim disjE)
      using F_imp_front_tickFree ftf_Sync apply blast
      by (metis D_imp_front_tickFree T_imp_front_tickFree append.right_neutral front_tickFree_append ftf_Sync)

  next
    fix s t assume \<open>(s @ t, {}) \<in> ?f\<close>
    then consider (fail) t_P t_Q X_P X_Q where 
      \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
      \<open>(s @ t) setinterleaves ((t_P, t_Q), range tick \<union> ev ` A)\<close>
      \<open>(X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q = {}\<close>
    | (div) t' u r v where \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>s @ t = r @ v\<close>
      \<open>r setinterleaves ((t', u), range tick \<union> ev ` A)\<close>
      \<open>t' \<in> \<D> P \<and> u \<in> \<T> Q \<or> t' \<in> \<D> Q \<and> u \<in> \<T> P\<close>
      (* TODO: break this smt *)
      by (smt (verit, ccfv_SIG) Un_iff case_prod_conv mem_Collect_eq)
    thus \<open>(s, {}) \<in> ?f\<close>
    proof cases
      case fail
      from fail(3)[THEN synPrefix] show \<open>(s, {}) \<in> ?f\<close>
        apply (elim exE conjE)
        apply (drule fail(1, 2)[THEN F_T, THEN is_processT3_TR])+
        by simp (metis Int_empty_left T_F Un_absorb)
    next
      case div
      show \<open>(s, {}) \<in> ?f\<close>
      proof (cases \<open>length r \<le> length s\<close>)
        assume \<open>length r \<le> length s\<close>
        with div have \<open>front_tickFree (take (length s - length r) v) \<and>
                       (tickFree r \<or> take (length s - length r) v = []) \<and>
                       s = r @ take (length s - length r) v\<close>
          by simp (metis append_eq_conv_conj append_take_drop_id
              front_tickFree_dw_closed take_all_iff take_append)
        show \<open>(s, {}) \<in> ?f\<close> by simp (use \<open>?this\<close> div in blast)
      next
        assume \<open>\<not> length r \<le> length s\<close>
        with div obtain r' where \<open>r = s @ r'\<close>
          by (metis append_eq_append_conv_if append_take_drop_id)
        from div \<open>r = s @ r'\<close> synPrefix obtain t1 u1
          where ** : \<open>t1 \<le> t'\<close> \<open>u1 \<le> u\<close>
            \<open>s setinterleaves ((t1, u1), range tick \<union> ev ` A)\<close> by metis
        from div "**"(1, 2) D_T is_processT3_TR
        have \<open>t1 \<in> \<T> P \<and> u1 \<in> \<T> Q \<or> t1 \<in> \<T> Q \<and> u1 \<in> \<T> P\<close> by blast
        thus \<open>(s, {}) \<in> ?f\<close>
          by simp (metis "**"(3) Int_Un_eq(1) T_F setinterleaving_sym sup_bot.right_neutral)
      qed
    qed
  next
    fix s X Y
    assume \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y\<close>
    then consider \<open>s \<in> ?d P Q\<close>
      | (fail) s_P s_Q X_P X_Q
      where \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close>
        \<open>s setinterleaves ((s_P, s_Q), range tick \<union> ev ` A)\<close>
        \<open>Y = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q\<close>
      by simp blast
    thus \<open>(s, X) \<in> ?f\<close>
    proof cases
      show \<open>s \<in> ?d P Q \<Longrightarrow> (s, X) \<in> ?f\<close> by blast
    next
      case fail
      have \<open>(s_P, X_P \<inter> X) \<in> \<F> P\<close> using fail(1) by (meson inf_le1 process_charn)
      moreover have \<open>(s_Q, X_Q \<inter> X) \<in> \<F> Q\<close> using fail(2) by (meson inf_le1 process_charn)
      moreover have \<open>X = (X_P \<inter> X \<union> X_Q \<inter> X) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X \<inter> (X_Q \<inter> X)\<close>
        by (subst \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y\<close>[THEN conjunct2, THEN Int_absorb1, symmetric])
          (use fail(4) in blast)
      ultimately show \<open>(s, X) \<in> ?f\<close> using fail(3) by simp blast
    qed
  next
    fix s X Y
    assume \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f)\<close>
    then consider \<open>s \<in> ?d P Q\<close> | \<open>(s, X) \<in> ?f \<and> s \<notin> ?d P Q\<close> by linarith
    thus \<open>(s, X \<union> Y) \<in> ?f\<close>
    proof cases
      show \<open>s \<in> ?d P Q \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> by blast
    next
      assume \<open>(s, X) \<in> ?f \<and> s \<notin> ?d P Q\<close>
      then obtain s_P X_P s_Q X_Q
        where assms : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close>
          \<open>s setinterleaves ((s_P, s_Q), range tick \<union> ev ` A)\<close>
          \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q\<close>
        by simp blast
      have assms4 : \<open>c \<in> Y \<Longrightarrow> ((s @ [c]) setinterleaves ((t1, u1), range tick \<union> ev ` A) \<Longrightarrow>
                     ((t1, {}) \<in> \<F> P \<longrightarrow> (u1, {}) \<notin> \<F> Q) \<and>
                     ((t1, {}) \<in> \<F> Q \<longrightarrow> (u1, {}) \<notin> \<F> P))\<close> for c t1 u1
        using \<open>(s, X) \<in> ?f \<and> s \<notin> ?d P Q\<close>
          \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f)\<close> 
        by simp (metis (no_types, lifting) Int_empty_left setinterleaving_sym sup_bot.right_neutral)
      show \<open>(s, X \<union> Y) \<in> ?f\<close>
      proof-
        define Y1 Y2 where Y1_def: \<open>Y1 \<equiv> Y \<inter> (range tick \<union> ev ` A)\<close>
          and Y2_def: \<open>Y2 \<equiv> Y - (range tick \<union> ev ` A)\<close>
        hence \<open>Y1 \<union> Y2 = Y\<close> by blast
        have $ : \<open>\<forall>z\<in>Y1. (s_P @ [z], {}) \<notin> \<F> P \<or> (s_Q @ [z], {}) \<notin> \<F> Q\<close>
        proof (rule ccontr)
          assume \<open>\<not> (\<forall>z\<in>Y1. (s_P @ [z], {}) \<notin> \<F> P \<or> (s_Q @ [z], {}) \<notin> \<F> Q)\<close>
          then obtain z1 where * : \<open>z1 \<in> Y1\<close> \<open>(s_P @ [z1], {}) \<in> \<F> P\<close> \<open>(s_Q @ [z1], {}) \<in> \<F> Q\<close> by blast
          have \<open>(s @ [z1]) setinterleaves ((s_P @ [z1], s_Q @ [z1]), range tick \<union> ev ` A)\<close>
            by (metis "*"(1) IntD2 Y1_def addSync assms(3))
          with "*" assms4 show False by (metis IntD1 Y1_def)
        qed
        define Z1 Z2 where Z1_def: \<open>Z1 \<equiv> Y1 \<inter> {z. (s_P @ [z], {}) \<notin> \<F> P}\<close>
          and Z2_def: \<open>Z2 \<equiv> Y1 - {z. (s_P @ [z], {}) \<notin> \<F> P}\<close>
        hence \<open>Y1 = Z1 \<union> Z2\<close> by blast
        have $$ : \<open>\<forall>y\<in>Y2. (s_P @ [y], {}) \<notin> \<F> P \<and> (s_Q @ [y], {}) \<notin> \<F> Q\<close>
        proof (rule ccontr)
          assume \<open>\<not> (\<forall>y\<in>Y2. (s_P @ [y], {}) \<notin> \<F> P \<and> (s_Q @ [y], {}) \<notin> \<F> Q)\<close>
          then obtain y1 where * : \<open>y1 \<in> Y2\<close> \<open>((s_P @ [y1], {}) \<in> \<F> P \<or> (s_Q @ [y1], {}) \<in> \<F> Q)\<close> by blast
          hence \<open>(s @ [y1]) setinterleaves ((s_P @ [y1], s_Q), range tick \<union> ev ` A) \<or>
                 (s @ [y1]) setinterleaves ((s_P, s_Q @ [y1]), range tick \<union> ev ` A)\<close>
            by (simp add: Y2_def addNonSync assms(3))
          with "*" assms show False
            by (metis DiffD1 DiffD2 Y2_def addNonSync assms(1, 2, 3) assms4 is_processT4_empty)
        qed

        define X_P' where \<open>X_P' = X_P \<union> Z1 \<union> Y2\<close>
        hence f1: \<open>(s_P, X_P') \<in> \<F> P\<close> by (simp add: "$$" Z1_def assms(1) process_charn)
        define X_Q' where \<open>X_Q' = X_Q \<union> Z2 \<union> Y2\<close>
        hence f2: \<open>(s_Q, X_Q') \<in> \<F> Q\<close> using "$" "$$" by (simp add: Z2_def assms(2) is_processT5)
        have \<open>(X_P \<union> X_Q \<union> Y1 \<union> Y2) \<inter> range tick \<union> ev ` A =
              (X_P \<union> X_Q) \<inter> range tick \<union> ev ` A \<union> Y1\<close>
          unfolding Y1_def Y2_def by auto
        hence \<open>(X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q \<union> Y =
               (X_P' \<union> X_Q') \<inter> (range tick \<union> ev ` A) \<union> X_P' \<inter> X_Q'\<close>
          using X_P'_def X_Q'_def \<open>Y1 = Z1 \<union> Z2\<close> \<open>Y1 \<union> Y2 = Y\<close> by blast
        thus \<open>(s, X \<union> Y) \<in> ?f\<close> by simp (use f1 f2 assms(3, 4) in blast)
      qed
    qed
  next
    show processT9: \<open>s @ [\<checkmark>(res)] \<in> ?d P Q \<Longrightarrow> s \<in> ?d P Q\<close> for s res
    proof -
      { fix s t u r v and res :: 'r and P Q
        assume assms : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>s @ [\<checkmark>(res)] = r @ v\<close>
          \<open>r setinterleaves ((t, u), range tick \<union> ev ` A)\<close> \<open>t \<in> \<D> P\<close> \<open>u \<in> \<T> Q\<close>
        from assms(2) have \<open>s \<in> ?d P Q\<close>
        proof (elim disjE)
          assume \<open>tickFree r\<close>
          with assms(1, 3) have \<open>s @ [\<checkmark>(res)] = r @ (butlast v @ [\<checkmark>(res)])\<close>
            by (cases v rule: rev_cases) auto
          with \<open>tickFree r\<close> assms(1, 4, 5, 6) show \<open>s \<in> ?d P Q\<close>
            by simp (use front_tickFree_iff_tickFree_butlast tickFree_imp_front_tickFree in blast)
        next
          assume \<open>v = []\<close>
          with assms(3) obtain r' where \<open>r = r' @ [\<checkmark>(res)]\<close> \<open>s = r'\<close> by auto
          with D_imp_front_tickFree SyncWithTick_imp_NTF assms(4, 5, 6) is_processT2_TR
          obtain t1 u1 where \<open>t = t1 @ [\<checkmark>(res)]\<close> \<open>u = u1 @ [\<checkmark>(res)]\<close>
            \<open>r' setinterleaves ((t1, u1), range tick \<union> ev ` A)\<close> by metis
          with assms(5, 6) show \<open>s \<in> ?d P Q\<close>
            apply (simp add: \<open>s = r'\<close>)
            by (metis prefixI \<open>v = []\<close> append.right_neutral assms(1) is_processT3_TR is_processT9)
        qed
      }
      thus \<open>s @ [\<checkmark>(res)] \<in> ?d P Q \<Longrightarrow> s \<in> ?d P Q\<close> for s by simp blast
    qed    

    fix s X res
    assume \<open>(s @ [\<checkmark>(res)], {}) \<in> ?f\<close>
    hence \<open>s @ [\<checkmark>(res)] \<in> ?d P Q \<or>
           (\<exists>s_P s_Q X_P X_Q. (s_P, X_P) \<in> \<F> P \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
                              (s @ [\<checkmark>(res)]) setinterleaves ((s_P, s_Q), range tick \<union> ev ` A) \<and>
                              {} = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q)\<close> by auto
    thus \<open>(s, X - {\<checkmark>(res)}) \<in> ?f\<close>
    proof (elim disjE exE conjE)
      from processT9 show \<open>s @ [\<checkmark>(res)] \<in> ?d P Q \<Longrightarrow> (s, X - {\<checkmark>(res)}) \<in> ?f\<close> by blast
    next
      fix s_P s_Q X_P X_Q res
      assume * : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close>
        \<open>(s @ [\<checkmark>(res)]) setinterleaves ((s_P, s_Q), range tick \<union> ev ` A)\<close>
        \<open>{} = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q\<close>
      from SyncWithTick_imp_NTF1[OF "*"(3) "*"(1, 2)[THEN F_T]]
      show \<open>(s, X - {\<checkmark>(res)}) \<in> ?f\<close> by simp
    qed
  next
    show \<open>s \<in> ?d P Q \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> ?d P Q\<close> for s t
      using front_tickFree_append by fastforce
  next  
    show \<open>s \<in> ?d P Q \<Longrightarrow> (s, X) \<in> ?f\<close> for s X by blast
  qed
qed



section\<open>The Projections\<close>

lemma F_Sync :
  \<open>\<F> (P \<lbrakk> A \<rbrakk> Q) = 
   {(s, R). \<exists>t u X Y. (t, X) \<in> \<F> P \<and> (u, Y) \<in> \<F> Q \<and>
                  s setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                      R = (X \<union> Y) \<inter> (range tick \<union> ev ` A) \<union> X \<inter> Y} \<union>
   {(s, R). \<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and> s = r @ v \<and>
                      r setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                      (t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P)}\<close>
  by (simp add: Failures.rep_eq Sync.rep_eq FAILURES_def)   

lemma D_Sync :
  \<open>\<D> (P \<lbrakk> A \<rbrakk> Q) = 
   {s. \<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and> s = r @ v \<and>
                 r setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                 (t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P)}\<close>
  by (simp add: Divergences.rep_eq Sync.rep_eq DIVERGENCES_def)   

lemma T_Sync :
  \<open>\<T> (P \<lbrakk> A \<rbrakk> Q) =
   {s. \<exists>t u. t \<in> \<T> P \<and> u \<in> \<T> Q \<and> s setinterleaves ((t, u), range tick \<union> ev ` A)} \<union>
   {s. \<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and>
                 s = r @ v \<and> r setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                 (t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P)}\<close>
  by (simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_Sync) blast

lemmas Sync_projs = F_Sync D_Sync T_Sync


section\<open>Syntax for Interleave and Parallel Operator \<close>

abbreviation Inter_syntax  ("(_ ||| _)" [72,73] 72)
  where "P ||| Q \<equiv> (P \<lbrakk> {} \<rbrakk> Q)"

abbreviation Par_syntax  ("(_ || _)" [74,75] 74)
  where "P || Q  \<equiv> (P \<lbrakk> UNIV \<rbrakk> Q)"


lemma setinterleaving_UNIV_iff : \<open>s setinterleaves ((t, u), UNIV) \<longleftrightarrow> s = t \<and> s = u\<close>
  for s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (induct \<open>(u, UNIV :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set, t)\<close>
      arbitrary: s t u rule: setinterleaving.induct) auto

lemma F_Par :
  \<open>\<F> (P || Q) = {(s, R). \<exists>X Y. (s, X) \<in> \<F> P \<and> (s, Y) \<in> \<F> Q \<and> R = X \<union> Y \<union> X \<inter> Y} \<union>
                 {(s, R). \<exists>t v. ftF v \<and> (tF t \<or> v = []) \<and> s = t @ v \<and>
                                (t \<in> \<D> P \<and> t \<in> \<T> Q \<or> t \<in> \<D> Q \<and> t \<in> \<T> P)}\<close>
  by (auto simp add: F_Sync setinterleaving_UNIV_iff)

lemma D_Par :
  \<open>\<D> (P || Q) = {s. \<exists>t v. ftF v \<and> (tF t \<or> v = []) \<and> s = t @ v \<and>
                          (t \<in> \<D> P \<and> t \<in> \<T> Q \<or> t \<in> \<D> Q \<and> t \<in> \<T> P)}\<close>
  by (simp add: D_Sync setinterleaving_UNIV_iff)

lemma T_Par :
  \<open>\<T> (P || Q) = \<T> P \<inter> \<T> Q \<union> {t @ v| t v. ftF v \<and> (tF t \<or> v = []) \<and>
                                          t \<in> \<D> P \<inter> \<T> Q \<union> \<D> Q \<inter> \<T> P}\<close>
  by (simp add: set_eq_iff T_Sync setinterleaving_UNIV_iff) blast

lemmas Par_projs = F_Par D_Par T_Par


lemma superset_T_Inter : \<open>{t. tF t \<and> t \<in> \<T> P \<union> \<T> Q} \<subseteq> \<T> (P ||| Q)\<close>
proof (rule subsetI, clarify)
  fix t assume \<open>tF t\<close> \<open>t \<in> \<T> P \<union> \<T> Q\<close>
  from \<open>tF t\<close> have \<open>t setinterleaves ((t, []), range tick)\<close>
    by (metis disjoint_iff emptyLeftSelf setinterleaving_sym tickFree_def)
  with \<open>t \<in> \<T> P \<union> \<T> Q\<close> show \<open>t \<in> \<T> (P ||| Q)\<close>
    by (simp add: T_Sync) (use Nil_elem_T setinterleaving_sym in blast)
qed

lemma superset_D_Inter : \<open>\<D> P \<union> \<D> Q \<subseteq> \<D> (P ||| Q)\<close>
proof (rule subsetI)
  fix t assume \<open>t \<in> \<D> P \<union> \<D> Q\<close>
  define t' where \<open>t' \<equiv> if tF t then t else butlast t\<close>
  from \<open>t \<in> \<D> P \<union> \<D> Q\<close> D_imp_front_tickFree front_tickFree_iff_tickFree_butlast
  have \<open>tF t'\<close> unfolding t'_def by auto
  with \<open>t \<in> \<D> P \<union> \<D> Q\<close> have \<open>t' \<in> \<D> P \<union> \<D> Q\<close>
    by (metis t'_def D_imp_front_tickFree Un_iff butlast_snoc
        is_processT9 nonTickFree_n_frontTickFree)
  from \<open>tF t'\<close> have \<open>t' setinterleaves ((t', []), range tick)\<close>
    by (metis disjoint_iff emptyLeftSelf setinterleaving_sym tickFree_def)
  with \<open>t' \<in> \<D> P \<union> \<D> Q\<close> have \<open>t' \<in> \<D> (P ||| Q)\<close>
    by (simp add: D_Sync) (use front_tickFree_Nil Nil_elem_T in blast)
  thus \<open>t \<in> \<D> (P ||| Q)\<close>
    by (metis \<open>tF t'\<close> butlast_snoc front_tickFree_iff_tickFree_butlast
        front_tickFree_single is_processT7 nonTickFree_n_frontTickFree t'_def)
qed



section\<open> Continuity Rule \<close>

lemma Sync_commute: \<open>P \<lbrakk>S\<rbrakk> Q = Q \<lbrakk>S\<rbrakk> P\<close>
  \<comment>\<open>This will simplify the following proofs.\<close>
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> s \<in> \<D> (Q \<lbrakk>S\<rbrakk> P)\<close> for s by (simp add: D_Sync) blast
next
  show \<open>s \<in> \<D> (Q \<lbrakk>S\<rbrakk> P) \<Longrightarrow> s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> for s by (simp add: D_Sync) blast
next
  show \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> (s, X) \<in> \<F> (Q \<lbrakk>S\<rbrakk> P)\<close> for s X
    by (simp add: F_Sync, elim disjE exE)
      (metis (no_types) Int_commute Un_commute setinterleaving_sym, blast)
next
  show \<open>(s, X) \<in> \<F> (Q \<lbrakk>S\<rbrakk> P) \<Longrightarrow> (s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> for s X
    by (simp add: F_Sync, elim disjE exE)
      (metis (no_types) Int_commute Un_commute setinterleaving_sym, blast)
qed


(* TODO: declare this simp ? *)
lemma mono_Sync : \<open>P \<sqsubseteq> P' \<Longrightarrow> Q \<sqsubseteq> Q' \<Longrightarrow> P \<lbrakk>A\<rbrakk> Q \<sqsubseteq> P' \<lbrakk>A\<rbrakk> Q'\<close>
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  have \<open>P \<lbrakk>A\<rbrakk> S \<sqsubseteq> Q \<lbrakk>A\<rbrakk> S\<close> if \<open>P \<sqsubseteq> Q\<close> for P S Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (unfold le_approx_def, safe)
    from le_approx1[OF \<open>P \<sqsubseteq> Q\<close>] le_approx_lemma_T[OF \<open>P \<sqsubseteq> Q\<close>]
    show \<open>s \<in> \<D> (Q \<lbrakk>A\<rbrakk> S) \<Longrightarrow> s \<in> \<D> (P \<lbrakk>A\<rbrakk> S)\<close> for s by (simp add: D_Sync) blast
  next
    show \<open>s \<notin> \<D> (P \<lbrakk>A\<rbrakk> S) \<Longrightarrow> X \<in> \<R>\<^sub>a (P \<lbrakk>A\<rbrakk> S) s \<Longrightarrow> X \<in> \<R>\<^sub>a (Q \<lbrakk>A\<rbrakk> S) s\<close> for s X
      by (simp add: D_Sync Refusals_after_def F_Sync, elim disjE)
        (metis F_T front_tickFree_Nil proc_ord2a[OF that] self_append_conv, blast)
  next
    show \<open>s \<notin> \<D> (P \<lbrakk>A\<rbrakk> S) \<Longrightarrow> X \<in> \<R>\<^sub>a (Q \<lbrakk>A\<rbrakk> S) s \<Longrightarrow> X \<in> \<R>\<^sub>a (P \<lbrakk>A\<rbrakk> S) s\<close> for s X
      apply (simp add: D_Sync Refusals_after_def F_Sync, elim disjE)
      using le_approx_lemma_F that apply blast
        (* TODO: break this smt *)
      by (smt (verit, ccfv_SIG) in_mono le_approx1 le_approx_lemma_T that)
  next
    fix s
    assume \<open>s \<in> min_elems (\<D> (P \<lbrakk>A\<rbrakk> S))\<close>
    hence \<open>s \<in> \<D> (P \<lbrakk>A\<rbrakk> S)\<close> by (simp add: elem_min_elems)
    then obtain t u r
      where * : \<open>r \<le> s\<close> \<open>t \<in> \<D> P \<and> u \<in> \<T> S \<or> t \<in> \<D> S \<and> u \<in> \<T> P\<close>
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
      by (simp add: D_Sync less_eq_list_def prefix_def) blast

    have \<open>\<exists>t u r. r \<le> s \<and> r setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                  (t \<in> min_elems (\<D> P) \<and> u \<in> \<T> S \<or> t \<in> min_elems (\<D> S) \<and> u \<in> \<T> P)\<close>
    proof (rule ccontr)
      assume assm : \<open>\<nexists>t u r1. r1 \<le> s \<and> r1 setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                              (t \<in> min_elems (\<D> P) \<and> u \<in> \<T> S \<or> t \<in> min_elems (\<D> S) \<and> u \<in> \<T> P)\<close>

      obtain tm1 tm2 where $: \<open>t \<in> \<D> P \<Longrightarrow> tm1 \<le> t \<and> tm1 \<in> min_elems (\<D> P)\<close>
        \<open>t \<in> \<D> S \<Longrightarrow> tm2 \<le> t \<and> tm2 \<in> min_elems (\<D> S)\<close>
        by (metis min_elems5)
      hence $$ : \<open>t \<in> \<D> P \<Longrightarrow> u \<in> \<T> S \<Longrightarrow> tm1 < t\<close> \<open>t \<in> \<D> S \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> tm2 < t\<close>
        by (metis "*"(1, 3) assm order_neq_le_trans)+
      then obtain um1 rm1 um2 rm2 where
        \<open>t \<in> \<D> P \<Longrightarrow> u \<in> \<T> S \<Longrightarrow> um1 \<le> u \<and> rm1 setinterleaves ((tm1, um1), range tick \<union> ev ` A)\<close>
        \<open>t \<in> \<D> S \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> um2 \<le> u \<and> rm2 setinterleaves ((tm2, um2), range tick \<union> ev ` A)\<close>
        by (metis "*"(3) interleave_less_left)
      moreover have \<open>t \<in> \<D> P \<Longrightarrow> u \<in> \<T> S \<Longrightarrow> rm1 < s \<and> rm1 \<in> \<D> (P \<lbrakk>A\<rbrakk> S)\<close>
        \<open>t \<in> \<D> S \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> rm2 < s \<and> rm2 \<in> \<D> (P \<lbrakk>A\<rbrakk> S)\<close>
        by (meson assm "$"(1, 2) "$$"(1, 2) "*"(1) "*"(3)
            interleave_le_left is_processT3_TR order_trans)+
      ultimately show False by (metis "*"(2) \<open>s \<in> min_elems (\<D> (P \<lbrakk>A\<rbrakk> S))\<close> less_list_def min_elems_no)
    qed

\<comment>\<open>We override.\<close>
    then obtain t u r
      where * : \<open>r \<le> s\<close> \<open>r setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
        \<open>t \<in> min_elems (\<D> P) \<and> u \<in> \<T> S \<or> t \<in> min_elems (\<D> S) \<and> u \<in> \<T> P\<close> by blast

    from "*"(2, 3) have \<open>r \<in> \<D> (P \<lbrakk>A\<rbrakk> S)\<close>
      by (simp add: D_Sync) (use elem_min_elems front_tickFree_Nil in blast)
    with "*"(1) \<open>s \<in> min_elems (\<D> (P \<lbrakk>A\<rbrakk> S))\<close> min_elems_no have \<open>s = r\<close> by blast

    have \<open>t \<in> \<D> S \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> u \<in> \<T> P - (\<D> P - min_elems (\<D> P))\<close>
    proof (rule ccontr)
      assume assms : \<open>t \<in> \<D> S\<close> \<open>u \<in> \<T> P\<close> \<open>u \<notin> \<T> P - (\<D> P - min_elems (\<D> P))\<close>
      from assms(2, 3) have \<open>u \<in> \<D> P\<close> \<open>u \<notin> min_elems (\<D> P)\<close> by simp_all
      then obtain u1 where \<open>u1 < u\<close> \<open>u1 \<in> min_elems (\<D> P)\<close> 
        by (metis min_elems5 order_neq_le_trans)

      obtain t1 r1 where \<open>t1 \<le> t\<close> \<open>r1 setinterleaves ((t1, u1), range tick \<union> ev ` A)\<close> \<open>r1 < r\<close>
        by (metis (no_types, lifting) "*"(2) \<open>u1 < u\<close> interleave_less_left setinterleaving_sym)
      from \<open>t1 \<le> t\<close> \<open>u1 \<in> min_elems (\<D> P)\<close> assms(1) have \<open>u1 \<in> \<D> P \<and> t1 \<in> \<T> S\<close>
        using D_T elem_min_elems is_processT3_TR by blast
      moreover have \<open>r1 \<in> \<D> (P \<lbrakk>A\<rbrakk> S)\<close>
        by (simp add: D_Sync)  
          (use \<open>r1 setinterleaves ((t1, u1), range tick \<union> ev ` A)\<close>
            \<open>u1 \<in> \<D> P \<and> t1 \<in> \<T> S\<close> front_tickFree_Nil setinterleaving_sym in blast)
      ultimately show False
        by (metis \<open>r1 < r\<close> \<open>s = r\<close> \<open>s \<in> min_elems (\<D> (P \<lbrakk>A\<rbrakk> S))\<close> less_list_def min_elems_no)
    qed

    hence \<open>\<exists>t u. s setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                (t \<in> min_elems (\<D> P) \<and> u \<in> \<T> S \<or> t \<in> min_elems (\<D> S) \<and>
                u \<in> \<T> P \<and> u \<in> \<T> P - (\<D> P - min_elems (\<D> P)))\<close>
      using "*"(2, 3) \<open>s = r\<close> elem_min_elems by blast
    thus \<open>s \<in> \<T> (Q \<lbrakk>A\<rbrakk> S)\<close>
      by (simp add: T_Sync)
        (metis (no_types) append.right_neutral elem_min_elems front_tickFree_Nil
          le_approx2T[OF \<open>P \<sqsubseteq> Q\<close>] \<open>P \<sqsubseteq> Q\<close>[unfolded le_approx_def] in_mono)
  qed
  thus \<open>P \<sqsubseteq> P' \<Longrightarrow> Q \<sqsubseteq> Q' \<Longrightarrow> P \<lbrakk>A\<rbrakk> Q \<sqsubseteq> P' \<lbrakk>A\<rbrakk> Q'\<close>
    by (metis Sync_commute below_trans)
qed



lemma chain_Sync_left  : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<lbrakk>A\<rbrakk> S)\<close>
  and chain_Sync_right : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. S \<lbrakk>A\<rbrakk> Y i)\<close>
  by (simp_all add: chain_def mono_Sync) 




lemma finite_interleaves: \<open>finite {(t, u). (s :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) setinterleaves ((t, u), A)}\<close>
proof (induction \<open>length s\<close> arbitrary: s rule: nat_less_induct)
  fix s :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assume hyp : \<open>\<forall>m < length s. \<forall>s. m = length s \<longrightarrow> finite {(t, u). s setinterleaves ((t, u), A)}\<close>
  show \<open>finite {(t, u). s setinterleaves ((t, u), A)}\<close>
  proof (cases s)
    have \<open>[] setinterleaves ((t, u), A) \<Longrightarrow> t = [] \<and> u = []\<close> for t u
      using EmptyLeftSync empty_setinterleaving by blast
    hence \<open>{(t, u). [] setinterleaves ((t, u), A)} = {([], [])}\<close> by auto
    thus \<open>s = [] \<Longrightarrow> finite {(t, u). s setinterleaves ((t, u), A)}\<close> by simp
  next
    fix x s'
    assume \<open>s = x # s'\<close>
    define S where \<open>S \<equiv> {(t, u). s' setinterleaves ((t, u), A)}\<close>
    with hyp \<open>s = x # s'\<close> have \<open>finite S\<close> by auto
    have \<open>s setinterleaves ((t, u), A) \<Longrightarrow>
          t \<noteq> [] \<and> hd t = x \<and> s' setinterleaves ((tl t,    u), A) \<or>
          u \<noteq> [] \<and> hd u = x \<and> s' setinterleaves ((   t, tl u), A) \<or>
          t \<noteq> [] \<and> hd t = x \<and> u \<noteq> [] \<and> hd u = x \<and>
          s' setinterleaves ((tl t, tl u), A)\<close> for t u
      by (cases t; cases u; simp add: \<open>s = x # s'\<close> split: if_split_asm) blast
    hence * : \<open>{(t, u). s setinterleaves ((t, u), A)} \<subseteq>
               {(t, u). t \<noteq> [] \<and> hd t = x \<and> s' setinterleaves ((tl t,    u), A)} \<union>
               {(t, u). u \<noteq> [] \<and> hd u = x \<and> s' setinterleaves ((   t, tl u), A)} \<union>
               {(t, u). t \<noteq> [] \<and> hd t = x \<and> u \<noteq> [] \<and> hd u = x \<and>
                         s' setinterleaves ((tl t, tl u), A)}\<close>
      (is \<open>{(t, u). s setinterleaves ((t, u), A)} \<subseteq> ?S1 \<union> ?S2 \<union> ?S3\<close>) by blast

    have \<open>?S1 = {(x # t, u)| t u. s' setinterleaves ((t, u), A)}\<close> by force
    also have \<open>\<dots> = (\<lambda>(t, u). (x # t, u)) ` S\<close> unfolding S_def by auto
    finally have \<open>finite ?S1\<close> by (simp add: \<open>finite S\<close>)

    have \<open>?S2 = {(t, x # u)| t u. s' setinterleaves ((t, u), A)}\<close> by force
    also have \<open>\<dots> = (\<lambda>(t, u). (t, x # u)) ` S\<close> unfolding S_def by auto
    finally have \<open>finite ?S2\<close> by (simp add: \<open>finite S\<close>)

    have \<open>?S3 = {(x # t, x # u)| t u. s' setinterleaves ((t, u), A)}\<close>
      by (simp add: set_eq_iff) (metis list.collapse list.distinct(1) list.sel(1, 3))
    also have \<open>\<dots> = (\<lambda>(t, u). (x # t, x # u)) ` S\<close> unfolding S_def by auto
    finally have \<open>finite ?S3\<close> by (simp add: \<open>finite S\<close>)

    from "*" \<open>finite ?S1\<close> \<open>finite ?S2\<close> \<open>finite ?S3\<close> finite_subset
    show \<open>finite {(t, u). s setinterleaves ((t, u), A)}\<close> by blast
  qed
qed


lemma finite_interleaves_Sync:
  \<open>finite {(t, u, r). r setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                      (\<exists>v. s = r @ v \<and> front_tickFree v \<and> (tickFree r \<or> v = []))}\<close>
  (is \<open>finite ?A\<close>)
proof -
  have \<open>?A \<subseteq> (\<Union>r\<in>{r. r \<le> s}. {(t, u, r) |t u. r setinterleaves ((t, u), range tick \<union> ev ` A)})\<close>
    (is \<open>?A \<subseteq> (\<Union>r \<in> {r. r \<le> s}. ?P r)\<close>)
    unfolding less_eq_list_def prefix_def by blast

  have \<open>?P r \<subseteq> (\<lambda>(t, u). (t, u, r)) `
                {(t, u). r setinterleaves ((t, u), range tick \<union> ev ` A)}\<close> for r by auto
  hence \<open>finite (?P r)\<close> for r by (rule finite_subset) (simp add: finite_interleaves)

  have \<open>{r. \<exists>v. s = r @ v} = {r. \<exists>v. r @ v = s}\<close> by blast
  hence \<open>finite {r. r \<le> s}\<close>
    by (fold prefix_def less_eq_list_def)
      (use prefixes_fin[of s, simplified Let_def] in presburger)

  show ?thesis
    by (rule finite_subset[OF \<open>?A \<subseteq> (\<Union>r \<in> {r. r \<le> s}. ?P r)\<close>]) 
      (rule finite_UN_I[OF \<open>finite {r. r \<le> s}\<close> \<open>\<And>r. finite (?P r)\<close>])
qed



lemma Cont_Sync_prem:
  \<open>(\<Squnion> i. Y i) \<lbrakk>A\<rbrakk> Q = (\<Squnion> i. Y i \<lbrakk>A\<rbrakk> Q)\<close> if chain: \<open>chain Y\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ((\<Squnion> i. Y i) \<lbrakk>A\<rbrakk> Q) \<Longrightarrow> s \<in> \<D> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> Q)\<close> for s
    by (simp add: limproc_is_thelub chain chain_Sync_left D_Sync D_LUB T_LUB) blast
next
  show \<open>(s, X) \<in> \<F> ((\<Squnion> i. Y i) \<lbrakk>A\<rbrakk> Q) \<Longrightarrow> (s, X) \<in> \<F> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> Q)\<close> for s X
    by (simp add: limproc_is_thelub chain chain_Sync_left F_Sync D_LUB T_LUB F_LUB) blast
next
  fix s
  assume \<open>s \<in> \<D> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> Q)\<close>
  define S 
    where \<open>S i \<equiv> {(t, u, r). \<exists>v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and> s = r @ v \<and>
                                   r setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                                   (t \<in> \<D> (Y i) \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> (Y i))}\<close> for i
  have \<open>(\<Inter>i. S i) \<noteq> {}\<close> 
    apply (rule Inter_nonempty_finite_chained_sets, unfold S_def)
      apply (use \<open>s \<in> \<D> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> Q)\<close> in
        \<open>simp add: limproc_is_thelub chain chain_Sync_left D_Sync T_LUB D_LUB, blast\<close>)
     apply (rule finite_subset[OF _ finite_interleaves_Sync]; auto)
    using D_T le_approx1[OF po_class.chainE[OF chain]]
      le_approx2T[OF po_class.chainE[OF chain]] by blast
  then obtain t u r where \<open>(t, u, r) \<in> (\<Inter>i. S i)\<close> by auto
  hence \<open>front_tickFree (drop (length r) s) \<and> (tickFree r \<or> drop (length r) s = []) \<and>
           s = r @ drop (length r) s \<and> r setinterleaves ((t, u), range tick \<union> ev ` A) \<and> 
           ((\<forall>i. t \<in> \<D> (Y i)) \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> (\<forall>i. u \<in> \<T> (Y i)))\<close>
    by (auto simp add: S_def) (meson chain_lemma le_approx1 le_approx_lemma_T subsetD chain)

  show \<open>s \<in> \<D> ((\<Squnion> i. Y i) \<lbrakk>A\<rbrakk> Q)\<close>
    by (simp add: limproc_is_thelub chain chain_Sync_left D_Sync T_LUB D_LUB)
      (use \<open>?this\<close> in blast)
next
  assume same_div : \<open>\<D> ((\<Squnion> i. Y i) \<lbrakk>A\<rbrakk> Q) = \<D> (\<Squnion> i. Y i \<lbrakk>A\<rbrakk> Q)\<close>
  fix s X assume \<open>(s, X) \<in> \<F> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> Q)\<close>
  show \<open>(s, X) \<in> \<F> ((\<Squnion> i. Y i) \<lbrakk>A\<rbrakk> Q)\<close>
  proof (cases \<open>s \<in> \<D> (\<Squnion> i. Y i \<lbrakk>A\<rbrakk> Q)\<close>)
    show \<open>s \<in> \<D> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> Q) \<Longrightarrow> (s, X) \<in> \<F> ((\<Squnion>i. Y i) \<lbrakk>A\<rbrakk> Q)\<close>
      by (simp add: is_processT8 same_div)
  next
    assume \<open>s \<notin> \<D> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> Q)\<close>
    then obtain j where \<open>s \<notin> \<D> (Y j \<lbrakk>A\<rbrakk> Q)\<close>
      by (auto simp add: limproc_is_thelub chain_Sync_left \<open>chain Y\<close> D_LUB)
    moreover from \<open>(s, X) \<in> \<F> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> Q)\<close> have \<open>(s, X) \<in> \<F> (Y j \<lbrakk>A\<rbrakk> Q)\<close>
      by (simp add: limproc_is_thelub chain_Sync_left \<open>chain Y\<close> F_LUB)
    ultimately show \<open>(s, X) \<in> \<F> ((\<Squnion> i. Y i) \<lbrakk>A\<rbrakk> Q)\<close>
      by (fact le_approx2[OF mono_Sync[OF is_ub_thelub[OF \<open>chain Y\<close>] below_refl], THEN iffD2])
  qed
qed



lemma Sync_cont[simp]: \<open>cont (\<lambda>x. f x \<lbrakk>A\<rbrakk> g x)\<close> if \<open>cont f\<close> \<open>cont g\<close>
proof (rule cont_apply[where f = \<open>\<lambda>x y. y \<lbrakk>A\<rbrakk> g x\<close>])
  from \<open>cont f\<close> show \<open>cont f\<close> .
next
  show \<open>cont (\<lambda>y. y \<lbrakk>A\<rbrakk> g x)\<close> for x
  proof (rule contI2)
    show \<open>monofun (\<lambda>y. y \<lbrakk>A\<rbrakk> g x)\<close> by (simp add: monofunI mono_Sync)
  next
    show \<open>chain Y \<Longrightarrow> (\<Squnion>i. Y i) \<lbrakk>A\<rbrakk> g x \<sqsubseteq> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk> g x)\<close> for Y
      by (simp add: Cont_Sync_prem)
  qed
next
  show \<open>cont (\<lambda>x. y \<lbrakk>A\<rbrakk> g x)\<close> for y
  proof (rule cont_compose[of \<open>\<lambda>x. y \<lbrakk>A\<rbrakk> x\<close>])
    show \<open>cont (Sync y A)\<close> 
    proof (rule contI2)
      show \<open>monofun (Sync y A)\<close> by (simp add: monofunI mono_Sync)
    next
      show \<open>chain Y \<Longrightarrow> y \<lbrakk>A\<rbrakk> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. y \<lbrakk>A\<rbrakk> Y i)\<close> for Y
        by (subst (1 2) Sync_commute) (simp add: Cont_Sync_prem)
    qed
  next
    from \<open>cont g\<close> show \<open>cont g\<close> .
  qed
qed


(*<*)
end
  (*>*)