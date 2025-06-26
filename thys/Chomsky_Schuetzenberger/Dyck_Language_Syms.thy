(* Author: Moritz Roos, Tobias Nipkow *)

section \<open>Dyck Languages over Type \<open>syms\<close>\<close>

theory Dyck_Language_Syms
imports
  Dyck_Language.Dyck_Language
  Context_Free_Grammar.Context_Free_Grammar
begin

section\<open>Versions of \<^const>\<open>bal\<close> and restriction to \<open>\<Gamma>\<close> for @{type syms}\<close>

subsection\<open>Function \<^term>\<open>bal_tm\<close>\<close>

definition bal_tm where
  \<open>bal_tm = bal o (map destTm) o (filter isTm)\<close>

lemma bal_tm_empty[simp]: \<open>bal_tm []\<close>
  by (simp add: bal_tm_def)

lemma bal_tm_append[simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm ys \<Longrightarrow> bal_tm (xs @ ys)\<close> 
  unfolding bal_tm_def by simp

lemma bal_tm_surr[simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (Tm (Open a) # xs @ [Tm (Close a)])\<close> 
  unfolding bal_tm_def by simp

lemma bal_tm_prepend_Nt[simp]: \<open>bal_tm (Nt A # xs) = bal_tm xs\<close> 
  by (simp add: bal_tm_def)

lemma bal_tm2[simp]: "bal_tm [Tm (Open a), Tm (Close a)]"
using bal_tm_surr[of "[]"] by simp

lemma bal_iff_bal_tm[simp]: \<open>bal_tm (map Tm xs) = bal xs\<close>
unfolding bal_tm_def by simp

lemma bal_tm_append_inv: "bal_tm (u @ v) \<Longrightarrow> bal_tm u \<Longrightarrow> bal_tm v"
unfolding bal_tm_def by(auto dest: bal_append_inv)

lemma bal_tm_inside: 
  "bal_tm b \<Longrightarrow> bal_tm (v @ b @ w) = bal_tm (v @ w)"
unfolding bal_tm_def by(auto)


subsection\<open>Function \<open>snds_in_tm\<close>\<close>

text\<open>Restriction to \<open>\<Gamma>\<close> for a list of symbols:\<close>

definition snds_in_tm where
  \<open>snds_in_tm \<Gamma> w = (snd ` set(map destTm (filter isTm w)) \<subseteq> \<Gamma>)\<close>

lemma snds_in_tm_Nt[simp]:
  \<open>snds_in_tm \<Gamma> (Nt A # xs) = snds_in_tm \<Gamma> xs\<close>
unfolding snds_in_tm_def by auto

lemma snds_in_tm_append[simp]:
  \<open>snds_in_tm \<Gamma> (xs@ys) = (snds_in_tm \<Gamma> xs \<and> snds_in_tm \<Gamma> ys)\<close>
unfolding snds_in_tm_def by auto

lemma Dyck_langI_tm[simp]:
  \<open>xs \<in> Dyck_lang \<Gamma> \<longleftrightarrow> bal_tm (map Tm xs) \<and> snds_in_tm \<Gamma> (map Tm xs)\<close>
unfolding bal_tm_def snds_in_tm_def by auto

(*
subsection\<open>Lifting \<^const>\<open>bal\<close> and \<^const>\<open>bal_stk\<close> to @{type syms}\<close>


subsubsection\<open>Function \<open>bal_stk_tm\<close>\<close>

text\<open>A version of \<^term>\<open>bal_stk\<close> but for a symbol list that might contain nonterminals (they are ignored via filtering).\<close>
definition bal_stk_tm :: "'t list \<Rightarrow> ('n, 't bracket) syms \<Rightarrow> 't list * ('n, 't bracket) syms" where
\<open>bal_stk_tm x y \<equiv>
  (fst ((bal_stk x o map destTm o filter isTm) y), map Tm (snd ((bal_stk x o map destTm o filter isTm) y)))\<close>

lemma bal_stk_tm_append:
  "bal_stk_tm s1 (xs @ ys) = (let (s1',xs') = bal_stk_tm s1 xs in bal_stk_tm s1' (xs' @ ys))"
unfolding bal_stk_tm_def
apply simp
by (metis (no_types, lifting) bal_stk_append split_beta)

lemma bal_stk_tm_append_if[simp]:
  "bal_stk_tm s1 xs = (s2,[]) \<Longrightarrow> bal_stk_tm s1 (xs @ ys) = bal_stk_tm s2 ys"
by(simp add: bal_stk_tm_append[of _ xs])

lemma bal_stk_tm_if_bal_tm: "bal_tm xs \<Longrightarrow> bal_stk_tm s xs = (s,[])"
  unfolding bal_stk_tm_def 
  by (simp add: bal_tm_def bal_stk_if_bal)+

lemma bal_tm_insert_AB: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Tm (Open x) # Tm (Close x) # w)" using u
unfolding bal_tm_def by (auto intro!: bal_insert_AB)

lemma bal_tm_insert_Nt: "bal_tm u \<Longrightarrow> u = v@w \<Longrightarrow> bal_tm (v @ Nt A # w)"
unfolding bal_tm_def by auto

corollary bal_stk_tm_iff_bal_tm: "bal_stk_tm [] w = ([],[]) \<longleftrightarrow> bal_tm w"
  unfolding bal_stk_tm_def bal_tm_def o_def
  by (metis bal_stk_iff_bal map_is_Nil_conv split_pairs)

lemma bal_stk_tm_append_inv:
  \<open>bal_stk_tm s1 (xs@ys) = (s1', []) \<Longrightarrow>
  let (s1', xs') = bal_stk_tm s1 xs in bal_stk_tm s1 xs = (s1', [])\<close>
  unfolding bal_stk_tm_def Let_def apply auto 
  by (smt (verit, del_insts) case_prodE sndI bal_stk_append_inv surjective_pairing)
*)

end