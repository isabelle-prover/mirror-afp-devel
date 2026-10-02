
(*
Title:  Definitions and Lemmas Related to Lists and the Option-Type
Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Robert Colvin <r.colvin@uq.edu.au>
               Peter Hoefner <peter@hoefner-online.de>
               Roger Su <roger.c.su@proton.me>
*)

section \<open>Helpers\<close>

text \<open>This section contains all the helpers that are independent of
@{text queue_contract}, @{text prefix_before} and @{text suffix_after}.\<close>

theory Helpers_Lists_Option
imports "HOL-Library.Sublist"
begin

(*==================================================================*)
subsection \<open>List-Related\<close>

abbreviation at_head :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "at_head i xs \<equiv> i \<in> set xs \<and> hd xs = i"

lemma at_head_append: "at_head x ys \<Longrightarrow> at_head x (ys @ [y])"
  using length_pos_if_in_set by fastforce

lemma at_head_append_equiv: "at_head x (ys @ [y]) \<longleftrightarrow> at_head x ys \<or> ys = [] \<and> y = x "
  apply auto
  apply (metis append.left_neutral hd_append2 list.sel(1))
  by (meson at_head_append)

lemma at_head_tl:
  "\<lbrakk> distinct xs ; at_head i xs \<rbrakk> \<Longrightarrow> i \<notin> set (tl xs)"
  by (metis distinct.simps(2) empty_iff empty_set list.exhaust_sel)

lemma in_queue_not_hd_pred:
  "\<lbrakk> i \<in> set xs ; i \<noteq> hd xs \<rbrakk> \<Longrightarrow> \<exists> j. sublist [j,i] xs"
  apply (induction xs)
   apply simp
  apply clarsimp
  by (metis Cons_prefix_Cons append_Nil append_one_prefix hd_conv_nth
            length_pos_if_in_set less_numeral_extra(3) list.size(3)
            prefixI sublist_Cons_right)

lemma in_queue_not_hd_pred_distinct:
  "\<lbrakk> distinct xs ; i \<in> set xs ; i \<noteq> hd xs \<rbrakk> \<Longrightarrow> \<exists> j. j \<noteq> i \<and> sublist [j,i] xs"
  using in_queue_not_hd_pred
  by (metis distinct_append distinct_length_2_or_more sublist_def)

lemma sublist_ij_hd_tl:
  "\<lbrakk> distinct xs ; sublist [i,j] xs ; at_head i xs \<rbrakk> \<Longrightarrow> j = hd (tl xs)"
  unfolding sublist_def
  by (metis append_Cons append_self_conv2 at_head_tl in_set_conv_decomp
            list.sel(1) list.sel(3) tl_append2)

lemma sublist_ij_not_last:
  "\<lbrakk> sublist [i,j] (xs @ [k]) ; j \<noteq> k \<rbrakk> \<Longrightarrow> sublist [i,j] xs"
  by (simp add: sublist_snoc)

lemma sublist_ij_explicit:
  "sublist [i,j] xs \<longleftrightarrow> (\<exists> ps ss. ps @ i # j # ss = xs)"
  apply standard
   apply (metis Cons_eq_appendI sublist_def)
  by (metis Cons_prefix_Cons append_Nil prefixI prefix_imp_sublist sublist_append)

lemma sublist_ij_j_not_hd:
  "\<lbrakk> distinct xs ; sublist [i,j] xs \<rbrakk> \<Longrightarrow> j \<noteq> hd xs"
  apply (induction xs)
   apply simp
  apply clarsimp
  by (metis Cons_prefix_Cons list.distinct(1) list.sel(1,3) list.set_sel(1,2)
            prefix_imp_sublist set_mono_sublist sublist_Cons_right subsetD)

lemma sublist_ij_i_not_last:
  "\<lbrakk> distinct xs ; sublist [i,j] xs \<rbrakk> \<Longrightarrow> i \<noteq> last xs"
  apply (induction xs)
   apply simp
  apply clarsimp
  by (metis Cons_prefix_Cons impossible_Cons last_in_set
            sublist_Cons_right sublist_length_le)

lemma tl_preserves_sublist:
  "sublist [i,j] (tl xs) \<Longrightarrow> sublist [i,j] xs"
  using sublist_order.order.trans by blast

lemma sublist_ij_holds_on_tl:
  "\<lbrakk> sublist [i,j] xs ; i \<in> set (tl xs) ; distinct xs \<rbrakk>
  \<Longrightarrow> sublist [i,j] (tl xs)"
  by (metis Cons_prefix_Cons Nil_tl at_head_tl list.exhaust_sel list.set_intros(1) sublist_Cons_right)

(*------------------------------------------------------------------*)
lemma suffix_same_last:
  "\<lbrakk> xs \<noteq> [] ; suffix xs ys \<rbrakk> \<Longrightarrow> last xs = last ys"
  by (metis last_appendR suffix_def)

lemma sublist_ij_snoc_suffix:
  "\<lbrakk> sublist [j, i] (xs @ [i]) ; i \<notin> set xs \<rbrakk> \<Longrightarrow> suffix [j, i] (xs @ [i])"
  by (metis list.set_intros(1) set_subset_Cons subsetD sublist_snoc set_mono_sublist)

lemma last_snoc:
  "\<lbrakk> i \<in> set xs ; i = last xs \<rbrakk> \<Longrightarrow> \<exists> ys. xs = ys @ [i]"
  by (metis append_butlast_last_id empty_iff list.set(1))

(*==================================================================*)
subsection \<open>Option-Related\<close>

text \<open>Function-application and -update on values of the option-type.\<close>

fun fun_appl_opt :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b" where
  "fun_appl_opt f xs = (case xs of
    None \<Rightarrow> undefined
  | Some x \<Rightarrow> f x)"

fun fun_upd_opt :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" where
  "fun_upd_opt f xo z = (case xo of
    None \<Rightarrow> undefined
  | Some x \<Rightarrow> fun_upd f x z)"

(*------------------------------------------------------------------*)
text \<open>The analogues of the @{term hd} and @{term last} functions,
adapted to the option-type.\<close>

fun opt_hd :: "'a list \<Rightarrow> 'a option" where
    "opt_hd [] = None"
  | "opt_hd (x # xs) = Some x"

fun opt_last :: "'a list \<Rightarrow> 'a option" where
    "opt_last [] = None"
  | "opt_last [x] = Some x"
  | "opt_last (_ # xs) = opt_last xs"

lemma opt_hd_some: "opt_hd xs = Some x \<Longrightarrow> at_head x xs"
  by (cases xs; simp)

lemma hd_and_opt_hd: "xs \<noteq> [] \<longleftrightarrow> opt_hd xs = Some (hd xs)"
  by (metis list.exhaust_sel option.distinct(1) opt_hd.simps)

lemma last_and_opt_last: "xs \<noteq> [] \<longleftrightarrow> opt_last xs = Some (last xs)"
  apply (induction xs; simp)
  by (metis list.exhaust_sel opt_last.simps(3))

lemma opt_last_some: "opt_last xs = Some x \<Longrightarrow> x \<in> set xs"
  apply (induction xs; simp)
  using opt_last.elims by force

lemma opt_last_some_nonempty: "opt_last xs = None  \<longleftrightarrow>  xs = []"
  by (metis last_and_opt_last opt_last.simps(1) option.simps(3))

lemma opt_last_some_last: "opt_last xs = Some x  \<longleftrightarrow>  xs \<noteq> [] \<and> last xs = x"
  by (metis last_and_opt_last opt_last.simps(1) option.discI option.sel)

lemma sublist_ij_opt_last:
  "\<lbrakk> sublist [i,j] (xs @ [j]) ; j \<notin> set xs \<rbrakk> \<Longrightarrow> opt_last xs = Some i"
  by (smt (verit, best) butlast.simps(2) last_and_opt_last list.discI
      opt_last.simps(2) snoc_eq_iff_butlast sublist_code(2) sublist_ij_snoc_suffix 
      suffix_imp_sublist suffix_same_last suffix_snoc)

lemma opt_last_at_head:
  "\<lbrakk> opt_last xs = Some i ; at_head i xs ; distinct xs \<rbrakk> \<Longrightarrow> xs = [i]"
  by (metis at_head_tl last.simps last_in_set list.exhaust_sel opt_last_some_last)
(*
  apply (induction xs; simp)
  by (metis last_ConsR last_and_opt_last list.discI opt_last_some)
*)
lemma opt_last_at_head_j:
  "\<lbrakk> opt_last xs = Some i ; at_head i xs ; distinct xs ; i \<noteq> j \<rbrakk>
  \<Longrightarrow> j \<notin> set xs"
  using opt_last_at_head
  by (metis empty_iff list.set(1) set_ConsD)

lemma opt_last_not_none:
  "\<lbrakk> opt_last xs \<noteq> Some i ; i \<in> set xs \<rbrakk> \<Longrightarrow> \<exists> j. sublist [i,j] xs"
  by (metis (no_types, opaque_lifting)
      Nil_is_append_conv in_set_conv_decomp last_and_opt_last last_appendR
      list.exhaust opt_last.simps(2) sublist_ij_explicit)

lemma opt_last_none:
  "opt_last xs = None \<Longrightarrow> xs = []"
  by (metis last_and_opt_last option.distinct(1))

lemma opt_last_prefix_ij:
  "\<lbrakk> distinct xs ; prefix [i,j] xs \<rbrakk> \<Longrightarrow> opt_last xs \<noteq> Some i"
  unfolding prefix_def using opt_last_some by fastforce

lemma tl_same_opt_last:
  "tl xs \<noteq> [] \<Longrightarrow> opt_last xs = opt_last (tl xs)"
  by (metis last_and_opt_last last_tl tl_Nil)

end