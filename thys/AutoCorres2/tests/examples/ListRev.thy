(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ListRev
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "list_rev.c"

autocorres [heap_abs_syntax] "list_rev.c"

primrec
  list :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> bool"
where
  "list s p [] = (p = NULL)"
| "list s p (x#xs) = (
       p = x \<and> p \<noteq> NULL \<and> ptr_valid (heap_typing s) p \<and> list s (s[p]\<rightarrow>next) xs)"

lemma list_empty [simp]:
  "list s NULL xs = (xs = [])"
  by (induct xs) auto

lemma list_in [simp]:
  "\<lbrakk> list s p xs; p \<noteq> NULL \<rbrakk> \<Longrightarrow> p \<in> set xs"
  by (induct xs) auto

lemma list_non_NULL:
  "\<lbrakk> p \<noteq> NULL \<rbrakk> \<Longrightarrow>
    list s p xs = (\<exists>ys. xs = p # ys \<and> ptr_valid (heap_typing s) p \<and> list s (s[p]\<rightarrow>next) ys)"
  by (cases xs) auto

lemma list_unique:
  "list s p xs \<Longrightarrow> list s p ys \<Longrightarrow> xs = ys"
  by (induct xs arbitrary: p ys) (auto simp add: list_non_NULL)

lemma list_append_Ex:
  "list s p (xs @ ys) \<Longrightarrow> (\<exists>q. list s q ys)"
  by (induct xs arbitrary: p) auto

lemma list_distinct [simp]:
  "list s p xs \<Longrightarrow> distinct xs"
  apply (induct xs arbitrary: p)
   apply simp
  apply (clarsimp dest!: split_list)
  apply (frule list_append_Ex)
  apply (auto dest: list_unique)
  done

lemma list_heap_update_ignore [simp]:
  "q \<notin> set xs \<Longrightarrow> list (s[q\<rightarrow>next := v]) p xs = list s p xs"
  apply (induct xs arbitrary: p)
   apply clarsimp
  apply (clarsimp simp: fun_upd_def )
  done

definition
  the_list :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list"
where
  "the_list s p = (THE xs. list s p xs)"

lemma the_list_val [simp]: "list s p xs \<Longrightarrow> the_list s p = xs"
  apply (clarsimp simp: the_list_def)
  apply (metis (lifting) list_unique the_equality)
  done

lemma [simp]:
   "\<lbrakk> q \<notin> set xs; list s p xs \<rbrakk> \<Longrightarrow> the_list s[q\<rightarrow>next := v] p = the_list s p"
  apply (subgoal_tac "list s[q\<rightarrow>next := v] p xs")
   apply (metis the_list_val)
  apply clarsimp
  done

definition "reverse_inv xs list' rev' s =
                 (\<exists>ys zs. list s list' ys
                    \<and> list s rev' zs
                    \<and> rev xs = rev ys @ zs
                    \<and> distinct (rev xs))"

lemmas runs_to_whileLoop2 =  runs_to_whileLoop_res' [split_tuple C and B arity: 2]

lemma (in ts_definition_reverse) reverse_correct:
  "list s p xs \<Longrightarrow>
     reverse' p \<bullet> s
   \<lbrace> \<lambda>r s. \<exists>rv. r = Result rv \<and> list s rv (rev xs) \<rbrace>"
  unfolding reverse'_def
  apply (runs_to_vcg)
  apply (rule runs_to_whileLoop2 [where
        I="\<lambda>(list', rev') s. reverse_inv xs list' rev' s"
        and R="measure (\<lambda>((list', rev'), s). length (the_list s list'))",
        unfolded reverse_inv_def])
  subgoal by simp
  subgoal by simp
  subgoal by (simp split: prod.splits)
  supply distinct_rev[simp del]
    apply runs_to_vcg
    subgoal 
      using list_non_NULL by blast
    subgoal for p_ys p_zs s1 ys zs
      apply (case_tac ys, fastforce)
      apply clarsimp
      subgoal for ys'
        apply (rule_tac x=ys' in exI)
        apply (simp add: fun_upd_def)
        done
      done
    subgoal for p_ys p_zs s1 ys zs
      apply (case_tac ys, fastforce)
      apply clarsimp
      subgoal for ys'
        apply (subgoal_tac "the_list s1 p_ys = (p_ys#ys')")
         apply (simp only:)
         apply simp
        apply simp
        done
      done
    done

end
