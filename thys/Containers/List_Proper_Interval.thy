(*  Title:      Containers/List_Proper_Interval.thy
    Author:     Andreas Lochbihler, ETH Zurich *)

theory List_Proper_Interval imports
  "HOL-Library.List_Lexorder"
  Collection_Order
begin

section \<open>Instantiate @{class proper_interval} of for @{typ "'a list"}\<close>

lemma Nil_less_conv_neq_Nil: "[] < xs \<longleftrightarrow> xs \<noteq> []"
by(cases xs) simp_all

lemma less_append_same_iff:
  fixes xs :: "'a :: preorder list"
  shows "xs < xs @ ys \<longleftrightarrow> [] < ys"
by(induct xs) simp_all

lemma less_append_same2_iff:
  fixes xs :: "'a :: preorder list"
  shows "xs @ ys < xs @ zs \<longleftrightarrow> ys < zs"
by(induct xs) simp_all

lemma Cons_less_iff:
  fixes x :: "'a :: preorder" shows
  "x # xs < ys \<longleftrightarrow> (\<exists>y ys'. ys = y # ys' \<and> (x < y \<or> x = y \<and> xs < ys'))"
by(cases ys) auto

instantiation list :: ("{proper_interval, order}") proper_interval begin

definition proper_interval_list_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where proper_interval_list_aux_correct:
  "proper_interval_list_aux xs ys \<longleftrightarrow> (\<exists>zs. xs < zs \<and> zs < ys)"

lemma proper_interval_list_aux_simp_1: 
  "proper_interval_list_aux xs [] \<longleftrightarrow> False"
  by (simp add: proper_interval_list_aux_correct)

lemma proper_interval_list_aux_simp_2:
  "proper_interval_list_aux [] (y # ys) \<longleftrightarrow> ys \<noteq> [] \<or> proper_interval None (Some y)"
  apply(auto simp add: proper_interval_list_aux_correct proper_interval_simps Nil_less_conv_neq_Nil)
  apply (metis Cons_less_Cons neq_Nil_conv not_less_Nil)
  by (metis Cons_less_Cons Nil_less_Cons neq_Nil_conv)

lemma proper_interval_list_aux_simp_3: 
  "proper_interval_list_aux (x # xs) (y # ys) \<longleftrightarrow> (if x = y then proper_interval_list_aux xs ys else x < y)"
    apply(auto simp add: proper_interval_list_aux_correct proper_interval_simps Nil_less_conv_neq_Nil Cons_less_iff)
  apply fastforce
  by (metis Cons_less_Cons Nil_less_Cons less_append_same_iff)

lemmas proper_interval_list_aux_simps [code] = 
  proper_interval_list_aux_simp_1 proper_interval_list_aux_simp_2 proper_interval_list_aux_simp_3

fun proper_interval_list :: "'a list option \<Rightarrow> 'a list option \<Rightarrow> bool" where
  "proper_interval_list None None \<longleftrightarrow> True"
| "proper_interval_list None (Some xs) \<longleftrightarrow> (xs \<noteq> [])"
| "proper_interval_list (Some xs) None \<longleftrightarrow> True"
| "proper_interval_list (Some xs) (Some ys) \<longleftrightarrow> proper_interval_list_aux xs ys"
instance
proof(intro_classes)
  fix xs ys :: "'a list"
  show "proper_interval None (Some ys) \<longleftrightarrow> (\<exists>zs. zs < ys)"
    by(auto simp add: Nil_less_conv_neq_Nil intro: exI[where x="[]"])
  show "proper_interval (Some xs) None \<longleftrightarrow> (\<exists>zs. xs < zs)"
    by(simp add: exI[where x="xs @ [undefined]"] less_append_same_iff)
  show "proper_interval (Some xs) (Some ys) \<longleftrightarrow> (\<exists>zs. xs < zs \<and> zs < ys)"
    by(simp add: proper_interval_list_aux_correct)
qed simp
end

end
