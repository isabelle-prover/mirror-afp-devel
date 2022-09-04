theory BPlusTree_Split
imports BPlusTree
begin

subsection "Auxiliary functions"

(* a version of split half that assures the left side to be non-empty *)
fun split_half:: "_ list \<Rightarrow> _ list \<times> _ list" where
  "split_half xs = (take ((length xs + 1) div 2) xs, drop ((length xs + 1) div 2) xs)"

lemma split_half_conc: "split_half xs = (ls, rs) = (xs = ls@rs \<and> length ls = (length xs + 1) div 2)"
  by force

lemma drop_not_empty: "xs \<noteq> [] \<Longrightarrow> drop (length xs div 2) xs \<noteq> []"
  apply(induction xs)
   apply(auto split!: list.splits)
  done

lemma take_not_empty: "xs \<noteq> [] \<Longrightarrow> take ((length xs + 1) div 2) xs \<noteq> []"
  apply(induction xs)
   apply(auto split!: list.splits)
  done

lemma split_half_not_empty: "length xs \<ge> 1 \<Longrightarrow> \<exists>ls a rs. split_half xs = (ls@[a],rs)"
  using take_not_empty
  by (metis (no_types, opaque_lifting) Ex_list_of_length One_nat_def le_trans length_Cons list.size(4) nat_1_add_1 not_one_le_zero rev_exhaust split_half.simps take0 take_all_iff)

subsection "The split function locale"

text "Here, we abstract away the inner workings of the split function
      for B-tree operations."

lemma leaves_conc: "leaves (Node (ls@rs) t) = leaves_list ls @ leaves_list rs @ leaves t"
  apply(induction ls)
  apply auto
  done

locale split_tree =
  fixes split ::  "('a bplustree\<times>'a::{linorder,order_top}) list \<Rightarrow> 'a \<Rightarrow> (('a bplustree\<times>'a) list \<times> ('a bplustree\<times>'a) list)"
  assumes split_req:
    "\<lbrakk>split xs p = (ls,rs)\<rbrakk> \<Longrightarrow> xs = ls @ rs"
    "\<lbrakk>split xs p = (ls@[(sub,sep)],rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> sep < p"
    "\<lbrakk>split xs p = (ls,(sub,sep)#rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> p \<le> sep"
begin

  lemmas split_conc = split_req(1)
  lemmas split_sorted = split_req(2,3)
  
  
  lemma [termination_simp]:"(ls, (sub, sep) # rs) = split ts y \<Longrightarrow>
        size sub < Suc (size_list (\<lambda>x. Suc (size (fst x))) ts  + size l)"
    using split_conc[of ts y ls "(sub,sep)#rs"] by auto

  
  lemma leaves_split: "split ts x = (ls,rs) \<Longrightarrow> leaves (Node ts t) = leaves_list ls @ leaves_list rs @ leaves t"
    using leaves_conc split_conc by blast

end

locale split_list =
  fixes split_list ::  "('a::{linorder,order_top}) list \<Rightarrow> 'a \<Rightarrow> 'a list \<times> 'a list"
  assumes split_list_req:
    "\<lbrakk>split_list ks p = (kls,krs)\<rbrakk> \<Longrightarrow> ks = kls @ krs"
    "\<lbrakk>split_list ks p = (kls@[sep],krs); sorted_less ks\<rbrakk> \<Longrightarrow> sep < p"
    "\<lbrakk>split_list ks p = (kls,(sep)#krs); sorted_less ks\<rbrakk> \<Longrightarrow> p \<le> sep"

locale split_full = split_tree: split_tree split + split_list split_list
    for split::
      "('a bplustree \<times> 'a::{linorder,order_top}) list \<Rightarrow> 'a
         \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list"
    and split_list::
      "'a::{linorder,order_top} list \<Rightarrow> 'a
         \<Rightarrow> 'a list \<times> 'a list"

section "Abstract split functions"

subsection "Linear split"

text "Finally we show that the split axioms are feasible by providing an example split function"

text "Linear split is similar to well known functions, therefore a quick proof can be done."

fun linear_split where "linear_split xs x = (takeWhile (\<lambda>(_,s). s<x) xs, dropWhile (\<lambda>(_,s). s<x) xs)"
fun linear_split_list where "linear_split_list xs x = (takeWhile (\<lambda>s. s<x) xs, dropWhile (\<lambda>s. s<x) xs)"

(* works but inhibits code extraction *)

(*interpretation bplustree_linear_search_list: split_list linear_split_list
  apply unfold_locales
  unfolding linear_split.simps
    apply (auto split: list.splits)
  subgoal
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done *)

(* interpretation bplustree_linear_search: split_tree linear_split
  apply unfold_locales
  unfolding linear_split.simps
    apply (auto split: list.splits)
  subgoal
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done *)
end