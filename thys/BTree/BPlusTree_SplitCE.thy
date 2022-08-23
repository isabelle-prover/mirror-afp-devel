theory BPlusTree_SplitCE
  imports 
  BPlusTree_Set
  BPlusTree_Range
begin

global_interpretation bplustree_linear_search_list: split_list linear_split_list
  defines bplustree_ls_isin_list = bplustree_linear_search_list.isin_list
  and bplustree_ls_insert_list = bplustree_linear_search_list.insert_list
  and bplustree_ls_delete_list = bplustree_linear_search_list.delete_list
  and bplustree_ls_lrange_list = bplustree_linear_search_list.lrange_split
  apply unfold_locales
  unfolding linear_split.simps
    apply (auto split: list.splits)
  subgoal
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done

declare bplustree_linear_search_list.isin_list.simps[code]
declare bplustree_linear_search_list.insert_list.simps[code]
declare bplustree_linear_search_list.delete_list.simps[code]

(* interpretation bplustree_linear_search: split_tree linear_split
  apply unfold_locales
  unfolding linear_split.simps
    apply (auto split: list.splits)
  subgoal
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done *)

global_interpretation bplustree_linear_search:
    split_full linear_split linear_split_list 
  (* the below definitions are required to be set here for evaluating example code... *)
  defines bplustree_ls_isin = bplustree_linear_search.isin 
    and bplustree_ls_ins = bplustree_linear_search.ins
    and bplustree_ls_insert = bplustree_linear_search.insert
    and bplustree_ls_del = bplustree_linear_search.del
    and bplustree_ls_delete = bplustree_linear_search.delete
    and bplustree_ls_lrange = bplustree_linear_search.lrange
  apply unfold_locales
  unfolding linear_split.simps
  subgoal by (auto split: list.splits)
  subgoal
    apply (auto split: list.splits)
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done

lemma [code]: "bplustree_ls_isin (Leaf ks) x = bplustree_ls_isin_list x ks"
  by (simp add: bplustree_ls_isin_list_def)
declare bplustree_linear_search.isin.simps(2)[code]

lemma [code]: "bplustree_ls_ins k x (Leaf ks) =
bplustree_linear_search.Lnode\<^sub>i k (bplustree_ls_insert_list x ks)"
  by (simp add: bplustree_ls_insert_list_def)
declare bplustree_linear_search.ins.simps(2)[code]

lemma [code]: "bplustree_ls_del k x (Leaf ks) =
Leaf (bplustree_ls_delete_list x ks)"
  by (simp add: bplustree_ls_delete_list_def)
declare bplustree_linear_search.del.simps(2)[code]

find_theorems bplustree_ls_isin

text "Some examples follow to show that the implementation works
      and the above lemmas make sense. The examples are visualized in the thesis."

abbreviation "bplustree\<^sub>q \<equiv> bplustree_ls_isin"
abbreviation "bplustree\<^sub>i \<equiv> bplustree_ls_insert"
abbreviation "bplustree\<^sub>d \<equiv> bplustree_ls_delete"

definition "uint8_max \<equiv> 2^8-1::nat"
declare uint8_max_def[simp]

typedef uint8 = "{n::nat. n \<le> uint8_max}" 
  by auto

setup_lifting type_definition_uint8

instantiation uint8 :: linorder
begin

lift_definition less_eq_uint8 :: "uint8 \<Rightarrow> uint8 \<Rightarrow> bool"
  is "(less_eq::nat \<Rightarrow> nat \<Rightarrow> bool)" .

lift_definition less_uint8 :: "uint8 \<Rightarrow> uint8 \<Rightarrow> bool"
  is "(less::nat \<Rightarrow> nat \<Rightarrow> bool)" .

instance
  by standard (transfer; auto)+
end

instantiation uint8 :: order_top
begin

lift_definition top_uint8 :: uint8 is "uint8_max::nat"
  by simp


instance 
  by standard (transfer; simp)
end


instantiation uint8 :: numeral
begin

lift_definition one_uint8 :: uint8 is "1::nat"
  by auto

lift_definition plus_uint8 :: "uint8 \<Rightarrow> uint8 \<Rightarrow> uint8"
  is "\<lambda>a b. min (a + b) uint8_max"
  by simp

instance by standard (transfer; auto)
end

instantiation uint8 :: equal
begin

lift_definition equal_uint8 :: "uint8 \<Rightarrow> uint8 \<Rightarrow> bool"
  is "(=)" .

instance by standard (transfer; auto)
end


value "uint8_max"

value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [21,22,23]))) in
      root_order k x"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [21,22,23]))) in
      bal x"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      sorted_less (leaves x)"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      Laligned x top"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      x"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      bplustree\<^sub>q x 4"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      bplustree\<^sub>q x 20"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      bplustree\<^sub>i k 9 x"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      bplustree\<^sub>i k 1 (bplustree\<^sub>i k 9 x)"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      bplustree\<^sub>d k 10 (bplustree\<^sub>i k 1 (bplustree\<^sub>i k 9 x))"
value "let k=2::nat; x::uint8 bplustree = (Node [(Node [(Leaf [1,2], 2),(Leaf [3,4], 4),(Leaf [5,6,7], 8)] (Leaf [9,10]), 10)] (Node [(Leaf [11,12,13,14], 14), (Leaf [15,17], 20)] (Leaf [50,55,56]))) in
      bplustree\<^sub>d k 3 (bplustree\<^sub>d k 10 (bplustree\<^sub>i k 1 (bplustree\<^sub>i k 9 x)))"


end