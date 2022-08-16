theory BPlusTree_ImpSplit
  imports
    BPlusTree_Imp
    BPlusTree_Split
    Imperative_Loops
begin

definition "split_relation xs \<equiv>
   \<lambda>(as,bs) i. i \<le> length xs \<and> as = take i xs \<and> bs = drop i xs"

lemma split_relation_alt: 
  "split_relation as (ls,rs) i = (as = ls@rs \<and> i = length ls)"
  by (auto simp add: split_relation_def)


lemma split_relation_length: "split_relation xs (ls,rs) (length xs) = (ls = xs \<and> rs = [])"
  by (simp add: split_relation_def)

(* auxiliary lemmas on assns *)
(* simp? not sure if it always makes things more easy *)
lemma list_assn_prod_map: "list_assn (A \<times>\<^sub>a B) xs ys = list_assn B (map snd xs) (map snd ys) * list_assn A (map fst xs) (map fst ys)"
  apply(induct "(A \<times>\<^sub>a B)" xs ys rule: list_assn.induct)
     apply(auto simp add: ab_semigroup_mult_class.mult.left_commute ent_star_mono star_aci(2) star_assoc)
  done

(* concrete *)
lemma id_assn_list: "h \<Turnstile> list_assn id_assn (xs::'a list) ys \<Longrightarrow> xs = ys"
  apply(induction "id_assn::('a \<Rightarrow> 'a \<Rightarrow> assn)" xs ys rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj pure_def)
  done

lemma id_assn_list_alt: "list_assn id_assn (xs::'a list) ys = \<up>(xs = ys)"
  apply(induction "id_assn::('a \<Rightarrow> 'a \<Rightarrow> assn)" xs ys rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj pure_def)
  done


lemma snd_map_help:
  "x \<le> length tsi \<Longrightarrow>
       (\<forall>j<x. snd (tsi ! j) = ((map snd tsi)!j))"
  "x < length tsi \<Longrightarrow> snd (tsi!x) = ((map snd tsi)!x)"
  by auto


lemma split_ismeq: "((a::nat) \<le> b \<and> X) = ((a < b \<and> X) \<or> (a = b \<and> X))"
  by auto

lemma split_relation_map: "split_relation as (ls,rs) i \<Longrightarrow> split_relation (map f as) (map f ls, map f rs) i"
  apply(induction as arbitrary: ls rs i)
   apply(auto simp add: split_relation_def take_map drop_Cons')
  apply(metis list.simps(9) take_map)
  done

lemma split_relation_access: "\<lbrakk>split_relation as (ls,rs) i; rs = r#rrs\<rbrakk> \<Longrightarrow> as!i = r"
  by (simp add: split_relation_alt)



lemma index_to_elem_all: "(\<forall>j<length xs. P (xs!j)) = (\<forall>x \<in> set xs. P x)"
  by (simp add: all_set_conv_nth)

lemma index_to_elem: "n < length xs \<Longrightarrow> (\<forall>j<n. P (xs!j)) = (\<forall>x \<in> set (take n xs). P x)"
  by (simp add: all_set_conv_nth)
    (* ----------------- *)

definition split_half :: "'a::heap pfarray \<Rightarrow> nat Heap"
  where
    "split_half a \<equiv> do {
  l \<leftarrow> pfa_length a;
  return ((l + 1) div 2)
}"

lemma split_half_rule[sep_heap_rules]: "<
    is_pfa c tsi a>
    split_half a
  <\<lambda>i. 
      is_pfa c tsi a
    * \<up>(i = (length tsi + 1) div 2 \<and>  split_relation tsi (BPlusTree_Split.split_half tsi) i)>"
  unfolding split_half_def split_relation_def
  apply(rule hoare_triple_preI)
  apply(sep_auto dest!: list_assn_len mod_starD)
  done


subsection "The imperative split locale"

locale split\<^sub>i_tree = abs_split_tree: BPlusTree_Split.split_tree split
  for split::
    "('a::{heap,default,linorder,order_top} bplustree \<times> 'a) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" +
  fixes split\<^sub>i:: "('a btnode ref option \<times> 'a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes split\<^sub>i_rule [sep_heap_rules]:"sorted_less (separators ts) \<Longrightarrow>
  length tsi = length rs \<Longrightarrow>
  tsi'' = zip (zip (map fst tsi) (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi) \<Longrightarrow>
 <is_pfa c tsi (a,n) 
  * blist_assn k ts tsi'' > 
    split\<^sub>i (a,n) p 
  <\<lambda>i. 
    is_pfa c tsi (a,n)
    * blist_assn k ts tsi''
    * \<up>(split_relation ts (split ts p) i)>\<^sub>t"

locale split\<^sub>i_list = abs_split_list: split_list split_list
  for split_list::
    "('a::{heap,default,linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> 'a list \<times> 'a list" +
  fixes split\<^sub>i_list:: "('a::{heap,default,linorder,order_top}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes split\<^sub>i_list_rule [sep_heap_rules]: "sorted_less xs \<Longrightarrow>
   <is_pfa c xs (a,n)> 
    split\<^sub>i_list (a,n) p 
  <\<lambda>i. 
    is_pfa c xs (a,n)
    * \<up>(split_relation xs (split_list xs p) i)>\<^sub>t"


locale split\<^sub>i_full = split\<^sub>i_tree: split\<^sub>i_tree split + split\<^sub>i_list: split\<^sub>i_list split_list
    for split::
      "('a bplustree \<times> 'a::{linorder,heap,default,order_top}) list \<Rightarrow> 'a
         \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list"
    and split_list::
      "'a::{default,linorder,order_top,heap} list \<Rightarrow> 'a
         \<Rightarrow> 'a list \<times> 'a list"

section "Imperative split operations"

text "So far, we have only given a functional specification of a possible split.
      We will now provide imperative split functions that refine the functional specification.
      However, rather than tracing the execution of the abstract specification,
      the imperative versions are implemented using while-loops."


subsection "Linear split"

text "The linear split is the most simple split function for binary trees.
      It serves a good example on how to use while-loops in Imperative/HOL
      and how to prove Hoare-Triples about its application using loop invariants."

definition lin_split :: "('a::heap \<times> 'b::{heap,linorder}) pfarray \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "lin_split \<equiv> \<lambda> (a,n) p. do {
  
  i \<leftarrow> heap_WHILET 
    (\<lambda>i. if i<n then do {
      (_,s) \<leftarrow> Array.nth a i;
      return (s<p)
    } else return False) 
    (\<lambda>i. return (i+1)) 
    0;
       
  return i
}"


lemma lin_split_rule: "
< is_pfa c xs (a,n)>
 lin_split (a,n) p
 <\<lambda>i. is_pfa c xs (a,n) * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p) \<and> (i<n \<longrightarrow> snd (xs!i)\<ge>p))>\<^sub>t"
  unfolding lin_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>i. n - i)"
      and I = "\<lambda>i. is_pfa c xs (a,n) * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p))"
      and b = "\<lambda>i. i<n \<and> snd (xs!i) < p"
      and Q="\<lambda>i. is_pfa c xs (a,n) * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p) \<and> (i<n \<longrightarrow> snd (xs!i)\<ge>p))"
      ]
  thm R

  apply (sep_auto  decon: R simp: less_Suc_eq is_pfa_def) []
       apply (metis nth_take snd_eqD)
      apply (metis nth_take snd_eqD)
     apply (sep_auto simp: is_pfa_def less_Suc_eq)+
      apply (metis nth_take)
    apply(sep_auto simp: is_pfa_def)
  apply (metis le_simps(3) less_Suc_eq less_le_trans nth_take)
  apply(sep_auto simp: is_pfa_def)+
  done

subsection "Binary split"

text "To obtain an efficient B-Tree implementation, we prefer a binary split
function.
To explore the searching procedure
and the resulting proof, we first implement the split on singleton arrays."

definition bin'_split :: "'b::{heap,linorder} array_list \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "bin'_split \<equiv> \<lambda>(a,n) p. do {
  (low',high') \<leftarrow> heap_WHILET 
    (\<lambda>(low,high). return (low < high)) 
    (\<lambda>(low,high). let mid = ((low  + high) div 2) in
     do {
      s \<leftarrow> Array.nth a mid;
      if p < s then
         return (low, mid)
      else if p > s then
         return (mid+1, high)
      else return (mid,mid)
     }) 
    (0::nat,n);
  return low'
}"


thm sorted_wrt_nth_less

(* alternative: replace (\<forall>j<l. xs!j < p) by (l > 0 \<longrightarrow> xs!(l-1) < p)*)
lemma bin'_split_rule: "
sorted_less xs \<Longrightarrow>
< is_pfa c xs (a,n)>
 bin'_split (a,n) p
 <\<lambda>l. is_pfa c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (l<n \<longrightarrow> xs!l\<ge>p)) >\<^sub>t"
  unfolding bin'_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>(l,h). h-l)"
      and I = "\<lambda>(l,h). is_pfa c xs (a,n) * \<up>(l\<le>h \<and> h \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (h<n \<longrightarrow> xs!h\<ge>p))"
      and b = "\<lambda>(l,h). l<h"
      and Q="\<lambda>(l,h). is_pfa c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (l<n \<longrightarrow> xs!l\<ge>p))"
      ]
  thm R

  apply (sep_auto decon: R simp: less_Suc_eq is_pfa_def) []
  subgoal for l' aa l'a aaa ba j
  proof -
    assume 0: "n \<le> length l'a"
    assume a: "l'a ! ((aa + n) div 2) < p"
    moreover assume "aa < n"
    ultimately have b: "((aa+n)div 2) < n"
      by linarith
    then have "(take n l'a) ! ((aa + n) div 2) < p"
      using a by auto
    moreover assume "sorted_less (take n l'a)"
    ultimately have "\<And>j. j < (aa+n)div 2 \<Longrightarrow> (take n l'a) ! j < (take n l'a) ! ((aa + n) div 2)"
      using
        sorted_wrt_nth_less[where ?P="(<)" and xs="(take n l'a)" and ?j="((aa + n) div 2)"]
        a b "0" by auto
    moreover fix j assume "j < (aa+n) div 2"
    ultimately show "l'a ! j < p" using "0" b
      using \<open>take n l'a ! ((aa + n) div 2) < p\<close> dual_order.strict_trans by auto
  qed
  subgoal for l' aa b l'a aaa ba j
  proof -
    assume t0: "n \<le> length l'a"
    assume t1: "aa < b"
    assume a: "l'a ! ((aa + b) div 2) < p"
    moreover assume "b \<le> n"
    ultimately have b: "((aa+b)div 2) < n" using t1
      by linarith
    then have "(take n l'a) ! ((aa + b) div 2) < p"
      using a by auto
    moreover assume "sorted_less (take n l'a)"
    ultimately have "\<And>j. j < (aa+b)div 2 \<Longrightarrow> (take n l'a) ! j < (take n l'a) ! ((aa + b) div 2)"
      using
        sorted_wrt_nth_less[where ?P="(<)" and xs="(take n l'a)" and ?j="((aa + b) div 2)"]
        a b t0 by auto
    moreover fix j assume "j < (aa+b) div 2"
    ultimately show "l'a ! j < p" using t0 b
      using \<open>take n l'a ! ((aa + b) div 2) < p\<close> dual_order.strict_trans by auto
  qed
     apply sep_auto
      apply (metis le_less nth_take)
     apply (metis le_less nth_take)
    apply sep_auto
  subgoal for l' aa l'a aaa ba j
  proof -
    assume t0: "aa < n"
    assume t1: " n \<le> length l'a"
    assume t4: "sorted_less (take n l'a)"
    assume t5: "j < (aa + n) div 2"
    have "(aa+n) div 2 < n" using t0 by linarith
    then have "(take n l'a) ! j < (take n l'a) ! ((aa + n) div 2)"
      using t0 sorted_wrt_nth_less[where xs="take n l'a" and ?j="((aa + n) div 2)"]
        t1 t4 t5 by auto
    then show ?thesis
      using \<open>(aa + n) div 2 < n\<close> t5 by auto
  qed
  subgoal for l' aa b l'a aaa ba j
  proof -
    assume t0: "aa < b"
    assume t1: " n \<le> length l'a"
    assume t3: "b \<le> n"
    assume t4: "sorted_less (take n l'a)"
    assume t5: "j < (aa + b) div 2"
    have "(aa+b) div 2 < n" using t3 t0 by linarith
    then have "(take n l'a) ! j < (take n l'a) ! ((aa + b) div 2)"
      using t0 sorted_wrt_nth_less[where xs="take n l'a" and ?j="((aa + b) div 2)"]
        t1 t4 t5 by auto
    then show ?thesis
      using \<open>(aa + b) div 2 < n\<close> t5 by auto
  qed
    apply (metis nth_take order_mono_setup.refl)
   apply sep_auto
  apply (sep_auto simp add: is_pfa_def)
  done

text "We can fortunately directly use this function as the split_list interpretation"


text "Then, using the same loop invariant, a binary split for B-tree-like arrays
is derived in a straightforward manner."


definition bin_split :: "('a::heap \<times> 'b::{heap,linorder}) pfarray \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "bin_split \<equiv> \<lambda>(a,n) p. do {
  (low',high') \<leftarrow> heap_WHILET 
    (\<lambda>(low,high). return (low < high)) 
    (\<lambda>(low,high). let mid = ((low  + high) div 2) in
     do {
      (_,s) \<leftarrow> Array.nth a mid;
      if p < s then
         return (low, mid)
      else if p > s then
         return (mid+1, high)
      else return (mid,mid)
     }) 
    (0::nat,n);
  return low'
}"


thm nth_take

lemma nth_take_eq: "take n ls = take n ls' \<Longrightarrow> i < n \<Longrightarrow> ls!i = ls'!i"
  by (metis nth_take)

lemma map_snd_sorted_less: "\<lbrakk>sorted_less (map snd xs); i < j; j < length xs\<rbrakk>
       \<Longrightarrow> snd (xs ! i) < snd (xs ! j)"
  by (metis (mono_tags, opaque_lifting) length_map less_trans nth_map sorted_wrt_iff_nth_less)

lemma map_snd_sorted_lesseq: "\<lbrakk>sorted_less (map snd xs); i \<le> j; j < length xs\<rbrakk>
       \<Longrightarrow> snd (xs ! i) \<le> snd (xs ! j)"
  by (metis eq_iff less_imp_le map_snd_sorted_less order.not_eq_order_implies_strict)

lemma bin_split_rule: "
sorted_less (map snd xs) \<Longrightarrow>
< is_pfa c xs (a,n)>
 bin_split (a,n) p
 <\<lambda>l. is_pfa c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. snd(xs!j) < p) \<and> (l<n \<longrightarrow> snd(xs!l)\<ge>p)) >\<^sub>t"
  (* this works in principle, as demonstrated above *)
  unfolding bin_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>(l,h). h-l)"
      and I = "\<lambda>(l,h). is_pfa c xs (a,n) * \<up>(l\<le>h \<and> h \<le> n \<and> (\<forall>j<l. snd (xs!j) < p) \<and> (h<n \<longrightarrow> snd (xs!h)\<ge>p))"
      and b = "\<lambda>(l,h). l<h"
      and Q="\<lambda>(l,h). is_pfa c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. snd (xs!j) < p) \<and> (l<n \<longrightarrow> snd (xs!l)\<ge>p))"
      ]
  thm R

  apply (sep_auto decon: R simp: less_Suc_eq is_pfa_def) []

      apply(auto dest!: sndI nth_take_eq[of n _ _ "(_ + _) div 2"])[]
     apply(auto dest!: sndI nth_take_eq[of n _ _ "(_ + _) div 2"])[]
    apply (sep_auto dest!: sndI )
  subgoal for ls i ls' _ _ j
    using map_snd_sorted_lesseq[of "take n ls'" j "(i + n) div 2"] 
      less_mult_imp_div_less apply(auto)[]
    done
  subgoal for ls i j ls' _ _ j'
    using map_snd_sorted_lesseq[of "take n ls'" j' "(i + j) div 2"] 
      less_mult_imp_div_less apply(auto)[]
    done
    apply sep_auto
  subgoal for ls i ls' _ _ j
    using map_snd_sorted_less[of "take n ls'" j "(i + n) div 2"] 
      less_mult_imp_div_less
    apply(auto)[]
    done
  subgoal for ls i j ls' _ _ j'
    using map_snd_sorted_less[of "take n ls'" j' "(i + j) div 2"] 
      less_mult_imp_div_less
    apply(auto)[]
    done
    apply (metis le_less nth_take_eq)
   apply sep_auto
  apply (sep_auto simp add: is_pfa_def)
  done


subsection "Refinement of an abstract split"


text \<open>Any function that yields the heap rule
we have obtained for bin\_split and lin\_split also
refines this abstract split.\<close>

locale split\<^sub>i_tree_smeq =
  fixes split_fun :: "('a::{heap,default,linorder,order_top} btnode ref option \<times> 'a) array \<times> nat \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes split_rule: "sorted_less (separators xs) \<Longrightarrow> 
 <is_pfa c xs (a, n)>
   split_fun (a, n) (p::'a)
  <\<lambda>r. is_pfa c xs (a, n) *
                 \<up> (r \<le> n \<and>
                   (\<forall>j<r. snd (xs ! j) < p) \<and>
                   (r < n \<longrightarrow> p \<le> snd (xs ! r)))>\<^sub>t"
begin


lemma linear_split_full: "\<forall>(_,s) \<in> set xs. s < p \<Longrightarrow> linear_split xs p = (xs,[])"
  by simp


lemma linear_split_split:
  assumes "n < length xs" 
    and "(\<forall>(_,s) \<in> set (take n xs). s < p)"
    and " (case (xs!n) of (_,s) \<Rightarrow> \<not>(s < p))"
  shows "linear_split xs p = (take n xs, drop n xs)"
  using assms  apply (auto)
   apply (metis (mono_tags, lifting) id_take_nth_drop old.prod.case takeWhile_eq_all_conv takeWhile_tail)
  by (metis (no_types, lifting) Cons_nth_drop_Suc case_prod_conv dropWhile.simps(2) dropWhile_append2 id_take_nth_drop)


(* TODO refactor proof? *)
lemma split_rule_linear_split: 
  shows
    "sorted_less (separators ts) \<Longrightarrow> 
    min (length ks) (length tsi) = length tsi \<Longrightarrow>
    tsi' = zip ks (separators tsi) \<Longrightarrow>
    <
    is_pfa c tsi (a,n)
  * list_assn (A \<times>\<^sub>a id_assn) ts tsi'> 
    split_fun (a,n) p 
  <\<lambda>i. 
    is_pfa c tsi (a,n)
    * list_assn (A \<times>\<^sub>a id_assn) ts tsi'
    * \<up>(split_relation ts (linear_split ts p) i)>\<^sub>t"
  apply(rule hoare_triple_preI)
  apply (sep_auto heap: split_rule dest!: mod_starD id_assn_list
      simp add: list_assn_prod_map split_ismeq map_snd_zip_take simp del: linear_split.simps)
    apply(auto simp add: is_pfa_def simp del: linear_split.simps)
proof -

  fix h l' assume heap_init:
    "h \<Turnstile> a \<mapsto>\<^sub>a l'"
    "map snd ts = (map snd (take n l'))"
    "n \<le> length l'"


  show full_thm: "\<forall>j<n. snd (l' ! j) < p \<Longrightarrow>
       split_relation ts (linear_split ts p) n"
  proof -
    assume sm_list: "\<forall>j<n. snd (l' ! j) < p"
    then have "\<forall>j < length (map snd (take n l')). ((map snd (take n l'))!j) < p"
      by simp
    then have "\<forall>j<length (map snd ts). ((map snd ts)!j) < p"
      using heap_init by simp
    then have "\<forall>(_,s) \<in> set ts. s < p"
      by (metis case_prod_unfold in_set_conv_nth length_map nth_map)
    then have "linear_split ts p = (ts, [])"
      using linear_split_full[of ts p] by simp
    then show "split_relation ts (linear_split ts p) n"
      using split_relation_length
      by (metis heap_init(2) heap_init(3) length_map length_take min.absorb2)

  qed
  then show "\<forall>j<n. snd (l' ! j) < p \<Longrightarrow>
       p \<le> snd (take n l' ! n) \<Longrightarrow>
       split_relation ts (linear_split ts p) n"
    by simp

  show part_thm: "\<And>x. x < n \<Longrightarrow>
       \<forall>j<x. snd (l' ! j) < p \<Longrightarrow>
       p \<le> snd (l' ! x) \<Longrightarrow> split_relation ts (linear_split ts p) x"
  proof -
    fix x assume x_sm_len: "x < n"
    moreover assume sm_list: "\<forall>j<x. snd (l' ! j) < p"
    ultimately have "\<forall>j<x. ((map snd l') ! j) < p"
      using heap_init
      by auto
    then have "\<forall>j<x. ((map snd ts)!j) < p"
      using heap_init  x_sm_len
      by auto
    moreover have x_sm_len_ts: "x < n"
      using heap_init x_sm_len by auto
    ultimately have "\<forall>(_,x) \<in> set (take x ts). x < p"
      by (auto simp add: in_set_conv_nth  min.absorb2)+
    moreover assume "p \<le> snd (l' ! x)"
    then have "case l'!x of (_,s) \<Rightarrow> \<not>(s < p)"
      by (simp add: case_prod_unfold)
    then have "case ts!x of (_,s) \<Rightarrow> \<not>(s < p)"
      using heap_init x_sm_len x_sm_len_ts
      by (metis (mono_tags, lifting) case_prod_unfold length_map length_take min.absorb2 nth_take snd_map_help(2))
    ultimately have "linear_split ts p = (take x ts, drop x ts)"
      using x_sm_len_ts linear_split_split[of x ts p] heap_init
      by (metis length_map length_take min.absorb2)
    then show "split_relation ts (linear_split ts p) x"
      using x_sm_len_ts 
      by (metis append_take_drop_id heap_init(2) heap_init(3) length_map length_take less_imp_le_nat min.absorb2 split_relation_alt)
  qed
qed


sublocale split\<^sub>i_tree linear_split split_fun
  apply(unfold_locales)
  unfolding linear_split.simps
  subgoal by (auto split: list.splits)
  subgoal
    apply (auto split: list.splits)
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  subgoal for ts tsi rs tsi'' r z c a n k p
    supply R= split_rule_linear_split[of ts "zip (subtrees tsi) (zip (butlast (r # rs)) (butlast (rs @ [z])))" tsi
tsi''
      ]
    thm R
    apply(sep_auto heap: R simp del: last.simps butlast.simps)
    done
  done

end

locale split\<^sub>i_list_smeq =
  fixes split_list_fun :: "('a::{heap,default,linorder,order_top} array \<times> nat) \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes split_list_rule: "sorted_less xs \<Longrightarrow> 
 <is_pfa c xs (a, n)>
   split_list_fun (a, n) (p::'a)
  <\<lambda>r. is_pfa c xs (a, n) *
                 \<up> (r \<le> n \<and>
                   (\<forall>j<r. xs ! j < p) \<and>
                   (r < n \<longrightarrow> p \<le> xs ! r))>\<^sub>t"
begin


lemma split_list_rule_linear_split: 
  shows
    "sorted_less ts \<Longrightarrow> <
    is_pfa c ts (a,n)> 
    split_list_fun (a,n) p 
  <\<lambda>i. 
    is_pfa c ts (a,n)
    * \<up>(split_relation ts (linear_split_list ts p) i)>\<^sub>t"
  apply(rule hoare_triple_preI)
  apply (sep_auto heap: split_list_rule dest!: mod_starD 
      simp add: list_assn_prod_map split_ismeq id_assn_list_alt simp del: linear_split_list.simps)
    apply(auto simp add: is_pfa_def split_relation_alt)
  subgoal by (smt (verit) eq_len_takeWhile_conv leD length_take length_takeWhile_le linorder_neqE_nat min_eq_arg(2) nth_length_takeWhile nth_take nth_take_eq)
  subgoal by (metis le_neq_implies_less length_take length_takeWhile_le min_eq_arg(2) nth_length_takeWhile nth_take)
  subgoal by (metis le_neq_implies_less length_take length_takeWhile_le min_eq_arg(2) nth_length_takeWhile nth_take)
  done


sublocale split\<^sub>i_list linear_split_list split_list_fun
  apply(unfold_locales)
  subgoal by (auto split: list.splits)
  subgoal
    apply (auto split: list.splits)
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal
    apply (auto split: list.splits)
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  apply(sep_auto heap: split_list_rule_linear_split)
  done

end

locale split\<^sub>i_full_smeq = split\<^sub>i_tree_smeq split_fun + split\<^sub>i_list_smeq split_list_fun
  for split_fun:: "('a::{heap,default,linorder,order_top} btnode ref option \<times> 'a) array \<times> nat \<Rightarrow> 'a \<Rightarrow> nat Heap"
  and split_list_fun :: "('a::{heap,default,linorder,order_top} array \<times> nat) \<Rightarrow> 'a \<Rightarrow> nat Heap"
begin

sublocale split\<^sub>i_full split_fun split_list_fun linear_split linear_split_list
  by (unfold_locales)

end

text "The fact that these functions fulfill the locale specifications will only be shown
when we try to extract the executable code, because
the correct definitions have to be derived directly at the first instance of interpretation."

end