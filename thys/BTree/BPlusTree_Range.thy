theory BPlusTree_Range
imports BPlusTree
    "HOL-Data_Structures.Set_Specs"
    "HOL-Library.Sublist"
    BPlusTree_Split
begin

text "Lrange describes all elements in a set that are greater or equal to l,
a lower bounded range (with no upper bound)"

definition Lrange where
  "Lrange l X = {x \<in> X. x \<ge> l}"

definition "lrange_filter l = filter (\<lambda>x. x \<ge> l)"

lemma lrange_filter_iff_Lrange: "set (lrange_filter l xs) = Lrange l (set xs)" 
  by (auto simp add: lrange_filter_def Lrange_def)

fun lrange_list where
  "lrange_list l (x#xs) = (if x \<ge> l then (x#xs) else lrange_list l xs)" |
  "lrange_list l [] = []"

lemma sorted_leq_lrange: "sorted_wrt (\<le>) xs \<Longrightarrow> lrange_list (l::'a::linorder) xs = lrange_filter l xs"
  apply(induction xs)
  apply(auto simp add: lrange_filter_def)
  by (metis dual_order.trans filter_True)

lemma sorted_less_lrange: "sorted_less xs \<Longrightarrow> lrange_list (l::'a::linorder) xs = lrange_filter l xs"
  by (simp add: sorted_leq_lrange strict_sorted_iff)

lemma lrange_list_sorted: "sorted_less (xs@x#ys) \<Longrightarrow>
  lrange_list l (xs@x#ys) =
  (if l < x then (lrange_list l xs)@x#ys else lrange_list l (x#ys))" 
  by (induction xs arbitrary: x) auto

lemma lrange_filter_sorted: "sorted_less (xs@x#ys) \<Longrightarrow>
  lrange_filter l (xs@x#ys) =
  (if l < x then (lrange_filter l xs)@x#ys else lrange_filter l (x#ys))" 
  by (metis lrange_list_sorted sorted_less_lrange sorted_wrt_append)


lemma lrange_suffix: "suffix (lrange_list l xs) xs" 
  apply(induction xs)
  apply (auto dest: suffix_ConsI)
  done


locale split_range = split_tree split
  for split::
    "('a bplustree \<times> 'a::{linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" +
  fixes lrange_list ::  "'a \<Rightarrow> ('a::{linorder,order_top}) list \<Rightarrow> 'a list"
  assumes lrange_list_req:
    (* we later derive such a function from a split function similar to the above *)
    "sorted_less ks \<Longrightarrow> lrange_list l ks = lrange_filter l ks"
begin

fun lrange:: "'a bplustree \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "lrange (Leaf ks) x = (lrange_list x ks)" |
  "lrange (Node ts t) x = (
      case split ts x of (_,(sub,sep)#rs) \<Rightarrow> (
             lrange sub x @ leaves_list rs @ leaves t
      ) 
   | (_,[]) \<Rightarrow> lrange t x
  )"

text "lrange proof"


(* lift to split *)


lemma lrange_sorted_split:
  assumes "Laligned (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, rs)"
  shows "lrange_filter x (leaves (Node ts t)) = lrange_filter x (leaves_list rs @ leaves t)"
proof (cases ls)
  case Nil
  then have "ts = rs"
    using assms by (auto dest!: split_conc)
  then show ?thesis by simp
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.simps(3) rev_exhaust surj_pair)
  then have x_sm_sep: "sep < x"
    using split_req(2)[of ts x ls' sub sep rs]
    using Laligned_sorted_separators[OF assms(1)]
    using assms sorted_cons sorted_snoc 
    by blast
  moreover have leaves_split: "leaves (Node ts t) = leaves_list ls @ leaves_list rs @ leaves t"
    using assms(3) leaves_split by blast
  then show ?thesis
  proof (cases "leaves_list ls")
    case Nil
    then show ?thesis
      using leaves_split
      by (metis self_append_conv2)
  next
    case Cons
    then obtain leavesls' l' where leaves_tail_split: "leaves_list ls = leavesls' @ [l']"
      by (metis list.simps(3) rev_exhaust)
    then have "l' \<le> sep"
    proof -
      have "l' \<in> set (leaves_list ls)"
        using leaves_tail_split by force
      then have "l' \<in> set (leaves (Node ls' sub))"
        using ls_tail_split
        by auto
      moreover have "Laligned (Node ls' sub) sep" 
        using assms split_conc[OF assms(3)] Cons ls_tail_split
        using Laligned_split_left[of ls' sub sep rs t u]
        by simp
      ultimately show ?thesis
        using Laligned_leaves_inbetween[of "Node ls' sub" sep]
        by blast
    qed
    then have "l' < x"
      using le_less_trans x_sm_sep by blast
    then show ?thesis
      using assms(2) ls_tail_split leaves_tail_split leaves_split x_sm_sep
      using lrange_filter_sorted[of "leavesls'" l' "leaves_list rs @ leaves t" x]
      by (auto simp add: lrange_filter_def) 
  qed
qed


lemma lrange_sorted_split_right:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (leaves (Node ts t))"
    and "Laligned (Node ts t) u"
  shows "lrange_filter x (leaves_list ((sub,sep)#rs) @ leaves t) = lrange_filter x (leaves sub)@leaves_list rs@leaves t"
proof -
  from assms have "x \<le> sep"
  proof -
    from assms have "sorted_less (separators ts)"
      by (meson Laligned_sorted_inorder sorted_cons sorted_inorder_separators sorted_snoc)
    then show ?thesis
      using split_req(3)
      using assms
      by fastforce
  qed
  moreover have leaves_split: "leaves (Node ts t) = leaves_list ls @ leaves sub @ leaves_list rs @ leaves t"
    using split_conc[OF assms(1)] by auto
  ultimately show ?thesis
  proof (cases "leaves_list rs @ leaves t")
    case Nil
    then show ?thesis 
      by (metis assms(1) leaves_split same_append_eq self_append_conv split_tree.leaves_split split_tree_axioms)
  next
    case (Cons r' rs')
    then have "sep < r'"
      by (metis (mono_tags, lifting) Laligned_split_right aligned_leaves_inbetween append.right_neutral append_assoc assms(1) assms(3) concat.simps(1) leaves_conc list.set_intros(1) list.simps(8) split_tree.split_conc split_tree_axioms)
    then have  "x < r'"
      using \<open>x \<le> sep\<close> by auto
    moreover have "sorted_less (leaves_list ((sub,sep)#rs) @ leaves t)"
      using assms sorted_wrt_append split_conc
      by fastforce
    ultimately show ?thesis
      using lrange_filter_sorted[of "leaves sub" "r'" "rs'" x] Cons 
      by auto
  qed
qed


theorem lrange_set: 
  assumes "sorted_less (leaves t)"
    and "aligned l t u"
  shows "lrange t x = lrange_filter x (leaves t)"
  using assms
proof(induction t x arbitrary: l u rule: lrange.induct)
  case (1 ks x)
  then show ?case
    using lrange_list_req
    by auto
next
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs" 
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have "lrange (Node ts t) x = lrange t x"
      by (simp add: list_split)
    also have "\<dots> = lrange_filter x (leaves t)"
      by (metis "2.IH"(1) "2.prems"(1) "2.prems"(2) align_last' list_split local.Nil sorted_leaves_induct_last)
    also have "\<dots> = lrange_filter x (leaves (Node ts t))"
      by (metis "2.prems"(1) "2.prems"(2) aligned_imp_Laligned leaves.simps(2) list_conc list_split local.Nil lrange_sorted_split same_append_eq self_append_conv split_tree.leaves_split split_tree_axioms)
    finally show ?thesis .
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
      then have "lrange (Node ts t) x = lrange sub x @ leaves_list list @ leaves t"
        using list_split Cons a_split
        by auto
      also have "\<dots> = lrange_filter x (leaves sub) @ leaves_list list @ leaves t"
        using "2.IH"(2)[of ls rs "(sub,sep)" list sub sep]
        using "2.prems" a_split list_conc list_split local.Cons sorted_leaves_induct_subtree
              align_sub
        by (metis in_set_conv_decomp)
      also have "\<dots> = lrange_filter x (leaves (Node ts t))"
        by (metis "2.prems"(1) "2.prems"(2) a_split aligned_imp_Laligned list_split local.Cons lrange_sorted_split lrange_sorted_split_right)
      finally show ?thesis  .
    qed
qed

text "Now the alternative explanation that first obtains the correct leaf node
and in a second step obtains the correct element from the leaf node."

fun leaf_nodes_lrange:: "'a bplustree \<Rightarrow> 'a \<Rightarrow> 'a bplustree list" where
  "leaf_nodes_lrange (Leaf ks) x = [Leaf ks]" |
  "leaf_nodes_lrange (Node ts t) x = (
      case split ts x of (_,(sub,sep)#rs) \<Rightarrow> (
             leaf_nodes_lrange sub x @ leaf_nodes_list rs @ leaf_nodes t
      ) 
   | (_,[]) \<Rightarrow> leaf_nodes_lrange t x
  )"

text "lrange proof"


(* lift to split *)

lemma concat_leaf_nodes_leaves_list: "(concat (map leaves (leaf_nodes_list ts))) = leaves_list ts"
  apply(induction ts)
  subgoal by auto
  subgoal using concat_leaf_nodes_leaves by auto
  done

theorem leaf_nodes_lrange_set: 
  assumes "sorted_less (leaves t)"
    and "aligned l t u"
  shows "suffix (lrange_filter x (leaves t)) (concat (map leaves (leaf_nodes_lrange t x)))"
  using assms
proof(induction t x arbitrary: l u rule: lrange.induct)
  case (1 ks x)
  then show ?case
    apply simp
    by (metis lrange_suffix sorted_less_lrange)
next
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs" 
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have *: "leaf_nodes_lrange (Node ts t) x = leaf_nodes_lrange t x"
      by (simp add: list_split)
    moreover have "suffix (lrange_filter x (leaves t)) (concat (map leaves (leaf_nodes_lrange t x)))"
      by (metis "2.IH"(1) "2.prems"(1) "2.prems"(2) align_last' list_split local.Nil sorted_leaves_induct_last)
    then have "suffix (lrange_filter x (leaves (Node ts t))) (concat (map leaves (leaf_nodes_lrange t x)))"
      by (metis "2.prems"(1) "2.prems"(2) aligned_imp_Laligned leaves.simps(2) list_conc list_split local.Nil lrange_sorted_split same_append_eq self_append_conv split_tree.leaves_split split_tree_axioms)
    ultimately show ?thesis by simp
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
      then have "leaf_nodes_lrange (Node ts t) x = leaf_nodes_lrange sub x @ leaf_nodes_list list @ leaf_nodes t"
        using list_split Cons a_split
        by auto
      moreover have *: "suffix (lrange_filter x (leaves sub)) (concat (map leaves (leaf_nodes_lrange sub x)))"
        by (metis "2.IH"(2) "2.prems"(1) "2.prems"(2) a_split align_sub in_set_conv_decomp list_conc list_split local.Cons sorted_leaves_induct_subtree)
      then have "suffix (lrange_filter x (leaves (Node ts t))) (concat (map leaves (leaf_nodes_lrange sub x @ leaf_nodes_list list @ leaf_nodes t)))"
      proof (goal_cases)
        case 1
        have "lrange_filter x (leaves (Node ts t)) = lrange_filter x (leaves sub @ leaves_list list @ leaves t)" 
          by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) a_split aligned_imp_Laligned append.assoc concat_map_maps fst_conv list.simps(9) list_split local.Cons lrange_sorted_split maps_simps(1))
        also have "\<dots> = lrange_filter x (leaves sub) @ leaves_list list @ leaves t"
          by (metis "2.prems"(1) "2.prems"(2) a_split aligned_imp_Laligned calculation list_split local.Cons lrange_sorted_split_right split_range.lrange_sorted_split split_range_axioms)
        moreover have "(concat (map leaves (leaf_nodes_lrange sub x @ leaf_nodes_list list @ leaf_nodes t))) = (concat (map leaves (leaf_nodes_lrange sub x)) @ leaves_list list @ leaves t)" 
          using concat_leaf_nodes_leaves_list[of list] concat_leaf_nodes_leaves[of t]
          by simp
        ultimately show ?case
          using *
          by simp
      qed
      ultimately show ?thesis by simp
    qed
qed

lemma leaf_nodes_lrange_not_empty: "\<exists>ks list. leaf_nodes_lrange t x = (Leaf ks)#list \<and> (Leaf ks) \<in> set (leaf_nodes t)" 
  apply(induction t x rule: leaf_nodes_lrange.induct)
  apply (auto split!: prod.splits list.splits)
  by (metis Cons_eq_appendI fst_conv in_set_conv_decomp split_conc)


text "Note that, conveniently, this argument is purely syntactic,
we do not need to show that this has anything to do with linear orders"

lemma leaf_nodes_lrange_pre_lrange: "leaf_nodes_lrange t x = (Leaf ks)#list \<Longrightarrow> lrange_list x ks @ (concat (map leaves list)) = lrange t x"
proof(induction t x arbitrary: ks list rule: leaf_nodes_lrange.induct)
  case (1 ks x)
  then show ?case by simp
next
  case (2 ts t x ks list)
  then show ?case
  proof(cases "split ts x")
    case split: (Pair ls rs)
    then show ?thesis
    proof (cases rs)
      case Nil
      then show ?thesis
        using "2.IH"(1) "2.prems" split by auto
    next
      case (Cons subsep rss)
      then show ?thesis
      proof(cases subsep)
        case sub_sep: (Pair sub sep)
        thm "2.IH"(2) "2.prems"
        have "\<exists>list'. leaf_nodes_lrange sub x = (Leaf ks)#list'"
          using "2.prems" split Cons sub_sep leaf_nodes_lrange_not_empty[of sub x]
            apply simp
          by fastforce
        then obtain list' where *: "leaf_nodes_lrange sub x = (Leaf ks)#list'"
          by blast
        moreover have "list = list'@concat (map (leaf_nodes \<circ> fst) rss) @ leaf_nodes t"
          using * 
          using "2.prems" split Cons sub_sep
          by simp
        ultimately show ?thesis
          using split "2.IH"(2)[OF split[symmetric] Cons sub_sep[symmetric] *,symmetric]
                Cons sub_sep concat_leaf_nodes_leaves_list[of rss] concat_leaf_nodes_leaves[of t]
          by simp
      qed
    qed
  qed
qed

text "We finally obtain a function that is way easier to reason about in the imperative setting"
fun concat_leaf_nodes_lrange where
  "concat_leaf_nodes_lrange t x = (case leaf_nodes_lrange t x of (Leaf ks)#list \<Rightarrow> lrange_list x ks @ (concat (map leaves list)))"

lemma concat_leaf_nodes_lrange_lrange: "concat_leaf_nodes_lrange t x = lrange t x"
proof -
  obtain ks list where *: "leaf_nodes_lrange t x = (Leaf ks)#list"
    using leaf_nodes_lrange_not_empty by blast
  then have "concat_leaf_nodes_lrange t x = lrange_list x ks @ (concat (map leaves list))"
    by simp
  also have "\<dots> = lrange t x"
    using leaf_nodes_lrange_pre_lrange[OF *]
    by simp
  finally show ?thesis .
qed

end

context split_list
begin

definition lrange_split where
"lrange_split l xs = (case split_list xs l of (ls,rs) \<Rightarrow> rs)"

lemma lrange_filter_split: 
  assumes "sorted_less xs"
    and "split_list xs l = (ls,rs)"
  shows "lrange_list l xs = rs"
  find_theorems split_list
proof(cases rs)
  case rs_Nil: Nil
  then show ?thesis
  proof(cases ls)
    case Nil
    then show ?thesis
      using assms split_list_req(1)[of xs l ls rs] rs_Nil
      by simp
  next
    case Cons
    then obtain lss sep where snoc: "ls = lss@[sep]"
      by (metis append_butlast_last_id list.simps(3))
    then have "sep < l"
      using assms(1) assms(2) split_list_req(2) by blast
    then show ?thesis 
      using lrange_list_sorted[of lss sep rs l]
            snoc split_list_req(1)[OF assms(2)]
            assms rs_Nil
      by simp
  qed
next
  case ls_Cons: (Cons sep rss)
  then have *: "l \<le> sep"
    using assms(1) assms(2) split_list_req(3) by auto
  then show ?thesis 
  proof(cases ls)
    case Nil
    then show ?thesis
    using lrange_list_sorted[of ls sep rss l]
          split_list_req(1)[OF assms(2)] assms
          ls_Cons *
    by simp
  next
    case Cons
    then obtain lss sep2 where snoc: "ls = lss@[sep2]"
      by (metis append_butlast_last_id list.simps(3))
    then have "sep2 < l"
      using assms(1) assms(2) split_list_req(2) by blast
    moreover have "sorted_less (lss@[sep2])"
      using assms(1) assms(2) ls_Cons snoc sorted_mid_iff sorted_snoc split_list_req(1) by blast
    ultimately show ?thesis 
      using lrange_list_sorted[of ls sep rss l]
            lrange_list_sorted[of lss "sep2" "[]" l]
            split_list_req(1)[OF assms(2)] assms
            ls_Cons * snoc
      by simp
  qed
qed

lemma lrange_split_req: 
  assumes "sorted_less xs"
  shows "lrange_split l xs = lrange_filter l xs"
  unfolding lrange_split_def
  using lrange_filter_split[of xs l] assms
  using sorted_less_lrange
  by (simp split!: prod.splits)

end

context split_full
begin

sublocale split_range split lrange_split 
  using lrange_split_req
  by unfold_locales auto

end

end