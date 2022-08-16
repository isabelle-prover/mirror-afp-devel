theory BPlusTree_Set
  imports
    BPlusTree_Split
    "HOL-Data_Structures.Set_Specs"
begin


section "Set interpretation"

(* obsolete fact *)
lemma insert_list_length[simp]:
  assumes "sorted_less ks"
    and "set (insert_list k ks) = set ks \<union> {k}"
    and "sorted_less ks \<Longrightarrow> sorted_less (insert_list k ks)"
  shows "length (insert_list k ks) = length ks + (if k \<in> set ks then 0 else 1)"
proof -
  have "distinct (insert_list k ks)"
    using assms(1) assms(3) strict_sorted_iff by blast
  then have "length (insert_list k ks) = card (set (insert_list k ks))"
    by (simp add: distinct_card)
  also have "\<dots> = card (set ks \<union> {k})"
    using assms(2) by presburger
  also have "\<dots> = card (set ks) + (if k \<in> set ks then 0 else 1)"
    by (cases "k \<in> set ks") (auto simp add: insert_absorb)
  also have "\<dots> = length ks + (if k \<in> set ks then 0 else 1)"
    using assms(1) distinct_card strict_sorted_iff by auto
  finally show ?thesis.
qed

lemma delete_list_length[simp]:
  assumes "sorted_less ks"
    and "set (delete_list k ks) = set ks - {k}"
    and "sorted_less ks \<Longrightarrow> sorted_less (delete_list k ks)"
  shows "length (delete_list k ks) = length ks - (if k \<in> set ks then 1 else 0)"
proof -
  have "distinct (delete_list k ks)"
    using assms(1) assms(3) strict_sorted_iff by blast
  then have "length (delete_list k ks) = card (set (delete_list k ks))"
    by (simp add: distinct_card)
  also have "\<dots> = card (set ks - {k})"
    using assms(2) by presburger
  also have "\<dots> = card (set ks) - (if k \<in> set ks then 1 else 0)"
    by (cases "k \<in> set ks") (auto)
  also have "\<dots> = length ks - (if k \<in> set ks then 1 else 0)"
    by (metis assms(1) distinct_card strict_sorted_iff)
  finally show ?thesis.
qed

lemma ins_list_length[simp]:
  assumes "sorted_less ks"
  shows "length (ins_list k ks) = length ks + (if k \<in> set ks then 0 else 1)"
  using insert_list_length[of ks ins_list k]
  by (simp add: assms set_ins_list sorted_ins_list)

lemma del_list_length[simp]:
  assumes "sorted_less ks"
  shows "length (del_list k ks) = length ks - (if k \<in> set ks then 1 else 0)"
  using delete_list_length[of ks ins_list k]
  by (simp add: assms set_del_list sorted_del_list)


(* TODO what if we define a function "list_split" that returns
 a split list for mapping arbitrary f (separators) and g (subtrees)
s.th. f :: 'a \<Rightarrow> ('b::linorder) and g :: 'a \<Rightarrow> 'a bplustree
this would allow for key,pointer pairs to be inserted into the tree *)
(* TODO what if the keys are the pointers? *)
locale split_set = split_tree: split_tree split
  for split::
    "('a bplustree \<times> 'a::{linorder,order_top}) list \<Rightarrow> 'a
       \<Rightarrow> ('a bplustree \<times> 'a) list \<times> ('a bplustree \<times> 'a) list" +
  fixes isin_list ::  "'a \<Rightarrow> ('a::{linorder,order_top}) list \<Rightarrow> bool"
  and insert_list ::  "'a \<Rightarrow> ('a::{linorder,order_top}) list \<Rightarrow> 'a list"
  and delete_list ::  "'a \<Rightarrow> ('a::{linorder,order_top}) list \<Rightarrow> 'a list"
  assumes insert_list_req:
    (* TODO locale that derives such a function from a split function similar to the above *)
    "sorted_less ks \<Longrightarrow> isin_list x ks = (x \<in> set ks)"
    "sorted_less ks \<Longrightarrow> insert_list x ks = ins_list x ks"
    "sorted_less ks \<Longrightarrow> delete_list x ks = del_list x ks"
begin

lemmas split_req = split_tree.split_req
lemmas split_conc = split_tree.split_req(1)
lemmas split_sorted = split_tree.split_req(2,3)

lemma insert_list_length[simp]:
  assumes "sorted_less ks"
  shows "length (insert_list k ks) = length ks + (if k \<in> set ks then 0 else 1)"
  using insert_list_req
  by (simp add: assms)

lemma set_insert_list[simp]:
  "sorted_less ks \<Longrightarrow> set (insert_list k ks) = set ks \<union> {k}"
  by (simp add: insert_list_req set_ins_list)

lemma sorted_insert_list[simp]:
  "sorted_less ks \<Longrightarrow> sorted_less (insert_list k ks)"
  by (simp add: insert_list_req sorted_ins_list)

lemma delete_list_length[simp]:
  assumes "sorted_less ks"
  shows "length (delete_list k ks) = length ks - (if k \<in> set ks then 1 else 0)"
  using insert_list_req
  by (simp add: assms)

lemma set_delete_list[simp]:
  "sorted_less ks \<Longrightarrow> set (delete_list k ks) = set ks - {k}"
  by (simp add: insert_list_req set_del_list)

lemma sorted_delete_list[simp]:
  "sorted_less ks \<Longrightarrow> sorted_less (delete_list k ks)"
  by (simp add: insert_list_req sorted_del_list)



definition "empty_bplustree = (Leaf [])"

subsection "Membership"

fun isin:: "'a bplustree \<Rightarrow> 'a \<Rightarrow> bool" where
  "isin (Leaf ks) x = (isin_list x ks)" |
  "isin (Node ts t) x = (
      case split ts x of (_,(sub,sep)#rs) \<Rightarrow> (
             isin sub x
      )
   | (_,[]) \<Rightarrow> isin t x
  )"


text "Isin proof"

thm isin_simps
  (* copied from comment in List_Ins_Del *)
lemma sorted_ConsD: "sorted_less (y # xs) \<Longrightarrow> x \<le> y \<Longrightarrow> x \<notin> set xs"
  by (auto simp: sorted_Cons_iff)

lemma sorted_snocD: "sorted_less (xs @ [y]) \<Longrightarrow> y \<le> x \<Longrightarrow> x \<notin> set xs"
  by (auto simp: sorted_snoc_iff)


lemmas isin_simps2 = sorted_lems sorted_ConsD sorted_snocD
  (*-----------------------------*)

lemma isin_sorted: "sorted_less (xs@a#ys) \<Longrightarrow>
  (x \<in> set (xs@a#ys)) = (if x < a then x \<in> set xs else x \<in> set (a#ys))"
  by (auto simp: isin_simps2)

(* lift to split *)


lemma isin_sorted_split:
  assumes "Laligned (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, rs)"
  shows "x \<in> set (leaves (Node ts t)) = (x \<in> set (leaves_list rs @ leaves t))"
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
    using assms(3) split_tree.leaves_split by blast
  then show ?thesis
  proof (cases "leaves_list ls")
    case Nil
    then show ?thesis
      using leaves_split by auto
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
    then show ?thesis
      using assms(2) ls_tail_split leaves_tail_split leaves_split x_sm_sep
      using isin_sorted[of "leavesls'" l' "leaves_list rs @ leaves t" x]
      by auto
  qed
qed

lemma isin_sorted_split_right:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (leaves (Node ts t))"
    and "Laligned (Node ts t) u"
  shows "x \<in> set (leaves_list ((sub,sep)#rs) @ leaves t) = (x \<in> set (leaves sub))"
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
      using leaves_split by auto
  next
    case (Cons r' rs')
    then have "sep < r'"
      by (metis Laligned_split_right aligned_leaves_inbetween assms(1) assms(3) leaves.simps(2) list.set_intros(1) split_set.split_conc split_set_axioms)
    then have  "x < r'"
      using \<open>x \<le> sep\<close> by auto
    moreover have "sorted_less (leaves_list ((sub,sep)#rs) @ leaves t)"
      using assms sorted_wrt_append split_conc
      by fastforce
    ultimately show ?thesis
      using isin_sorted[of "leaves sub" "r'" "rs'" x] Cons 
      by auto
  qed
qed


theorem isin_set_inorder: 
  assumes "sorted_less (leaves t)"
    and "aligned l t u"
  shows "isin t x = (x \<in> set (leaves t))"
  using assms
proof(induction t x arbitrary: l u rule: isin.induct)
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs" 
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have "isin (Node ts t) x = isin t x"
      by (simp add: list_split)
    also have "\<dots> = (x \<in> set (leaves t))"
      using "2.IH"(1)[of ls rs] list_split Nil
      using "2.prems" sorted_leaves_induct_last align_last'
      by metis
    also have "\<dots> = (x \<in> set (leaves (Node ts t)))"
      using isin_sorted_split
      using "2.prems" list_split list_conc Nil
      by (metis aligned_imp_Laligned leaves.simps(2) leaves_conc same_append_eq self_append_conv)
    finally show ?thesis .
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
      then have "isin (Node ts t) x = isin sub x"
        using list_split Cons a_split
        by auto
      also have "\<dots> = (x \<in> set (leaves sub))"
        using "2.IH"(2)[of ls rs "(sub,sep)" list sub sep]
        using "2.prems" a_split list_conc list_split local.Cons sorted_leaves_induct_subtree
              align_sub
        by (metis in_set_conv_decomp)
      also have "\<dots> = (x \<in> set (leaves (Node ts t)))"
        using isin_sorted_split
        using isin_sorted_split_right "2.prems" list_split Cons a_split
        using aligned_imp_Laligned by blast
      finally show ?thesis  .
    qed
qed (auto simp add: insert_list_req)


theorem isin_set_Linorder: 
  assumes "sorted_less (leaves t)"
    and "Laligned t u"
  shows "isin t x = (x \<in> set (leaves t))"
  using assms
proof(induction t x arbitrary: u rule: isin.induct)
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs" 
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have "isin (Node ts t) x = isin t x"
      by (simp add: list_split)
    also have "\<dots> = (x \<in> set (leaves t))"
      by (metis "2.IH"(1) "2.prems"(1) "2.prems"(2) Lalign_Llast list_split local.Nil sorted_leaves_induct_last)
    also have "\<dots> = (x \<in> set (leaves (Node ts t)))"
      using isin_sorted_split
      using "2.prems" list_split list_conc Nil
      by simp
    finally show ?thesis .
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
      then have "isin (Node ts t) x = isin sub x"
        using list_split Cons a_split
        by auto
      also have "\<dots> = (x \<in> set (leaves sub))"
        using "2.IH"(2)[of ls rs "(sub,sep)" list sub sep]
        using "2.prems" a_split list_conc list_split local.Cons sorted_leaves_induct_subtree
              align_sub
        by (metis Lalign_Llast Laligned_split_left)
      also have "\<dots> = (x \<in> set (leaves (Node ts t)))"
        using isin_sorted_split
        using isin_sorted_split_right "2.prems" list_split Cons a_split
        by simp
      finally show ?thesis  .
    qed
qed (auto simp add: insert_list_req)

corollary isin_set_Linorder_top: 
  assumes "sorted_less (leaves t)"
    and "Laligned t top"
  shows "isin t x = (x \<in> set (leaves t))"
  using assms isin_set_Linorder
  by simp

subsection "Insertion"

text "The insert function requires an auxiliary data structure
and auxiliary invariant functions."

datatype 'b up\<^sub>i = T\<^sub>i "'b bplustree" | Up\<^sub>i "'b bplustree" 'b "'b bplustree"

fun order_up\<^sub>i where
  "order_up\<^sub>i k (T\<^sub>i sub) = order k sub" |
  "order_up\<^sub>i k (Up\<^sub>i l a r) = (order k l \<and> order k r)"

fun root_order_up\<^sub>i where
  "root_order_up\<^sub>i k (T\<^sub>i sub) = root_order k sub" |
  "root_order_up\<^sub>i k (Up\<^sub>i l a r) = (order k l \<and> order k r)"


fun height_up\<^sub>i where
  "height_up\<^sub>i (T\<^sub>i t) = height t" |
  "height_up\<^sub>i (Up\<^sub>i l a r) = max (height l) (height r)"

fun bal_up\<^sub>i where
  "bal_up\<^sub>i (T\<^sub>i t) = bal t" |
  "bal_up\<^sub>i (Up\<^sub>i l a r) = (height l = height r \<and> bal l \<and> bal r)"

fun inorder_up\<^sub>i where
  "inorder_up\<^sub>i (T\<^sub>i t) = inorder t" |
  "inorder_up\<^sub>i (Up\<^sub>i l a r) = inorder l @ [a] @ inorder r"

fun leaves_up\<^sub>i where
  "leaves_up\<^sub>i (T\<^sub>i t) = leaves t" |
  "leaves_up\<^sub>i (Up\<^sub>i l a r) = leaves l @ leaves r"

fun aligned_up\<^sub>i where
  "aligned_up\<^sub>i l (T\<^sub>i t) u = aligned l t u" |
  "aligned_up\<^sub>i l (Up\<^sub>i lt a rt) u = (aligned l lt a \<and> aligned a rt u)"

fun Laligned_up\<^sub>i where
  "Laligned_up\<^sub>i (T\<^sub>i t) u = Laligned t u" |
  "Laligned_up\<^sub>i (Up\<^sub>i lt a rt) u = (Laligned lt a \<and> aligned a rt u)"

text "The following function merges two nodes and returns separately split nodes
   if an overflow occurs"

(* note here that splitting away the last element is actually very nice
   from the implementation perspective *)
fun node\<^sub>i:: "nat \<Rightarrow> ('a bplustree \<times> 'a) list \<Rightarrow> 'a bplustree \<Rightarrow> 'a up\<^sub>i" where
  "node\<^sub>i k ts t = (
  if length ts \<le> 2*k then T\<^sub>i (Node ts t)
  else (
    case split_half ts of (ls, rs) \<Rightarrow>
      case last ls of (sub,sep) \<Rightarrow>
        Up\<^sub>i (Node (butlast ls) sub) sep (Node rs t)
    )
  )"

fun Lnode\<^sub>i:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a up\<^sub>i" where
  "Lnode\<^sub>i k ts = (
  if length ts \<le> 2*k then T\<^sub>i (Leaf ts)
  else (
    case split_half ts of (ls, rs) \<Rightarrow>
      Up\<^sub>i (Leaf ls) (last ls) (Leaf rs)
    )
  )"

fun ins:: "nat \<Rightarrow> 'a \<Rightarrow> 'a bplustree \<Rightarrow> 'a up\<^sub>i" where
  "ins k x (Leaf ks) = Lnode\<^sub>i k (insert_list x ks)" |
  "ins k x (Node ts t) = (
  case split ts x of
    (ls,(sub,sep)#rs) \<Rightarrow> 
        (case ins k x sub of 
          Up\<^sub>i l a r \<Rightarrow>
             node\<^sub>i k (ls@(l,a)#(r,sep)#rs) t | 
          T\<^sub>i a \<Rightarrow>
            T\<^sub>i (Node (ls@(a,sep)#rs) t)) |
    (ls, []) \<Rightarrow>
      (case ins k x t of
         Up\<^sub>i l a r \<Rightarrow>
           node\<^sub>i k (ls@[(l,a)]) r |
         T\<^sub>i a \<Rightarrow>
           T\<^sub>i (Node ls a)
  )
)"



fun tree\<^sub>i::"'a up\<^sub>i \<Rightarrow> 'a bplustree" where
  "tree\<^sub>i (T\<^sub>i sub) = sub" |
  "tree\<^sub>i (Up\<^sub>i l a r) = (Node [(l,a)] r)"

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a bplustree \<Rightarrow> 'a bplustree" where
  "insert k x t = tree\<^sub>i (ins k x t)"


subsection "Proofs of functional correctness"

lemma nodei_ti_simp: "node\<^sub>i k ts t = T\<^sub>i x \<Longrightarrow> x = Node ts t"
  apply (cases "length ts \<le> 2*k")
  apply (auto split!: list.splits prod.splits)
  done

lemma Lnodei_ti_simp: "Lnode\<^sub>i k ts = T\<^sub>i x \<Longrightarrow> x = Leaf ts"
  apply (cases "length ts \<le> 2*k")
  apply (auto split!: list.splits)
  done


lemma split_set: 
  assumes "split ts z = (ls,(a,b)#rs)"
  shows "(a,b) \<in> set ts"
    and "(x,y) \<in> set ls \<Longrightarrow> (x,y) \<in> set ts"
    and "(x,y) \<in> set rs \<Longrightarrow> (x,y) \<in> set ts"
    and "set ls \<union> set rs \<union> {(a,b)} = set ts"
    and "\<exists>x \<in> set ts. b \<in> Basic_BNFs.snds x"
  using split_conc assms by fastforce+

lemma split_length:
  "split ts x = (ls, rs) \<Longrightarrow> length ls + length rs = length ts"
  by (auto dest: split_conc)



(* TODO way to use this for custom case distinction? *)
lemma node\<^sub>i_cases: "length xs \<le> k \<or> (\<exists>ls sub sep rs. split_half xs = (ls@[(sub,sep)],rs))"
proof -
  have "\<not> length xs \<le> k \<Longrightarrow> length xs \<ge> 1"
    by linarith
  then show ?thesis
    using split_half_not_empty
    by fastforce
qed

lemma Lnode\<^sub>i_cases: "length xs \<le> k \<or> (\<exists>ls sep rs. split_half xs = (ls@[sep],rs))"
proof -
  have "\<not> length xs \<le> k \<Longrightarrow> length xs \<ge> 1"
    by linarith
  then show ?thesis
    using split_half_not_empty
    by fastforce
qed

lemma root_order_tree\<^sub>i: "root_order_up\<^sub>i (Suc k) t = root_order (Suc k) (tree\<^sub>i t)"
  apply (cases t)
   apply auto
  done

lemma length_take_left: "length (take ((length ts + 1) div 2) ts) = (length ts + 1) div 2"
  apply (cases ts)
  apply auto
  done

lemma node\<^sub>i_root_order:
  assumes "length ts > 0"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set (subtrees ts). order k x"
    and "order k t"
  shows "root_order_up\<^sub>i k (node\<^sub>i k ts t)"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis
    using assms
    by (simp add: node\<^sub>i.simps)
next
  case False
  then obtain ls sub sep rs where split_half_ts: 
    "take ((length ts + 1) div 2) ts = ls@[(sub,sep)]"
    using split_half_not_empty[of ts]
    by auto
  then have length_ls: "length ls = (length ts + 1) div 2 - 1"
    by (metis One_nat_def add_diff_cancel_right' add_self_div_2 bits_1_div_2 length_append length_take_left list.size(3) list.size(4) odd_one odd_succ_div_two)
  also have "\<dots> \<le> (4*k + 1) div 2"
    using assms(2) by simp
  also have "\<dots> = 2*k"
    by auto
  finally have "length ls \<le> 2*k"
    by simp
  moreover have "length ls \<ge> k" 
    using False length_ls by simp
  moreover have "set (ls@[(sub,sep)]) \<subseteq> set ts"
    by (metis split_half_ts(1) set_take_subset)
  ultimately have o_r: "order k (Node ls sub)"
    using split_half_ts assms by auto
  have
    "butlast (take ((length ts + 1) div 2) ts) = ls"
    "last (take ((length ts + 1) div 2) ts) = (sub,sep)" 
    using split_half_ts by auto
  then show ?thesis
    using o_r assms set_drop_subset[of _ ts]
    by (auto simp add: False split_half_ts split!: prod.splits)
qed

lemma node\<^sub>i_order_helper:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set (subtrees ts). order k x"
    and "order k t"
  shows "case (node\<^sub>i k ts t) of T\<^sub>i t \<Rightarrow> order k t | _ \<Rightarrow> True"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis
    using assms
    by (simp add: node\<^sub>i.simps)
next
  case False
  then obtain sub sep ls where 
    "take ((length ts + 1) div 2) ts = ls@[(sub,sep)]" 
    using split_half_not_empty[of ts]
    by fastforce
  then show ?thesis
    using assms by simp
qed


lemma node\<^sub>i_order:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set (subtrees ts). order k x"
    and "order k t"
  shows "order_up\<^sub>i k (node\<^sub>i k ts t)"
  apply(cases "node\<^sub>i k ts t")
  using node\<^sub>i_root_order node\<^sub>i_order_helper assms apply fastforce
  by (metis (full_types) assms le_0_eq nat_le_linear node\<^sub>i.elims node\<^sub>i_root_order order_up\<^sub>i.simps(2) root_order_up\<^sub>i.simps(2) up\<^sub>i.simps(4) verit_comp_simplify1(3))


lemma Lnode\<^sub>i_root_order:
  assumes "length ts > 0"
    and "length ts \<le> 4*k"
  shows "root_order_up\<^sub>i k (Lnode\<^sub>i k ts)"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis
    using assms
    by simp
next
  case False
  then obtain ls sep rs where split_half_ts: 
    "take ((length ts + 1) div 2) ts = ls@[sep]"
    "drop ((length ts + 1) div 2) ts = rs" 
    using split_half_not_empty[of ts]
    by auto
  then have length_ls: "length ls = ((length ts + 1) div 2) - 1"
    by (metis One_nat_def add_diff_cancel_right' add_self_div_2 bits_1_div_2 length_append length_take_left list.size(3) list.size(4) odd_one odd_succ_div_two)
  also have "\<dots> < (4*k + 1) div 2"
    using assms(2)
    by (smt (z3) Groups.add_ac(2) One_nat_def split_half_ts add.right_neutral diff_is_0_eq' div_le_mono le_add_diff_inverse le_neq_implies_less length_append length_take_left less_add_Suc1 less_imp_diff_less list.size(4) nat_le_linear not_less_eq plus_nat.simps(2))
  also have "\<dots> = 2*k"
    by auto
  finally have "length ls < 2*k"
    by simp
  moreover have "length ls \<ge> k" 
    using False length_ls by simp
  ultimately have o_l: "order k (Leaf (ls@[sep]))"
    using set_take_subset assms split_half_ts
    by fastforce
  then show ?thesis
    using assms split_half_ts False
    by auto
qed

lemma Lnode\<^sub>i_order_helper:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
  shows "case (Lnode\<^sub>i k ts) of T\<^sub>i t \<Rightarrow> order k t | _ \<Rightarrow> True"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis
    using assms
    by (simp add: node\<^sub>i.simps)
next
  case False
  then obtain sep ls where 
    "take ((length ts + 1) div 2) ts = ls@[sep]" 
    using split_half_not_empty[of ts]
    by fastforce
  then show ?thesis
    using assms by simp
qed


lemma Lnode\<^sub>i_order:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k"
  shows "order_up\<^sub>i k (Lnode\<^sub>i k ts)"
  apply(cases "Lnode\<^sub>i k ts")
  apply (metis Lnode\<^sub>i_order_helper One_nat_def add.right_neutral add_Suc_right assms(1) assms(2) le_imp_less_Suc less_le order_up\<^sub>i.simps(1) up\<^sub>i.simps(5))
  by (metis Lnode\<^sub>i.elims Lnode\<^sub>i_root_order assms(1) assms(2) diff_is_0_eq' le_0_eq le_add_diff_inverse mult_2 order_up\<^sub>i.simps(2) root_order_up\<^sub>i.simps(2) up\<^sub>i.simps(3) verit_comp_simplify1(3))

(* explicit proof *)
lemma ins_order: 
  "k > 0 \<Longrightarrow> sorted_less (leaves t) \<Longrightarrow> order k t \<Longrightarrow> order_up\<^sub>i k (ins k x t)"
proof(induction k x t rule: ins.induct)
  case (1 k x ts)
  then show ?case
    by auto (* this proof requires both sorted_less and k > 0 *)
next
  case (2 k x ts t)
  then obtain ls rs where split_res: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ts = ls@rs"
    using split_conc
    by simp

  show ?case
  proof (cases rs)
    case Nil
    then have "order_up\<^sub>i k (ins k x t)"
      using 2 split_res sorted_leaves_induct_last
      by auto
    then show ?thesis
      using Nil 2 split_app split_res Nil node\<^sub>i_order
      by (auto split!: up\<^sub>i.splits simp del: node\<^sub>i.simps)
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)"
      by (cases a)
    then have "sorted_less (leaves sub)"
      using "2"(4) Cons sorted_leaves_induct_subtree split_app
      by blast
    then have "order_up\<^sub>i k (ins k x sub)"
      using "2.IH"(2) "2.prems" a_prod local.Cons split_app split_res
      by auto
    then show ?thesis
      using 2 split_app Cons length_append node\<^sub>i_order[of k "ls@_#_#list"] a_prod split_res
      by (auto split!: up\<^sub>i.splits simp del: node\<^sub>i.simps simp add: order_impl_root_order)
  qed
qed


(* notice this is almost a duplicate of ins_order *)
lemma ins_root_order: 
  assumes "k > 0" "sorted_less (leaves t)" "root_order k t"
  shows "root_order_up\<^sub>i k (ins k x t)"
proof(cases t)
  case (Leaf ks)
  then show ?thesis
    using assms by (auto simp add: Lnode\<^sub>i_order min_absorb2) (* this proof requires both sorted_less and k > 0 *)
next
  case (Node ts t)
  then obtain ls rs where split_res: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ls@rs = ts"
    using split_conc
    by fastforce

  show ?thesis
  proof (cases rs)
    case Nil
    then have "order_up\<^sub>i k (ins k x t)"
      using Node assms split_res sorted_leaves_induct_last
      using ins_order[of k t]
      by auto
    then show ?thesis
      using Nil Node split_app split_res assms node\<^sub>i_root_order
      by (auto split!: up\<^sub>i.splits simp del: node\<^sub>i.simps simp add: order_impl_root_order)
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a = (sub, sep)"
      by (cases a)
    then have "sorted_less (leaves sub)"
      using Node assms(2) local.Cons sorted_leaves_induct_subtree split_app
      by blast
    then have "order_up\<^sub>i k (ins k x sub)"
      using Node a_prod assms ins_order local.Cons split_app
      by auto
    then show ?thesis
      using assms split_app Cons length_append Node node\<^sub>i_root_order a_prod split_res
      by (auto split!: up\<^sub>i.splits simp del: node\<^sub>i.simps simp add: order_impl_root_order)
  qed
qed



lemma height_list_split: "height_up\<^sub>i (Up\<^sub>i (Node ls a) b (Node rs t)) = height (Node (ls@(a,b)#rs) t) "
  by (induction ls) (auto simp add: max.commute)

lemma node\<^sub>i_height: "height_up\<^sub>i (node\<^sub>i k ts t) = height (Node ts t)"
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls@[(sub,sep)], rs)"
    by (meson node\<^sub>i_cases)
  then have "node\<^sub>i k ts t = Up\<^sub>i (Node ls (sub)) sep (Node rs t)"
    using False by simp
  then have "height_up\<^sub>i (node\<^sub>i k ts t) = height (Node (ls@(sub,sep)#rs) t)"
    by (metis height_list_split)
  also have "\<dots> = height (Node ts t)" 
    by (metis (no_types, lifting) Pair_inject append_Cons append_eq_append_conv2 append_take_drop_id self_append_conv split_half.simps split_half_ts)
  finally show ?thesis.
qed simp


lemma Lnode\<^sub>i_height: "height_up\<^sub>i (Lnode\<^sub>i k xs) = height (Leaf xs)"
  by (auto)

lemma bal_up\<^sub>i_tree: "bal_up\<^sub>i t = bal (tree\<^sub>i t)"
  apply(cases t)
   apply auto
  done

lemma bal_list_split: "bal (Node (ls@(a,b)#rs) t) \<Longrightarrow> bal_up\<^sub>i (Up\<^sub>i (Node ls a) b (Node rs t))"
  by (auto simp add: image_constant_conv)

lemma node\<^sub>i_bal:
  assumes "bal (Node ts t)"
  shows "bal_up\<^sub>i (node\<^sub>i k ts t)"
  using assms
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls@[(sub,sep)], rs)"
    by (meson node\<^sub>i_cases)
  then have "bal (Node (ls@(sub,sep)#rs) t)"
    using assms append_take_drop_id[where n="(length ts + 1) div 2" and xs=ts]
    by auto
  then show ?thesis
    using split_half_ts assms False
    by (auto simp del: bal.simps bal_up\<^sub>i.simps dest!: bal_list_split[of ls sub sep rs t])
qed simp

lemma node\<^sub>i_aligned: 
  assumes "aligned l (Node ts t) u"
  shows "aligned_up\<^sub>i l (node\<^sub>i k ts t) u"
  using assms
proof (cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls@[(sub,sep)], rs)"
    by (meson node\<^sub>i_cases)
  then have "aligned l (Node ls sub) sep"
    by (metis aligned_split_left append.assoc append_Cons append_take_drop_id assms prod.sel(1) split_half.simps)
  moreover have "aligned sep (Node rs t) u"
    by (smt (z3) Pair_inject aligned_split_right append.assoc append_Cons append_Nil2 append_take_drop_id assms same_append_eq split_half.simps split_half_ts)
  ultimately show ?thesis 
    using split_half_ts False by auto
qed simp

lemma node\<^sub>i_Laligned: 
  assumes "Laligned (Node ts t) u"
  shows "Laligned_up\<^sub>i (node\<^sub>i k ts t) u"
  using assms
proof (cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls@[(sub,sep)], rs)"
    by (meson node\<^sub>i_cases)
  then have "Laligned (Node ls sub) sep"
    by (metis Laligned_split_left append.assoc append_Cons assms split_half_conc)
  moreover have "aligned sep (Node rs t) u"
    by (metis Laligned_split_right append.assoc append_Cons append_Nil2 assms same_append_eq split_half_conc split_half_ts)
  ultimately show ?thesis 
    using split_half_ts False by auto
qed simp


lemma length_right_side: "length xs > 1 \<Longrightarrow> length (drop ((length xs + 1) div 2) xs) > 0"
  by auto

lemma Lnode\<^sub>i_aligned: 
  assumes "aligned l (Leaf ks) u"
    and "sorted_less ks"
    and "k > 0"
  shows "aligned_up\<^sub>i l (Lnode\<^sub>i k ks) u"
  using assms
proof (cases "length ks \<le> 2*k")
  case False
  then obtain ls sep rs where split_half_ts: 
    "take ((length ks + 1) div 2) ks = ls@[sep]"
    "drop ((length ks + 1) div 2) ks = rs" 
    using split_half_not_empty[of ks]
    by auto                        
  moreover have "sorted_less (ls@[sep])" 
    by (metis append_take_drop_id assms(2) sorted_wrt_append split_half_ts(1))
  ultimately have "aligned l (Leaf (ls@[sep])) sep"
    using split_half_conc[of ks "ls@[sep]" rs] assms sorted_snoc_iff[of ls sep]
    by auto
  moreover have "aligned sep (Leaf rs) u"
  proof -
    have "length rs > 0"
      using False assms(3) split_half_ts(2) by fastforce
    then obtain sep' rs' where "rs = sep' # rs'"
      by (cases rs) auto
    moreover have "sep < sep'"
      by (metis append_take_drop_id assms(2) calculation in_set_conv_decomp sorted_mid_iff sorted_snoc_iff split_half_ts(1) split_half_ts(2))
    moreover have "sorted_less rs"
      by (metis append_take_drop_id assms(2) sorted_wrt_append split_half_ts(2))
    ultimately show ?thesis
      using split_half_ts split_half_conc[of ks "ls@[sep]" rs] assms
      by auto
  qed
  ultimately show ?thesis 
    using split_half_ts False by auto
qed simp

lemma height_up\<^sub>i_merge: "height_up\<^sub>i (Up\<^sub>i l a r) = height t \<Longrightarrow> height (Node (ls@(t,x)#rs) tt) = height (Node (ls@(l,a)#(r,x)#rs) tt)"
  by simp

lemma ins_height: "height_up\<^sub>i (ins k x t) = height t"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_list: "split ts x = (ls,rs)"
    by (meson surj_pair)
  then have split_append: "ts = ls@rs"
    using split_conc
    by auto
  then show ?case
  proof (cases rs)
    case Nil
    then have height_sub: "height_up\<^sub>i (ins k x t) = height t"
      using 2 by (simp add: split_list)
    then show ?thesis
    proof (cases "ins k x t")
      case (T\<^sub>i a)
      then have "height (Node ts t) = height (Node ts a)"
        using height_sub
        by simp
      then show ?thesis
        using T\<^sub>i Nil split_list split_append
        by simp
    next
      case (Up\<^sub>i l a r)
      then have "height (Node ls t) = height (Node (ls@[(l,a)]) r)"
        using height_bplustree_order height_sub by (induction ls) auto
      then show ?thesis using 2 Nil split_list Up\<^sub>i split_append
        by (simp del: node\<^sub>i.simps add: node\<^sub>i_height)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a) auto
    then have height_sub: "height_up\<^sub>i (ins k x sub) = height sub"
      by (metis "2.IH"(2) a_split Cons split_list)
    then show ?thesis
    proof (cases "ins k x sub")
      case (T\<^sub>i a)
      then have "height a = height sub"
        using height_sub by auto
      then have "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@(a,sep)#rs) t)"
        by auto
      then show ?thesis 
        using T\<^sub>i height_sub Cons 2 split_list a_split split_append
        by (auto simp add: image_Un max.commute finite_set_ins_swap)
    next
      case (Up\<^sub>i l a r)
      then have "height (Node (ls@(sub,sep)#list) t) = height (Node (ls@(l,a)#(r,sep)#list) t)"
        using height_up\<^sub>i_merge height_sub
        by fastforce
      then show ?thesis
        using Up\<^sub>i Cons 2 split_list a_split split_append
        by (auto simp del: node\<^sub>i.simps simp add: node\<^sub>i_height image_Un max.commute finite_set_ins_swap)
    qed
  qed
qed simp


(* the below proof is overly complicated as a number of lemmas regarding height are missing *)
lemma ins_bal: "bal t \<Longrightarrow> bal_up\<^sub>i (ins k x t)"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_res: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ts = ls@rs"
    using split_conc
    by fastforce

  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis 
    proof (cases "ins k x t")
      case (T\<^sub>i a)
      then have "bal (Node ls a)" unfolding bal.simps
        by (metis "2.IH"(1) "2.prems" append_Nil2 bal.simps(2) bal_up\<^sub>i.simps(1) height_up\<^sub>i.simps(1) ins_height local.Nil split_app split_res)
      then show ?thesis 
        using Nil T\<^sub>i 2 split_res
        by simp
    next
      case (Up\<^sub>i l a r)
      then have 
        "(\<forall>x\<in>set (subtrees (ls@[(l,a)])). bal x)"
        "(\<forall>x\<in>set (subtrees ls). height r = height x)"
        using 2 Up\<^sub>i Nil split_res split_app
        by simp_all (metis height_up\<^sub>i.simps(2) ins_height max_def)
      then show ?thesis unfolding ins.simps
        using Up\<^sub>i Nil 2 split_res
        by (simp del: node\<^sub>i.simps add: node\<^sub>i_bal)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)" by (cases a)
    then have "bal_up\<^sub>i (ins k x sub)" using 2 split_res
      using a_prod local.Cons split_app by auto
    show ?thesis
    proof (cases "ins k x sub")
      case (T\<^sub>i x1)
      then have  "height x1 = height t"
        by (metis "2.prems" a_prod add_diff_cancel_left' bal_split_left(1) bal_split_left(2) height_bal_tree height_up\<^sub>i.simps(1) ins_height local.Cons plus_1_eq_Suc split_app)
      then show ?thesis
        using split_app Cons T\<^sub>i 2 split_res a_prod
        by auto
    next
      case (Up\<^sub>i l a r)
        (* The only case where explicit reasoning is required - likely due to the insertion of 2 elements in the list *)
      then have
        "\<forall>x \<in> set (subtrees (ls@(l,a)#(r,sep)#list)). bal x"
        using Up\<^sub>i split_app Cons 2 \<open>bal_up\<^sub>i (ins k x sub)\<close> by auto
      moreover have "\<forall>x \<in> set (subtrees (ls@(l,a)#(r,sep)#list)). height x = height t"
        using Up\<^sub>i split_app Cons 2 \<open>bal_up\<^sub>i (ins k x sub)\<close> ins_height split_res a_prod
        apply auto
        by (metis height_up\<^sub>i.simps(2) sup.idem sup_nat_def)
      ultimately show ?thesis using Up\<^sub>i Cons 2 split_res a_prod
        by (simp del: node\<^sub>i.simps add: node\<^sub>i_bal)
    qed
  qed
qed simp

(* ins acts as ins_list wrt inorder *)

(* "simple enough" to be automatically solved *)
lemma node\<^sub>i_leaves: "leaves_up\<^sub>i (node\<^sub>i k ts t) = leaves (Node ts t)"
proof (cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls@[(sub,sep)], rs)"
    by (meson node\<^sub>i_cases)
  then have "leaves_up\<^sub>i (node\<^sub>i k ts t) = leaves_list ls @ leaves sub @ leaves_list rs @ leaves t"
    using False by auto
  also have "\<dots> = leaves (Node ts t)"
    using split_half_ts split_half_conc[of ts "ls@[(sub,sep)]" rs] by auto
  finally show ?thesis.
qed simp

corollary node\<^sub>i_leaves_simps:
  "node\<^sub>i k ts t = T\<^sub>i t' \<Longrightarrow> leaves t' = leaves (Node ts t)"
  "node\<^sub>i k ts t = Up\<^sub>i l a r \<Longrightarrow> leaves l @ leaves r = leaves (Node ts t)"
   apply (metis leaves_up\<^sub>i.simps(1) node\<^sub>i_leaves)
  by (metis leaves_up\<^sub>i.simps(2) node\<^sub>i_leaves)

lemma Lnode\<^sub>i_leaves: "leaves_up\<^sub>i (Lnode\<^sub>i k xs) = leaves (Leaf xs)"
proof (cases "length xs \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half xs = (ls@[sep], rs)"
    by (meson Lnode\<^sub>i_cases)
  then have "leaves_up\<^sub>i (Lnode\<^sub>i k xs) = ls @ sep # rs"
    using False by auto
  also have "\<dots> = leaves (Leaf xs)"
    using split_half_ts split_half_conc[of xs "ls@[sep]" rs] by auto
  finally show ?thesis.
qed simp

corollary Lnode\<^sub>i_leaves_simps:
  "Lnode\<^sub>i k xs = T\<^sub>i t \<Longrightarrow> leaves t = leaves (Leaf xs)"
  "Lnode\<^sub>i k xs = Up\<^sub>i l a r \<Longrightarrow> leaves l @ leaves r = leaves (Leaf xs)"
   apply (metis leaves_up\<^sub>i.simps(1) Lnode\<^sub>i_leaves)
  by (metis leaves_up\<^sub>i.simps(2) Lnode\<^sub>i_leaves)



(* specialize ins_list_sorted since it is cumbersome to express
 "inorder_list ts" as "xs @ [a]" and always having to use the implicit properties of split*)

lemma ins_list_split:
  assumes "Laligned (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, rs)"
  shows "ins_list x (leaves (Node ts t)) = leaves_list ls @ ins_list x (leaves_list rs @ leaves t)"
proof (cases ls)
  case Nil
  then show ?thesis
    using assms by (auto dest!: split_conc)
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.distinct(1) rev_exhaust surj_pair)
  have sorted_inorder: "sorted_less (inorder (Node ts t))"
    using Laligned_sorted_inorder assms(1) sorted_cons sorted_snoc by blast
  moreover have x_sm_sep: "sep < x"
    using split_req(2)[of ts x ls' sub sep rs]
    using sorted_inorder_separators[of ts t] sorted_inorder
    using assms ls_tail_split
    by auto
  moreover have leaves_split: "leaves (Node ts t) = leaves_list ls @ leaves_list rs @ leaves t"
    using assms(3) split_tree.leaves_split by blast
  then show ?thesis
  proof (cases "leaves_list ls")
    case Nil
    then show ?thesis
      by (metis append_self_conv2 leaves_split)
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
    moreover have "sorted_less (leaves_list ls)"
      using assms(2) leaves_split sorted_wrt_append by auto
    ultimately show ?thesis
      using assms(2) ls_tail_split leaves_tail_split leaves_split x_sm_sep
      using ins_list_sorted[of leavesls' l' x "leaves_list rs@leaves t"]
      by auto
  qed
qed

lemma ins_list_split_right:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (leaves (Node ts t))"
    and "Laligned (Node ts t) u"
  shows "ins_list x (leaves_list ((sub,sep)#rs) @ leaves t) = ins_list x (leaves sub) @ leaves_list rs @ leaves t"
proof -
  from assms have x_sm_sep: "x \<le> sep"
  proof -
    from assms have "sorted_less (separators ts)"
      using Laligned_sorted_separators sorted_cons sorted_snoc by blast
    then show ?thesis
      using split_req(3)
      using assms
      by blast
  qed
  then show ?thesis
  proof (cases "leaves_list rs @ leaves t")
    case Nil
    moreover have "leaves_list ((sub,sep)#rs) @ leaves t = leaves sub @ leaves_list rs @ leaves t"
      by simp
    ultimately show ?thesis 
      by (metis self_append_conv)
  next
    case (Cons r' rs')
    then have "sep < r'"
      by (metis aligned_leaves_inbetween Laligned_split_right assms(1) assms(3) leaves.simps(2) list.set_intros(1) split_set.split_conc split_set_axioms)
    then have  "x < r'"
      using \<open>x \<le> sep\<close> by auto
    moreover have "sorted_less (leaves sub @ [r'])"
    proof -
      have "sorted_less (leaves_list ls @ leaves sub @ leaves_list rs @ leaves t)"
        using assms(1) assms(2) split_tree.leaves_split split_set_axioms by fastforce
      then show ?thesis
        using assms 
        by (metis Cons sorted_mid_iff sorted_wrt_append)
    qed
    ultimately show ?thesis
      using ins_list_sorted[of "leaves sub" r' x rs'] Cons
      by auto
  qed
qed


(* a simple lemma, missing from the standard as of now *)
lemma ins_list_idem_eq_isin: "sorted_less xs \<Longrightarrow> x \<in> set xs \<longleftrightarrow> (ins_list x xs = xs)"
  apply(induction xs)
   apply auto
  done

lemma ins_list_contains_idem: "\<lbrakk>sorted_less xs; x \<in> set xs\<rbrakk> \<Longrightarrow> (ins_list x xs = xs)"
  using ins_list_idem_eq_isin by auto

lemma aligned_insert_list: "sorted_less ks \<Longrightarrow> l < x \<Longrightarrow> x \<le> u \<Longrightarrow> aligned l (Leaf ks) u \<Longrightarrow> aligned l (Leaf (insert_list x ks)) u"
  using insert_list_req
  by (simp add: set_ins_list)

lemma align_subst_two: "aligned l (Node (ts@[(sub,sep)]) t) u \<Longrightarrow> aligned sep lt a \<Longrightarrow> aligned a rt u \<Longrightarrow> aligned l (Node (ts@[(sub,sep),(lt,a)]) rt) u" 
  apply(induction ts arbitrary: l)
  apply auto
  done

lemma align_subst_three: "aligned l (Node (ls@(subl,sepl)#(subr,sepr)#rs) t) u \<Longrightarrow> aligned sepl lt a \<Longrightarrow> aligned a rt sepr \<Longrightarrow> aligned l (Node (ls@(subl,sepl)#(lt,a)#(rt,sepr)#rs) t) u" 
  apply(induction ls arbitrary: l)
  apply auto
  done


declare node\<^sub>i.simps [simp del]
declare node\<^sub>i_leaves [simp add]

lemma ins_inorder: 
  assumes "k > 0"
    and "aligned l t u"
    and "sorted_less (leaves t)"
    and "root_order k t"
    and "l < x" "x \<le> u"
  shows "(leaves_up\<^sub>i (ins k x t)) = ins_list x (leaves t) \<and> aligned_up\<^sub>i l (ins k x t) u"
  using assms
proof(induction k x t arbitrary: l u rule: ins.induct)
  case (1 k x ks)
  then show ?case
  proof (safe, goal_cases)
    case _: 1
    then show ?case   
      using 1 insert_list_req by auto
  next
    case 2
    from 1 have "aligned l (Leaf (insert_list x ks)) u" 
      by (metis aligned_insert_list leaves.simps(1))
    moreover have "sorted_less (insert_list x ks)"
      using "1.prems"(3) split_set.insert_list_req split_set_axioms
      by auto
    ultimately show ?case
      using Lnode\<^sub>i_aligned[of l "insert_list x ks" u k] 1
      by (auto simp del: Lnode\<^sub>i.simps split_half.simps)
  qed
next
  case (2 k x ts t)
  then obtain ls rs where list_split: "split ts x = (ls,rs)"
    by (cases "split ts x")
  then have list_conc: "ts = ls@rs"
    using split_set.split_conc split_set_axioms by blast
  then show ?case
  proof (cases rs)
    case Nil
    then obtain ts' sub' sep' where "ts = ts'@[(sub',sep')]"
      apply(cases ts)
      using 2 list_conc Nil apply(simp)
      by (metis isin.cases list.distinct(1) rev_exhaust)
    have IH: "leaves_up\<^sub>i (ins k x t) = ins_list x (leaves t) \<and> aligned_up\<^sub>i sep' (ins k x t) u"
      proof - 
        (* we need to fulfill all these IH requirements *)
        note "2.IH"(1)[OF sym[OF list_split] Nil "2.prems"(1), of sep' u]
        have "sorted_less (leaves t)"
          using "2.prems"(3) sorted_leaves_induct_last by blast
        moreover have "sep' < x"
          using split_req[of ts x] list_split
          by (metis "2.prems"(2) \<open>ts = ts' @ [(sub', sep')]\<close> aligned_sorted_separators local.Nil self_append_conv sorted_cons sorted_snoc)
        moreover have "aligned sep' t u"
          using "2.prems"(2) \<open>ts = ts' @ [(sub', sep')]\<close> align_last by blast
        ultimately show ?thesis
          using  "2.IH"(1)[OF sym[OF list_split] Nil "2.prems"(1), of sep' u]
          using "2.prems" list_split local.Nil sorted_leaves_induct_last
          using order_impl_root_order
          by auto
      qed
    show ?thesis
    proof (cases "ins k x t")
      case (T\<^sub>i a)
      have IH: "leaves a = ins_list x (leaves t) \<and> aligned sep' a u"
        using IH T\<^sub>i by force
      show ?thesis
      proof(safe, goal_cases)
        case 1
        have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves a"
          using list_split T\<^sub>i Nil by (auto simp add: list_conc)
        also have "\<dots> = leaves_list ls @ (ins_list x (leaves t))"
          by (simp add: IH)
        also have "\<dots> = ins_list x (leaves (Node ts t))"
          using ins_list_split
          using "2.prems" list_split Nil
          by (metis aligned_imp_Laligned append_self_conv2 concat.simps(1) list.simps(8))
        finally show ?case .
      next
        case 2
        have "aligned_up\<^sub>i l (ins k x (Node ts t)) u = aligned l (Node ts a) u"
          using Nil T\<^sub>i list_split list_conc by simp
        moreover have "aligned l (Node ts a) u"
          using "2.prems"(2)
          by (metis IH \<open>ts = ts' @ [(sub', sep')]\<close> aligned_subst_last)
        ultimately show ?case
          by auto
      qed
    next
      case (Up\<^sub>i lt a rt)
      then have IH:"leaves_up\<^sub>i (Up\<^sub>i lt a rt) = ins_list x (leaves t) \<and> aligned_up\<^sub>i sep' (Up\<^sub>i lt a rt) u"
        using IH by auto

      show ?thesis
      proof (safe, goal_cases)
        case 1
        have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves_up\<^sub>i (Up\<^sub>i lt a rt)"
          using list_split Up\<^sub>i Nil by (auto simp add: list_conc)
        also have "\<dots> = leaves_list ls @ ins_list x (leaves t)"
          using IH by simp
        also have "\<dots> = ins_list x (leaves (Node ts t))"
          using ins_list_split
          using "2.prems" list_split local.Nil
          by (metis aligned_imp_Laligned append_self_conv2 concat.simps(1) list.simps(8))
        finally show ?case. 
      next
        case 2
        have "aligned_up\<^sub>i l (ins k x (Node ts t)) u = aligned_up\<^sub>i l (node\<^sub>i k (ts @ [(lt, a)]) rt) u"
          using Nil Up\<^sub>i list_split list_conc node\<^sub>i_aligned by simp
        moreover have "aligned l (Node (ts@[(lt,a)]) rt) u"
          using "2.prems"(2) IH \<open>ts = ts' @ [(sub', sep')]\<close> align_subst_two by fastforce
        ultimately show ?case
          using node\<^sub>i_aligned
          by auto
      qed
    qed
  next
    case (Cons h list)
    then obtain sub sep where h_split: "h = (sub,sep)"
      by (cases h)

    then have sorted_inorder_sub: "sorted_less (leaves sub)"
      using "2.prems" list_conc Cons sorted_leaves_induct_subtree
      by fastforce
    moreover have order_sub: "order k sub" 
      using "2.prems" list_conc Cons h_split
      by auto
    then show ?thesis
(* TODO way to show this cleanly without distinguishing cases for ls? *)
    proof (cases ls)
      case Nil
      then have aligned_sub: "aligned l sub sep"
        using "2.prems"(2) list_conc h_split Cons
        by auto
      then have IH: "leaves_up\<^sub>i (ins k x sub) = ins_list x (leaves sub) \<and> aligned_up\<^sub>i l (ins k x sub) sep"
      proof -
        have "x \<le> sep"
          using "2.prems"(2) aligned_sorted_separators h_split list_split local.Cons sorted_cons sorted_snoc split_set.split_req(3) split_set_axioms
          by blast
        then show ?thesis
        using "2.IH"(2)[OF sym[OF list_split] Cons sym[OF h_split], of l sep]
          using "2.prems" list_split local.Nil aligned_sub sorted_inorder_sub order_sub
          using order_impl_root_order
          by auto
      qed
      then show ?thesis 
      proof (cases "ins k x sub")
        case (T\<^sub>i a)
        have IH:"leaves a = ins_list x (leaves sub) \<and> aligned l a sep"
          using T\<^sub>i IH by (auto)
        show ?thesis
        proof (safe, goal_cases)
          case 1
          have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves a @ leaves_list list @ leaves t"
            using h_split list_split T\<^sub>i Cons by simp
          also have "\<dots> = leaves_list ls @ ins_list x (leaves sub) @ leaves_list list @ leaves t"
            using IH by simp
          also have "\<dots> = ins_list x (leaves (Node ts t))"
            using ins_list_split ins_list_split_right
            using list_split "2.prems" Cons h_split
            by (metis aligned_imp_Laligned)
          finally show ?case.
        next
          case 2
          have "aligned_up\<^sub>i l (ins k x (Node ts t)) u = aligned l (Node ((a,sep)#list) t) u"
            using Nil Cons list_conc list_split h_split T\<^sub>i by simp
          moreover have "aligned l (Node ((a,sep)#list) t) u"
            using aligned_sub "2.prems"(2) IH h_split list_conc Cons Nil
            by auto
          ultimately show ?case
            by auto
        qed
      next
        case (Up\<^sub>i lt a rt)
        then have IH:"leaves_up\<^sub>i (Up\<^sub>i lt a rt) = ins_list x (leaves sub) \<and> aligned_up\<^sub>i l (Up\<^sub>i lt a rt) sep"
          using IH h_split list_split Cons sorted_inorder_sub
          by auto
        show ?thesis
        proof (safe, goal_cases)
          case 1
          have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves lt @ leaves rt @ leaves_list list @ leaves t"
            using h_split list_split Up\<^sub>i Cons by simp
          also have "\<dots> = leaves_list ls @ ins_list x (leaves sub) @ leaves_list list @ leaves t"
            using IH by simp
          also have "\<dots> = ins_list x (leaves (Node ts t))"
            using ins_list_split ins_list_split_right
            using list_split "2.prems" Cons h_split
            by (metis aligned_imp_Laligned)
          finally show ?case.
        next
          case 2
          have "aligned_up\<^sub>i l (ins k x (Node ts t)) u = aligned_up\<^sub>i l (node\<^sub>i k ((lt,a)#(rt,sep)#list) t) u"
            using Nil Cons list_conc list_split h_split Up\<^sub>i by simp
          moreover have "aligned l (Node ((lt,a)#(rt,sep)#list) t) u"
            using aligned_sub "2.prems"(2) IH h_split list_conc Cons Nil
            by auto
          ultimately show ?case
            using node\<^sub>i_aligned by auto
        qed
      qed
    next
      case ls_split': Cons
      then obtain ls' sub' sep' where ls_split: "ls = ls'@[(sub',sep')]"
        by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
      then have aligned_sub: "aligned sep' sub sep"
        using "2.prems"(2) list_conc h_split Cons
        using align_last aligned_split_left by blast
      then have IH: "leaves_up\<^sub>i (ins k x sub) = ins_list x (leaves sub) \<and> aligned_up\<^sub>i sep' (ins k x sub) sep"
      proof -
        have "x \<le> sep"
          using "2.prems"(2) aligned_sorted_separators h_split list_split local.Cons sorted_cons sorted_snoc split_set.split_req(3) split_set_axioms
          by blast
        moreover have "sep' < x"
          using "2.prems"(2) aligned_sorted_separators list_split ls_split sorted_cons sorted_snoc split_set.split_req(2) split_set_axioms
          by blast
        ultimately show ?thesis
        using "2.IH"(2)[OF sym[OF list_split] Cons sym[OF h_split], of sep' sep]
          using "2.prems" list_split ls_split aligned_sub sorted_inorder_sub order_sub
          using order_impl_root_order
          by auto
      qed
      then show ?thesis
      proof (cases "ins k x sub")
        case (T\<^sub>i a)
        have IH:"leaves a = ins_list x (leaves sub) \<and> aligned sep' a sep"
          using T\<^sub>i IH by (auto)
        show ?thesis
        proof (safe, goal_cases)
          case 1
          have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves a @ leaves_list list @ leaves t"
            using h_split list_split T\<^sub>i Cons by simp
          also have "\<dots> = leaves_list ls @ ins_list x (leaves sub) @ leaves_list list @ leaves t"
            using IH by simp
          also have "\<dots> = ins_list x (leaves (Node ts t))"
            using ins_list_split ins_list_split_right
            using list_split "2.prems" Cons h_split
            by (metis aligned_imp_Laligned)
          finally show ?case.
        next
          case 2
          have "aligned_up\<^sub>i l (ins k x (Node ts t)) u = aligned l (Node (ls'@(sub',sep')#(a,sep)#list) t) u"
            using Nil Cons list_conc list_split h_split T\<^sub>i ls_split by simp
          moreover have "aligned l (Node (ls'@(sub',sep')#(a,sep)#list) t) u"
            using aligned_sub "2.prems"(2) IH h_split list_conc Cons Nil ls_split
            using aligned_subst by fastforce
          ultimately show ?case
            by auto
        qed
      next
        case (Up\<^sub>i lt a rt)
        then have IH:"leaves_up\<^sub>i (Up\<^sub>i lt a rt) = ins_list x (leaves sub) \<and> aligned_up\<^sub>i sep' (Up\<^sub>i lt a rt) sep"
          using IH h_split list_split Cons sorted_inorder_sub
          by auto
        show ?thesis
        proof (safe, goal_cases)
          case 1
          have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves lt @ leaves rt @ leaves_list list @ leaves t"
            using h_split list_split Up\<^sub>i Cons by simp
          also have "\<dots> = leaves_list ls @ ins_list x (leaves sub) @ leaves_list list @ leaves t"
            using IH by simp
          also have "\<dots> = ins_list x (leaves (Node ts t))"
            using ins_list_split ins_list_split_right
            using list_split "2.prems" Cons h_split
            by (metis aligned_imp_Laligned)
          finally show ?case.
        next
          case 2
          have "aligned_up\<^sub>i l (ins k x (Node ts t)) u = aligned_up\<^sub>i l (node\<^sub>i k (ls'@(sub',sep')#(lt,a)#(rt,sep)#list) t) u"
            using Nil Cons list_conc list_split h_split Up\<^sub>i ls_split by simp
          moreover have "aligned l (Node (ls'@(sub',sep')#(lt,a)#(rt,sep)#list) t) u"
            using aligned_sub "2.prems"(2) IH h_split list_conc Cons Nil ls_split align_subst_three
            by auto
          ultimately show ?case
            using node\<^sub>i_aligned by auto
        qed
      qed
    qed
  qed
qed

declare node\<^sub>i.simps [simp add]
declare node\<^sub>i_leaves [simp del]

lemma Laligned_insert_list: "sorted_less ks \<Longrightarrow> x \<le> u \<Longrightarrow> Laligned (Leaf ks) u \<Longrightarrow> Laligned (Leaf (insert_list x ks)) u"
  using insert_list_req
  by (simp add: set_ins_list)

lemma Lalign_subst_two: "Laligned (Node (ts@[(sub,sep)]) t) u \<Longrightarrow> aligned sep lt a \<Longrightarrow> aligned a rt u \<Longrightarrow> Laligned (Node (ts@[(sub,sep),(lt,a)]) rt) u" 
  apply(induction ts)
  apply (auto)
  by (meson align_subst_two aligned.simps(2))

lemma Lalign_subst_three: "Laligned (Node (ls@(subl,sepl)#(subr,sepr)#rs) t) u \<Longrightarrow> aligned sepl lt a \<Longrightarrow> aligned a rt sepr \<Longrightarrow> Laligned (Node (ls@(subl,sepl)#(lt,a)#(rt,sepr)#rs) t) u" 
  apply(induction ls)
  apply auto
  by (meson align_subst_three aligned.simps(2))

lemma Lnode\<^sub>i_Laligned: 
  assumes "Laligned (Leaf ks) u"
    and "sorted_less ks"
    and "k > 0"
  shows "Laligned_up\<^sub>i (Lnode\<^sub>i k ks) u"
  using assms
proof (cases "length ks \<le> 2*k")
  case False
  then obtain ls sep rs where split_half_ts: 
    "take ((length ks + 1) div 2) ks = ls@[sep]"
    "drop ((length ks + 1) div 2) ks = rs" 
    using split_half_not_empty[of ks]
    by auto                        
  moreover have "sorted_less (ls@[sep])" 
    by (metis append_take_drop_id assms(2) sorted_wrt_append split_half_ts(1))
  ultimately have "Laligned (Leaf (ls@[sep])) sep"
    using split_half_conc[of ks "ls@[sep]" rs] assms sorted_snoc_iff[of ls sep]
    by auto
  moreover have "aligned sep (Leaf rs) u"
  proof -
    have "length rs > 0"
      using False assms(3) split_half_ts(2) by fastforce
    then obtain sep' rs' where "rs = sep' # rs'"
      by (cases rs) auto
    moreover have "sep < sep'"
      by (metis append_take_drop_id assms(2) calculation in_set_conv_decomp sorted_mid_iff sorted_snoc_iff split_half_ts(1) split_half_ts(2))
    moreover have "sorted_less rs"
      by (metis append_take_drop_id assms(2) sorted_wrt_append split_half_ts(2))
    ultimately show ?thesis
      using split_half_ts split_half_conc[of ks "ls@[sep]" rs] assms
      by auto
  qed
  ultimately show ?thesis 
    using split_half_ts False by auto
qed simp

declare node\<^sub>i.simps [simp del]
declare node\<^sub>i_leaves [simp add]

lemma ins_Linorder: 
  assumes "k > 0"
    and "Laligned t u"
    and "sorted_less (leaves t)"
    and "root_order k t"
    and "x \<le> u"
  shows "(leaves_up\<^sub>i (ins k x t)) = ins_list x (leaves t) \<and> Laligned_up\<^sub>i (ins k x t) u"
  using assms
proof(induction k x t arbitrary: u rule: ins.induct)
  case (1 k x ks)
  then show ?case
  proof (safe, goal_cases)
    case _: 1
    then show ?case   
      using 1 insert_list_req by auto
  next
    case 2
    from 1 have "Laligned (Leaf (insert_list x ks)) u" 
      by (metis Laligned_insert_list leaves.simps(1))
    moreover have "sorted_less (insert_list x ks)"
      using "1.prems"(3) split_set.insert_list_req split_set_axioms
      by auto
    ultimately show ?case
      using Lnode\<^sub>i_Laligned[of "insert_list x ks" u k] 1
      by (auto simp del: Lnode\<^sub>i.simps split_half.simps)
  qed
next
  case (2 k x ts t)
  then obtain ls rs where list_split: "split ts x = (ls,rs)"
    by (cases "split ts x")
  then have list_conc: "ts = ls@rs"
    using split_set.split_conc split_set_axioms by blast
  then show ?case
  proof (cases rs)
    case Nil
    then obtain ts' sub' sep' where "ts = ts'@[(sub',sep')]"
      apply(cases ts)
      using 2 list_conc Nil apply(simp)
      by (metis isin.cases list.distinct(1) rev_exhaust)
    have IH: "leaves_up\<^sub>i (ins k x t) = ins_list x (leaves t) \<and> aligned_up\<^sub>i sep' (ins k x t) u"
(* this is now a case covered by the previous proof *)
      proof - 
        (* we need to fulfill all these IH requirements *)
        note ins_inorder[of k]
        have "sorted_less (leaves t)"
          using "2.prems"(3) sorted_leaves_induct_last by blast
        moreover have "sep' < x"
          using split_req[of ts x] list_split
          by (metis "2.prems"(2) Laligned_sorted_separators \<open>ts = ts' @ [(sub', sep')]\<close> local.Nil self_append_conv sorted_snoc)
        moreover have "aligned sep' t u"
          using "2.prems"(2) Lalign_last \<open>ts = ts' @ [(sub', sep')]\<close> by blast
        ultimately show ?thesis
          by (meson "2.prems"(1) "2.prems"(4) "2.prems"(5) ins_inorder order_impl_root_order root_order.simps(2))
      qed
    show ?thesis
    proof (cases "ins k x t")
      case (T\<^sub>i a)
      have IH: "leaves a = ins_list x (leaves t) \<and> aligned sep' a u"
        using IH T\<^sub>i by force
      show ?thesis
      proof(safe, goal_cases)
        case 1
        have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves a"
          using list_split T\<^sub>i Nil by (auto simp add: list_conc)
        also have "\<dots> = leaves_list ls @ (ins_list x (leaves t))"
          by (simp add: IH)
        also have "\<dots> = ins_list x (leaves (Node ts t))"
          using ins_list_split
          using "2.prems" list_split Nil
          by auto
        finally show ?case .
      next
        case 2
        have "Laligned_up\<^sub>i (ins k x (Node ts t)) u = Laligned (Node ts a) u"
          using Nil T\<^sub>i list_split list_conc by simp
        moreover have "Laligned (Node ts a) u"
          using "2.prems"(2)
          by (metis IH \<open>ts = ts' @ [(sub', sep')]\<close> Laligned_subst_last)
        ultimately show ?case
          by auto
      qed
    next
      case (Up\<^sub>i lt a rt)
      then have IH:"leaves_up\<^sub>i (Up\<^sub>i lt a rt) = ins_list x (leaves t) \<and> aligned_up\<^sub>i sep' (Up\<^sub>i lt a rt) u"
        using IH by auto

      show ?thesis
      proof (safe, goal_cases)
        case 1
        have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves_up\<^sub>i (Up\<^sub>i lt a rt)"
          using list_split Up\<^sub>i Nil by (auto simp add: list_conc)
        also have "\<dots> = leaves_list ls @ ins_list x (leaves t)"
          using IH by simp
        also have "\<dots> = ins_list x (leaves (Node ts t))"
          using ins_list_split
          using "2.prems" list_split local.Nil by auto
        finally show ?case. 
      next
        case 2
        have "Laligned_up\<^sub>i (ins k x (Node ts t)) u = Laligned_up\<^sub>i (node\<^sub>i k (ts @ [(lt, a)]) rt) u"
          using Nil Up\<^sub>i list_split list_conc node\<^sub>i_aligned by simp
        moreover have "Laligned (Node (ts@[(lt,a)]) rt) u"
          using "2.prems"(2) IH \<open>ts = ts' @ [(sub', sep')]\<close> Lalign_subst_two by fastforce
        ultimately show ?case
          using node\<^sub>i_Laligned
          by auto
      qed
    qed
  next
    case (Cons h list)
    then obtain sub sep where h_split: "h = (sub,sep)"
      by (cases h)

    then have sorted_inorder_sub: "sorted_less (leaves sub)"
      using "2.prems" list_conc Cons sorted_leaves_induct_subtree
      by fastforce
    moreover have order_sub: "order k sub" 
      using "2.prems" list_conc Cons h_split
      by auto
    then show ?thesis
(* TODO way to show this cleanly without distinguishing cases for ls? *)
    proof (cases ls)
      case Nil
      then have aligned_sub: "Laligned sub sep"
        using "2.prems"(2) list_conc h_split Cons
        by auto
      then have IH: "leaves_up\<^sub>i (ins k x sub) = ins_list x (leaves sub) \<and> Laligned_up\<^sub>i (ins k x sub) sep"
      proof -
        have "x \<le> sep"
          using "2.prems"(2) Laligned_sorted_separators h_split list_split local.Cons sorted_snoc split_set.split_req(3) split_set_axioms
          by blast
        then show ?thesis
        using "2.IH"(2)[OF sym[OF list_split] Cons sym[OF h_split], of sep]
          using "2.prems" list_split local.Nil aligned_sub sorted_inorder_sub order_sub
          using order_impl_root_order
          by auto
      qed
      then show ?thesis 
      proof (cases "ins k x sub")
        case (T\<^sub>i a)
        have IH:"leaves a = ins_list x (leaves sub) \<and> Laligned a sep"
          using T\<^sub>i IH by (auto)
        show ?thesis
        proof (safe, goal_cases)
          case 1
          have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves a @ leaves_list list @ leaves t"
            using h_split list_split T\<^sub>i Cons by simp
          also have "\<dots> = leaves_list ls @ ins_list x (leaves sub) @ leaves_list list @ leaves t"
            using IH by simp
          also have "\<dots> = ins_list x (leaves (Node ts t))"
            using ins_list_split ins_list_split_right
            using list_split "2.prems" Cons h_split by auto
          finally show ?case.
        next
          case 2
          have "Laligned_up\<^sub>i (ins k x (Node ts t)) u = Laligned (Node ((a,sep)#list) t) u"
            using Nil Cons list_conc list_split h_split T\<^sub>i by simp
          moreover have "Laligned (Node ((a,sep)#list) t) u"
            using aligned_sub "2.prems"(2) IH h_split list_conc Cons Nil
            by auto
          ultimately show ?case
            by auto
        qed
      next
        case (Up\<^sub>i lt a rt)
        then have IH:"leaves_up\<^sub>i (Up\<^sub>i lt a rt) = ins_list x (leaves sub) \<and> Laligned_up\<^sub>i (Up\<^sub>i lt a rt) sep"
          using IH h_split list_split Cons sorted_inorder_sub
          by auto
        show ?thesis
        proof (safe, goal_cases)
          case 1
          have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves lt @ leaves rt @ leaves_list list @ leaves t"
            using h_split list_split Up\<^sub>i Cons by simp
          also have "\<dots> = leaves_list ls @ ins_list x (leaves sub) @ leaves_list list @ leaves t"
            using IH by simp
          also have "\<dots> = ins_list x (leaves (Node ts t))"
            using ins_list_split ins_list_split_right
            using list_split "2.prems" Cons h_split by auto
          finally show ?case.
        next
          case 2
          have "Laligned_up\<^sub>i (ins k x (Node ts t)) u = Laligned_up\<^sub>i (node\<^sub>i k ((lt,a)#(rt,sep)#list) t) u"
            using Nil Cons list_conc list_split h_split Up\<^sub>i by simp
          moreover have "Laligned (Node ((lt,a)#(rt,sep)#list) t) u"
            using aligned_sub "2.prems"(2) IH h_split list_conc Cons Nil
            by auto
          ultimately show ?case
            using node\<^sub>i_Laligned by auto
        qed
      qed
    next
      case ls_split': Cons
      then obtain ls' sub' sep' where ls_split: "ls = ls'@[(sub',sep')]"
        by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
      then have aligned_sub: "aligned sep' sub sep"
        using "2.prems"(2) list_conc h_split Cons
        using Lalign_last Laligned_split_left
        by blast
      then have IH: "leaves_up\<^sub>i (ins k x sub) = ins_list x (leaves sub) \<and> aligned_up\<^sub>i sep' (ins k x sub) sep"
      proof -
        have "x \<le> sep"
          using "2.prems"(2) Laligned_sorted_separators h_split list_split local.Cons sorted_snoc split_set.split_req(3) split_set_axioms
          by blast
        moreover have "sep' < x"
          using "2.prems"(2) Laligned_sorted_separators list_split ls_split sorted_cons sorted_snoc split_set.split_req(2) split_set_axioms
          by blast
        ultimately show ?thesis
          using "2.prems"(1) aligned_sub ins_inorder order_sub sorted_inorder_sub
          using order_impl_root_order
          by blast
      qed
      then show ?thesis
      proof (cases "ins k x sub")
        case (T\<^sub>i a)
        have IH:"leaves a = ins_list x (leaves sub) \<and> aligned sep' a sep"
          using T\<^sub>i IH by (auto)
        show ?thesis
        proof (safe, goal_cases)
          case 1
          have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves a @ leaves_list list @ leaves t"
            using h_split list_split T\<^sub>i Cons by simp
          also have "\<dots> = leaves_list ls @ ins_list x (leaves sub) @ leaves_list list @ leaves t"
            using IH by simp
          also have "\<dots> = ins_list x (leaves (Node ts t))"
            using ins_list_split ins_list_split_right
            using list_split "2.prems" Cons h_split by auto
          finally show ?case.
        next
          case 2
          have "Laligned_up\<^sub>i (ins k x (Node ts t)) u = Laligned (Node (ls'@(sub',sep')#(a,sep)#list) t) u"
            using Nil Cons list_conc list_split h_split T\<^sub>i ls_split by simp
          moreover have "Laligned (Node (ls'@(sub',sep')#(a,sep)#list) t) u"
            using aligned_sub "2.prems"(2) IH h_split list_conc Cons Nil ls_split
            using Laligned_subst by fastforce
          ultimately show ?case
            by auto
        qed
      next
        case (Up\<^sub>i lt a rt)
        then have IH:"leaves_up\<^sub>i (Up\<^sub>i lt a rt) = ins_list x (leaves sub) \<and> aligned_up\<^sub>i sep' (Up\<^sub>i lt a rt) sep"
          using IH h_split list_split Cons sorted_inorder_sub
          by auto
        show ?thesis
        proof (safe, goal_cases)
          case 1
          have "leaves_up\<^sub>i (ins k x (Node ts t)) = leaves_list ls @ leaves lt @ leaves rt @ leaves_list list @ leaves t"
            using h_split list_split Up\<^sub>i Cons by simp
          also have "\<dots> = leaves_list ls @ ins_list x (leaves sub) @ leaves_list list @ leaves t"
            using IH by simp
          also have "\<dots> = ins_list x (leaves (Node ts t))"
            using ins_list_split ins_list_split_right
            using list_split "2.prems" Cons h_split by auto
          finally show ?case.
        next
          case 2
          have "Laligned_up\<^sub>i (ins k x (Node ts t)) u = Laligned_up\<^sub>i (node\<^sub>i k (ls'@(sub',sep')#(lt,a)#(rt,sep)#list) t) u"
            using Nil Cons list_conc list_split h_split Up\<^sub>i ls_split by simp
          moreover have "Laligned (Node (ls'@(sub',sep')#(lt,a)#(rt,sep)#list) t) u"
            using aligned_sub "2.prems"(2) IH h_split list_conc Cons Nil ls_split Lalign_subst_three
            by auto
          ultimately show ?case
            using node\<^sub>i_Laligned by auto
        qed
      qed
    qed
  qed
qed

declare node\<^sub>i.simps [simp add]
declare node\<^sub>i_leaves [simp del]


thm ins.induct
thm bplustree.induct

(* wrapped up insert invariants *)

lemma tree\<^sub>i_bal: "bal_up\<^sub>i u \<Longrightarrow> bal (tree\<^sub>i u)"
  apply(cases u)
   apply(auto)
  done

lemma tree\<^sub>i_order: "\<lbrakk>k > 0; root_order_up\<^sub>i k u\<rbrakk> \<Longrightarrow> root_order k (tree\<^sub>i u)"
  apply(cases u)
   apply(auto simp add: order_impl_root_order)
  done

lemma tree\<^sub>i_inorder: "inorder_up\<^sub>i u = inorder (tree\<^sub>i u)"
  apply (cases u)
   apply auto
  done

lemma tree\<^sub>i_leaves: "leaves_up\<^sub>i u = leaves (tree\<^sub>i u)"
  apply (cases u)
   apply auto
  done

lemma tree\<^sub>i_aligned: "aligned_up\<^sub>i l a u \<Longrightarrow> aligned l (tree\<^sub>i a) u"
  apply (cases a)
   apply auto
  done

lemma tree\<^sub>i_Laligned: "Laligned_up\<^sub>i a u \<Longrightarrow> Laligned (tree\<^sub>i a) u"
  apply (cases a)
   apply auto
  done

lemma insert_bal: "bal t \<Longrightarrow> bal (insert k x t)"
  using ins_bal
  by (simp add: tree\<^sub>i_bal)

lemma insert_order: "\<lbrakk>k > 0; sorted_less (leaves t); root_order k t\<rbrakk> \<Longrightarrow> root_order k (insert k x t)"
  using ins_root_order
  by (simp add: tree\<^sub>i_order)


lemma insert_inorder: 
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "aligned l t u" "l < x" "x \<le> u"
  shows "leaves (insert k x t) = ins_list x (leaves t)"
    and "aligned l (insert k x t) u"
  using ins_inorder assms
  by (simp_all add: tree\<^sub>i_leaves tree\<^sub>i_aligned)

lemma insert_Linorder: 
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "Laligned t u" "x \<le> u"
  shows "leaves (insert k x t) = ins_list x (leaves t)"
    and "Laligned (insert k x t) u"
  using ins_Linorder insert_inorder assms
  by (simp_all add: tree\<^sub>i_leaves tree\<^sub>i_Laligned)

corollary insert_Linorder_top:
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "Laligned t top"
  shows "leaves (insert k x t) = ins_list x (leaves t)"
    and "Laligned (insert k x t) top"
  using insert_Linorder top_greatest assms by simp_all

subsection "Deletion"

text "The following deletion method is inspired by Bauer (70) and Fielding (??).
Rather than stealing only a single node from the neighbour,
the neighbour is fully merged with the potentially underflowing node.
If the resulting node is still larger than allowed, the merged node is split
again, using the rules known from insertion splits.
If the resulting node has admissable size, it is simply kept in the tree."

fun rebalance_middle_tree where
  "rebalance_middle_tree k ls (Leaf ms) sep rs (Leaf ts) = (
  if length ms \<ge> k \<and> length ts \<ge> k then 
    Node (ls@(Leaf ms,sep)#rs) (Leaf ts)
  else (
    case rs of [] \<Rightarrow> (
      case Lnode\<^sub>i k (ms@ts) of
       T\<^sub>i u \<Rightarrow>
        Node ls u |
       Up\<^sub>i l a r \<Rightarrow>
        Node (ls@[(l,a)]) r) |
    (Leaf rrs,rsep)#rs \<Rightarrow> (
      case Lnode\<^sub>i k (ms@rrs) of
      T\<^sub>i u \<Rightarrow>
        Node (ls@(u,rsep)#rs) (Leaf ts) |
      Up\<^sub>i l a r \<Rightarrow>
        Node (ls@(l,a)#(r,rsep)#rs) (Leaf ts))
))" |
  "rebalance_middle_tree k ls (Node mts mt) sep rs (Node tts tt) = (
  if length mts \<ge> k \<and> length tts \<ge> k then 
    Node (ls@(Node mts mt,sep)#rs) (Node tts tt)
  else (
    case rs of [] \<Rightarrow> (
      case node\<^sub>i k (mts@(mt,sep)#tts) tt of
       T\<^sub>i u \<Rightarrow>
        Node ls u |
       Up\<^sub>i l a r \<Rightarrow>
        Node (ls@[(l,a)]) r) |
    (Node rts rt,rsep)#rs \<Rightarrow> (
      case node\<^sub>i k (mts@(mt,sep)#rts) rt of
      T\<^sub>i u \<Rightarrow>
        Node (ls@(u,rsep)#rs) (Node tts tt) |
      Up\<^sub>i l a r \<Rightarrow>
        Node (ls@(l,a)#(r,rsep)#rs) (Node tts tt))
))"


text "All trees are merged with the right neighbour on underflow.
Obviously for the last tree this would not work since it has no right neighbour.
Therefore this tree, as the only exception, is merged with the left neighbour.
However since we it does not make a difference, we treat the situation
as if the second to last tree underflowed."

fun rebalance_last_tree where
  "rebalance_last_tree k ts t = (
case last ts of (sub,sep) \<Rightarrow>
   rebalance_middle_tree k (butlast ts) sub sep [] t
)"

text "Rather than deleting the minimal key from the right subtree,
we remove the maximal key of the left subtree.
This is due to the fact that the last tree can easily be accessed
and the left neighbour is way easier to access than the right neighbour,
it resides in the same pair as the separating element to be removed."


fun del where
  "del k x (Leaf xs) = (Leaf (delete_list x xs))" |
  "del k x (Node ts t) = (
  case split ts x of 
    (ls,[]) \<Rightarrow> 
     rebalance_last_tree k ls (del k x t)
  | (ls,(sub,sep)#rs) \<Rightarrow> (
     rebalance_middle_tree k ls (del k x sub) sep rs t
  )
)"

fun reduce_root where
  "reduce_root (Leaf xs) = (Leaf xs)" |
  "reduce_root (Node ts t) = (case ts of
   [] \<Rightarrow> t |
   _ \<Rightarrow> (Node ts t)
)"


fun delete where "delete k x t = reduce_root (del k x t)"


text "An invariant for intermediate states at deletion.
In particular we allow for an underflow to 0 subtrees."

fun almost_order where
  "almost_order k (Leaf xs) = (length xs \<le> 2*k)" |
  "almost_order k (Node ts t) = (
  (length ts \<le> 2*k) \<and>
  (\<forall>s \<in> set (subtrees ts). order k s) \<and>
   order k t
)"



text "Deletion proofs"

thm list.simps



lemma rebalance_middle_tree_height:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "height (rebalance_middle_tree k ls sub sep rs t) = height (Node (ls@(sub,sep)#rs) t)"
proof (cases "height t")
  case 0
  then obtain ts subs where "t = Leaf ts" "sub = Leaf subs" using height_Leaf assms
    by metis
  moreover have "rs = (rsub,rsep) # list \<Longrightarrow> rsub = Node rts rt \<Longrightarrow> False"
    for rsub rsep list rts rt
  proof (goal_cases)
    case 1
    then have "height rsub = height t"
      using assms(2) by auto
    then have "height rsub = 0"
      using 0 by simp
    then show ?case
      using "1"(2) height_Leaf by blast
  qed 
  ultimately show ?thesis
    by (auto split!: list.splits bplustree.splits)
next
  case (Suc nat)
  then obtain tts tt where t_node: "t = Node tts tt"
    using height_Leaf by (cases t) simp
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) simp
  then show ?thesis
  proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      then have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt) = height (Node (mts@(mt,sep)#tts) tt)"
        using node\<^sub>i_height by blast
      also have "\<dots> = max (height t) (height sub)"
        by (metis assms(1) height_up\<^sub>i.simps(2) height_list_split sub_node t_node)
      finally have height_max: "height_up\<^sub>i (node\<^sub>i k (mts @ (mt, sep) # tts) tt) = max (height t) (height sub)" by simp
      then show ?thesis
      proof (cases "node\<^sub>i k (mts@(mt,sep)#tts) tt")
        case (T\<^sub>i u)
        then have "height u = max (height t) (height sub)" using height_max by simp
        then have "height (Node ls u) = height (Node (ls@[(sub,sep)]) t)"
          by (induction ls) (auto simp add: max.commute)
        then show ?thesis using Nil False T\<^sub>i
          by (simp add: sub_node t_node)
      next
        case (Up\<^sub>i l a r)
        then have "height (Node (ls@[(sub,sep)]) t) =  height (Node (ls@[(l,a)]) r)"
          using assms(1) height_max by (induction ls) auto
        then show ?thesis
          using Up\<^sub>i Nil sub_node t_node by auto
      qed
    next
      case (Cons a list)
      then obtain rsub rsep where a_split: "a = (rsub, rsep)"
        by (cases a)
      then obtain rts rt where r_node: "rsub = Node rts rt"
        using assms(2) Cons height_Leaf Suc by (cases rsub) simp_all

      then have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt) = height (Node (mts@(mt,sep)#rts) rt)"
        using node\<^sub>i_height by blast
      also have "\<dots> = max (height rsub) (height sub)"
        by (metis r_node height_up\<^sub>i.simps(2) height_list_split max.commute sub_node)
      finally have height_max: "height_up\<^sub>i (node\<^sub>i k (mts @ (mt, sep) # rts) rt) = max (height rsub) (height sub)" by simp
      then show ?thesis
      proof (cases "node\<^sub>i k (mts@(mt,sep)#rts) rt")
        case (T\<^sub>i u)
        then have "height u = max (height rsub) (height sub)"
          using height_max by simp
        then show ?thesis 
          using T\<^sub>i False Cons r_node a_split sub_node t_node by auto
      next
        case (Up\<^sub>i l a r)
        then have height_max: "max (height l) (height r) = max (height rsub) (height sub)"
          using height_max by auto
        then show ?thesis
          using Cons a_split r_node Up\<^sub>i sub_node t_node by auto
      qed
    qed
  qed (simp add: sub_node t_node)
qed


lemma rebalance_last_tree_height:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "height (rebalance_last_tree k ts t) = height (Node ts t)"
  using rebalance_middle_tree_height assms by auto


lemma bal_sub_height: "bal (Node (ls@a#rs) t) \<Longrightarrow> (case rs of [] \<Rightarrow> True | (sub,sep)#_ \<Rightarrow> height sub = height t)"
  by (cases rs) (auto)

lemma del_height: "\<lbrakk>k > 0; root_order k t; bal t\<rbrakk> \<Longrightarrow> height (del k x t) = height t"
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls list where list_split: "split ts x = (ls, list)" by (cases "split ts x")
  then show ?case
  proof(cases list)
    case Nil
    then have "height (del k x t) = height t"
      using 2 list_split 
      by (simp add: order_impl_root_order)
    moreover obtain lls sub sep where "ls = lls@[(sub,sep)]"
      using split_conc 2 list_split Nil
      by (metis append_Nil2 less_nat_zero_code list.size(3) old.prod.exhaust rev_exhaust root_order.simps(2))
    moreover have "Node ls t = Node ts t" using split_conc Nil list_split by auto
    ultimately show ?thesis
      using rebalance_last_tree_height 2 list_split Nil split_conc 
      by (auto simp add: max.assoc sup_nat_def max_def)
  next
    case (Cons a rs)
    then have rs_height: "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t" (* notice the difference if rsub and t are switched *)
      using "2.prems"(3) bal_sub_height list_split split_conc by blast
    from Cons obtain sub sep where a_split: "a = (sub,sep)" by (cases a)

      have height_t_sub: "height t = height sub"
        using "2.prems"(3) a_split list_split local.Cons split_set.split_set(1) split_set_axioms by fastforce
      have height_t_del: "height (del k x sub) = height t"
        by (metis "2.IH"(2) "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) list_split local.Cons order_impl_root_order root_order.simps(2) some_child_sub(1) split_set(1))
      then have "height (rebalance_middle_tree k ls (del k x sub) sep rs t) = height (Node (ls@((del k x sub),sep)#rs) t)"
        using rs_height rebalance_middle_tree_height by simp
      also have "\<dots> = height (Node (ls@(sub,sep)#rs) t)"
        using height_t_sub "2.prems" height_t_del
        by auto
      also have "\<dots> = height (Node ts t)"
        using 2 a_split list_split Cons split_set(1) split_conc
        by auto
      finally show ?thesis
        using  Cons a_split list_split 2
        by simp
  qed
qed simp

(* proof for inorders *)

(* note: this works (as it should, since there is not even recursion involved)
  automatically. *yay* *)
lemma rebalance_middle_tree_inorder:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "leaves (rebalance_middle_tree k ls sub sep rs t) = leaves (Node (ls@(sub,sep)#rs) t)"
  apply(cases sub; cases t)
  using assms 
     apply (auto
      split!: bplustree.splits up\<^sub>i.splits list.splits
      simp del: node\<^sub>i.simps Lnode\<^sub>i.simps 
      simp add: node\<^sub>i_leaves_simps Lnode\<^sub>i_leaves_simps
      )
  done

lemma rebalance_last_tree_inorder:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "leaves (rebalance_last_tree k ts t) = leaves (Node ts t)"
  using rebalance_middle_tree_inorder assms by auto

lemma butlast_inorder_app_id: "xs = xs' @ [(sub,sep)] \<Longrightarrow> inorder_list xs' @ inorder sub @ [sep] = inorder_list xs"
  by simp


lemma height_bal_subtrees_merge: "\<lbrakk>height (Node as a) = height (Node bs b); bal (Node as a); bal (Node bs b)\<rbrakk>
 \<Longrightarrow> \<forall>x \<in> set (subtrees as) \<union> {a}. height x = height b"
  by (metis Suc_inject Un_iff bal.simps(2) height_bal_tree singletonD)

lemma bal_list_merge: 
  assumes "bal_up\<^sub>i (Up\<^sub>i (Node as a) x (Node bs b))"
  shows "bal (Node (as@(a,x)#bs) b)"
proof -
  have "\<forall>x\<in>set (subtrees (as @ (a, x) # bs)). bal x"
    using subtrees_split assms by auto
  moreover have "bal b"
    using assms by auto
  moreover have "\<forall>x\<in>set (subtrees as) \<union> {a} \<union> set (subtrees bs). height x = height b"
    using assms height_bal_subtrees_merge
    unfolding bal_up\<^sub>i.simps
    by blast
  ultimately show ?thesis
    by auto
qed

lemma node\<^sub>i_bal_up\<^sub>i: 
  assumes "bal_up\<^sub>i (node\<^sub>i k ts t)"
  shows "bal (Node ts t)"
  using assms
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where split_list: "split_half ts = (ls@[(sub,sep)], rs)"
    using node\<^sub>i_cases by blast
  then have "node\<^sub>i k ts t = Up\<^sub>i (Node ls sub) sep (Node rs t)"
    using False by auto
  moreover have "ts = ls@(sub,sep)#rs"
    by (metis append_Cons append_Nil2 append_eq_append_conv2 local.split_list same_append_eq split_half_conc)
  ultimately show ?thesis
    using bal_list_merge[of ls sub sep rs t] assms
    by (simp del: bal.simps bal_up\<^sub>i.simps)
qed simp

lemma node\<^sub>i_bal_simp: "bal_up\<^sub>i (node\<^sub>i k ts t) = bal (Node ts t)"
  using node\<^sub>i_bal node\<^sub>i_bal_up\<^sub>i by blast

lemma rebalance_middle_tree_bal:
  assumes "bal (Node (ls@(sub,sep)#rs) t)"
  shows "bal (rebalance_middle_tree k ls sub sep rs t)"
proof (cases t)
  case t_node: (Leaf txs)
  then obtain mxs where sub_node: "sub = Leaf mxs"
    using assms by (cases sub) (auto simp add: t_node)
  then have sub_heights: "height sub = height t" "bal sub" "bal t"
    apply (metis Suc_inject assms bal_split_left(1) bal_split_left(2) height_bal_tree)
    apply (meson assms bal.simps(2) bal_split_left(1))
    using assms bal.simps(2) by blast
  show ?thesis
  proof (cases "length mxs \<ge> k \<and> length txs \<ge> k")
    case True
    then show ?thesis
      using t_node sub_node assms
      by (auto simp del: bal.simps)
  next
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      have "height_up\<^sub>i (Lnode\<^sub>i k (mxs@txs)) = height (Leaf (mxs@txs))"
        using Lnode\<^sub>i_height by blast
      also have "\<dots> = 0"
        by simp
      also have "\<dots> = height t"
        using height_bal_tree sub_heights(3) t_node by fastforce
      finally have "height_up\<^sub>i (Lnode\<^sub>i k (mxs@txs)) = height t" .
      moreover have "bal_up\<^sub>i (Lnode\<^sub>i k (mxs@txs))"
        by (simp add: bal_up\<^sub>i.elims(3) height_Leaf height_up\<^sub>i.simps(2) max_nat.neutr_eq_iff)
      ultimately show ?thesis
        apply (cases "Lnode\<^sub>i k (mxs@txs)")
        using assms Nil sub_node t_node by auto
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split: "r = (rsub,rsep)" by (cases r)
      then have rsub_height: "height rsub = height t" "bal rsub"
        using assms Cons by auto
      then obtain rxs where r_node: "rsub = Leaf rxs"
        apply(cases rsub) using assms t_node by auto
      have "height_up\<^sub>i (Lnode\<^sub>i k (mxs@rxs)) = height (Leaf (mxs@rxs))"
        using Lnode\<^sub>i_height by blast
      also have "\<dots> = 0"
        by auto
      also have "\<dots> = height rsub"
        using height_bal_tree r_node rsub_height(2) by fastforce
      finally have 1: "height_up\<^sub>i (Lnode\<^sub>i k (mxs@rxs)) = height rsub" .
      moreover have 2: "bal_up\<^sub>i (Lnode\<^sub>i k (mxs@rxs))"
        by simp
      ultimately show ?thesis
      proof (cases "Lnode\<^sub>i k (mxs@rxs)")
        case (T\<^sub>i u)
        then have "bal (Node (ls@(u,rsep)#rs) t)"
          using 1 2 Cons assms t_node subtrees_split sub_heights r_split rsub_height
          unfolding bal.simps by (auto simp del: height_bplustree.simps)
        then show ?thesis
          using Cons assms t_node sub_node r_split r_node False T\<^sub>i
          by (auto simp del: node\<^sub>i.simps bal.simps)
      next
        case (Up\<^sub>i l a r)
        then have "bal (Node (ls@(l,a)#(r,rsep)#rs) t)"
          using 1 2 Cons assms t_node subtrees_split sub_heights r_split rsub_height
          unfolding bal.simps by (auto simp del: height_bplustree.simps)
        then show ?thesis
          using Cons assms t_node sub_node r_split r_node False Up\<^sub>i
          by (auto simp del: node\<^sub>i.simps bal.simps)
      qed
    qed
  qed
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto simp add: t_node)
  have sub_heights: "height sub = height t" "bal sub" "bal t"
    using assms by auto
  show ?thesis
  proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then show ?thesis
      using t_node sub_node assms
      by (auto simp del: bal.simps)
  next
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt) = height (Node (mts@(mt,sep)#tts) tt)"
        using node\<^sub>i_height by blast
      also have "\<dots> = Suc (height tt)"
        by (metis height_bal_tree height_up\<^sub>i.simps(2) height_list_split max.idem sub_heights(1) sub_heights(3) sub_node t_node)
      also have "\<dots> = height t"
        using height_bal_tree sub_heights(3) t_node by fastforce
      finally have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt) = height t" by simp
      moreover have "bal_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt)"
        by (metis bal_list_merge bal_up\<^sub>i.simps(2) node\<^sub>i_bal sub_heights(1) sub_heights(2) sub_heights(3) sub_node t_node)
      ultimately show ?thesis
        apply (cases "node\<^sub>i k (mts@(mt,sep)#tts) tt")
        using assms Nil sub_node t_node by auto
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split: "r = (rsub,rsep)" by (cases r)
      then have rsub_height: "height rsub = height t" "bal rsub"
        using assms Cons by auto
      then obtain rts rt where r_node: "rsub = (Node rts rt)"
        apply(cases rsub) using t_node by simp
      have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt) = height (Node (mts@(mt,sep)#rts) rt)"
        using node\<^sub>i_height by blast
      also have "\<dots> = Suc (height rt)"
        by (metis Un_iff  \<open>height rsub = height t\<close> assms bal.simps(2) bal_split_last(1) height_bal_tree height_up\<^sub>i.simps(2) height_list_split list.set_intros(1) Cons max.idem r_node r_split set_append some_child_sub(1) sub_heights(1) sub_node)
      also have "\<dots> = height rsub"
        using height_bal_tree r_node rsub_height(2) by fastforce
      finally have 1: "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt) = height rsub" .
      moreover have 2: "bal_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt)"
        by (metis bal_list_merge bal_up\<^sub>i.simps(2) node\<^sub>i_bal r_node rsub_height(1) rsub_height(2) sub_heights(1) sub_heights(2) sub_node)
      ultimately show ?thesis
      proof (cases "node\<^sub>i k (mts@(mt,sep)#rts) rt")
        case (T\<^sub>i u)
        then have "bal (Node (ls@(u,rsep)#rs) t)"
          using 1 2 Cons assms t_node subtrees_split sub_heights r_split rsub_height
          unfolding bal.simps by (auto simp del: height_bplustree.simps)
        then show ?thesis
          using Cons assms t_node sub_node r_split r_node False T\<^sub>i
          by (auto simp del: node\<^sub>i.simps bal.simps)
      next
        case (Up\<^sub>i l a r)
        then have "bal (Node (ls@(l,a)#(r,rsep)#rs) t)"
          using 1 2 Cons assms t_node subtrees_split sub_heights r_split rsub_height
          unfolding bal.simps by (auto simp del: height_bplustree.simps)
        then show ?thesis
          using Cons assms t_node sub_node r_split r_node False Up\<^sub>i
          by (auto simp del: node\<^sub>i.simps bal.simps)
      qed
    qed
  qed
qed


lemma rebalance_last_tree_bal: "\<lbrakk>bal (Node ts t); ts \<noteq> []\<rbrakk> \<Longrightarrow> bal (rebalance_last_tree k ts t)"
  using rebalance_middle_tree_bal append_butlast_last_id[of ts]
  apply(cases "last ts") 
  apply(auto simp del: bal.simps rebalance_middle_tree.simps)
  done

lemma Leaf_merge_aligned: "aligned l (Leaf ms) m \<Longrightarrow> aligned m (Leaf rs) r \<Longrightarrow> aligned l (Leaf (ms@rs)) r"
  by auto

lemma Node_merge_aligned: "
    inbetween aligned l mts mt sep \<Longrightarrow>
    inbetween aligned sep tts tt u \<Longrightarrow>
    inbetween aligned l (mts @ (mt, sep) # tts) tt u"
  apply(induction mts arbitrary: l)
  apply auto
  done

lemma aligned_subst_last_merge: "aligned l (Node (ts'@[(sub', sep'),(sub,sep)]) t) u \<Longrightarrow> aligned sep' t' u \<Longrightarrow>
  aligned l (Node (ts'@[(sub', sep')]) t') u" 
  apply (induction ts' arbitrary: l)
  apply auto
  done

lemma aligned_subst_last_merge_two: "aligned l (Node (ts@[(sub',sep'),(sub,sep)]) t) u \<Longrightarrow> aligned sep' lt a \<Longrightarrow> aligned a rt u \<Longrightarrow> aligned l (Node (ts@[(sub',sep'),(lt,a)]) rt) u" 
  apply(induction ts arbitrary: l)
  apply auto
  done

lemma aligned_subst_merge: "aligned l (Node (ls@(lsub, lsep)#(sub,sep)#(rsub,rsep)#rs) t) u \<Longrightarrow> aligned lsep sub' rsep \<Longrightarrow>
  aligned l (Node (ls@(lsub, lsep)#(sub', rsep)#rs) t) u" 
  apply (induction ls arbitrary: l)
  apply auto
  done

lemma aligned_subst_merge_two: "aligned l (Node (ls@(lsub, lsep)#(sub,sep)#(rsub,rsep)#rs) t) u \<Longrightarrow> aligned lsep sub' a \<Longrightarrow>
  aligned a rsub' rsep \<Longrightarrow> aligned l (Node (ls@(lsub, lsep)#(sub',a)#(rsub', rsep)#rs) t) u" 
  apply(induction ls arbitrary: l)
  apply auto
  done

lemma rebalance_middle_tree_aligned:
  assumes "aligned l (Node (ls@(sub,sep)#rs) t) u"
    and "height t = height sub"
    and "sorted_less (leaves (Node (ls@(sub,sep)#rs) t))"
    and "k > 0"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "aligned l (rebalance_middle_tree k ls sub sep rs t) u"
proof (cases t)
  case t_node: (Leaf txs)
  then obtain mxs where sub_node: "sub = Leaf mxs"
    using assms by (cases sub) (auto simp add: t_node)
  show ?thesis
  proof (cases "length mxs \<ge> k \<and> length txs \<ge> k")
    case True
    then show ?thesis
      using t_node sub_node assms
      by (auto simp del: bal.simps)
  next
    case False
    then show ?thesis
    proof (cases rs)
      case rs_nil: Nil
      then have sorted_leaves: "sorted_less (mxs@txs)"
        using assms(3) rs_nil t_node sub_node sorted_wrt_append
        by auto 
      then show ?thesis
      proof (cases ls)
        case ls_nil: Nil
        then have "aligned l (Leaf (mxs@txs)) u"
          using t_node sub_node assms rs_nil False
          using assms
          by auto
        then  have "aligned_up\<^sub>i l (Lnode\<^sub>i k (mxs@txs)) u"
          using Lnode\<^sub>i_aligned sorted_leaves assms by blast
        then show ?thesis
          using False t_node sub_node rs_nil ls_nil
          by (auto simp del: Lnode\<^sub>i.simps split!: up\<^sub>i.split)
      next
        case Cons
        then obtain ls' lsub lsep where ls_Cons: "ls = ls'@[(lsub,lsep)]"
          by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
        then have "aligned lsep (Leaf (mxs@txs)) u"
          using Leaf_merge_aligned
          using align_last aligned_split_left assms(1) t_node rs_nil sub_node
          by blast
        moreover have "sorted_less (mxs@txs)"
          using assms(3) rs_nil t_node sub_node
          by (auto simp add: sorted_wrt_append) 
        ultimately have "aligned_up\<^sub>i lsep (Lnode\<^sub>i k (mxs@txs)) u"
          using Lnode\<^sub>i_aligned assms(4) by blast
        then show ?thesis
          using False t_node sub_node rs_nil ls_Cons assms
          using aligned_subst_last_merge[of l ls' lsub lsep sub sep t u]
          using aligned_subst_last_merge_two[of l ls' lsub lsep sub sep t u]
          by (auto simp del: Lnode\<^sub>i.simps split!: up\<^sub>i.split)
      qed
    next
      case rs_Cons: (Cons r rs)
      then obtain rsub rsep where r_split[simp]: "r = (rsub,rsep)" by (cases r)
      then have "height rsub = 0"
        using \<open>\<And>thesis. (\<And>mxs. sub = Leaf mxs \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(2) assms(5) rs_Cons
        by fastforce
      then obtain rxs where rs_Leaf[simp]: "rsub = Leaf rxs"
        by (cases rsub) auto
      then have sorted_leaves: "sorted_less (mxs@rxs)"
        using assms(3) rs_Cons sub_node sorted_wrt_append r_split
        by (auto simp add: sorted_wrt_append) 
      then show ?thesis
      proof (cases ls)
        case ls_nil: Nil
        then have "aligned l (Leaf (mxs@rxs)) rsep"
          using sub_node assms rs_Cons False
          by auto
        then  have "aligned_up\<^sub>i l (Lnode\<^sub>i k (mxs@rxs)) rsep"
          using Lnode\<^sub>i_aligned sorted_leaves assms by blast
        then show ?thesis
          using False t_node sub_node rs_Cons ls_nil assms
          by (auto simp del: Lnode\<^sub>i.simps split!: up\<^sub>i.split)
      next
        case Cons
        then obtain ls' lsub lsep where ls_Cons: "ls = ls'@[(lsub,lsep)]"
          by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
        then have "aligned lsep (Leaf (mxs@rxs)) rsep"
          using Leaf_merge_aligned
          using align_last aligned_split_left assms(1) t_node rs_Cons sub_node
          by (metis aligned.elims(2) aligned_split_right bplustree.distinct(1) bplustree.inject(2) inbetween.simps(2) r_split rs_Leaf)
        then have "aligned_up\<^sub>i lsep (Lnode\<^sub>i k (mxs@rxs)) rsep"
          using Lnode\<^sub>i_aligned assms(4) sorted_leaves by blast
        then show ?thesis
          using False t_node sub_node rs_Cons ls_Cons assms
          using aligned_subst_merge[of l ls' lsub lsep sub sep rsub rsep rs]
          using aligned_subst_merge_two[of l ls' lsub lsep sub sep rsub rsep rs t u]
          by (auto simp del: Lnode\<^sub>i.simps split!: up\<^sub>i.split)
      qed
    qed
  qed
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto simp add: t_node)
  show ?thesis
  proof (cases "length tts \<ge> k \<and> length mts \<ge> k")
    case True
    then show ?thesis
      using t_node sub_node assms
      by (auto simp del: bal.simps)
  next
    case False
    then show ?thesis
    proof (cases rs)
      case rs_nil: Nil
      then have sorted_leaves: "sorted_less (leaves_list mts @ leaves mt @ leaves_list tts @ leaves tt)"
        using assms(3) rs_nil t_node sub_node
        by (auto simp add: sorted_wrt_append) 
      then show ?thesis
      proof (cases ls)
        case ls_nil: Nil
        then have "aligned l (Node (mts@(mt,sep)#tts) tt) u"
          using t_node sub_node assms rs_nil False 
          by (auto simp add: Node_merge_aligned)
        then  have "aligned_up\<^sub>i l (node\<^sub>i k (mts@(mt,sep)#tts) tt) u"
          using node\<^sub>i_aligned sorted_leaves assms by blast
        then show ?thesis
          using False t_node sub_node rs_nil ls_nil
          by (auto simp del: node\<^sub>i.simps split!: up\<^sub>i.split)
      next
        case Cons
        then obtain ls' lsub lsep where ls_Cons: "ls = ls'@[(lsub,lsep)]"
          by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
        then have "aligned lsep (Node (mts@(mt,sep)#tts) tt) u"
          using t_node sub_node assms rs_nil False ls_Cons
          by (metis Node_merge_aligned align_last aligned.simps(2) aligned_split_left)
        then have "aligned_up\<^sub>i lsep (node\<^sub>i k (mts@(mt,sep)#tts) tt) u"
          using node\<^sub>i_aligned assms(4) sorted_leaves by blast
        then show ?thesis
          using False t_node sub_node rs_nil ls_Cons assms
          using aligned_subst_last_merge[of l ls' lsub lsep sub sep t u]
          using aligned_subst_last_merge_two[of l ls' lsub lsep sub sep t u]
          by (auto simp del: node\<^sub>i.simps split!: up\<^sub>i.split)
      qed
    next
      case rs_Cons: (Cons r rs)
      then obtain rsub rsep where r_split[simp]: "r = (rsub,rsep)"
        by (cases r)
      then have "height rsub \<noteq> 0"
        using assms rs_Cons t_node by auto
      then obtain rts rt where rs_Node: "rsub = Node rts rt"
        by (cases rsub) auto
      have "sorted_less (leaves sub @ leaves rsub)"
        using assms(3) rs_Cons r_split 
        by (simp add: sorted_wrt_append) 
      then have sorted_leaves: "sorted_less (leaves_list mts @ leaves mt @ leaves_list rts @ leaves rt)" 
        by (simp add: rs_Node sub_node)
      then show ?thesis
      proof (cases ls)
        case ls_nil: Nil
        then have "aligned l (Node (mts@(mt,sep)#rts) rt) rsep"
          using sub_node assms rs_Cons False rs_Node
          by (metis Node_merge_aligned aligned.simps(2) append_self_conv2 inbetween.simps(2) r_split)
        then  have "aligned_up\<^sub>i l (node\<^sub>i k (mts@(mt,sep)#rts) rt) rsep"
          using node\<^sub>i_aligned sorted_leaves assms by blast
        then show ?thesis
          using False t_node sub_node rs_Cons ls_nil assms rs_Node
          by (auto simp del: node\<^sub>i.simps split!: up\<^sub>i.split)
      next
        case Cons
        then obtain ls' lsub lsep where ls_Cons: "ls = ls'@[(lsub,lsep)]"
          by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
        then have "aligned lsep (Node (mts@(mt,sep)#rts) rt) rsep"
          using Node_merge_aligned
          using align_last aligned_split_left assms(1) t_node rs_Cons sub_node
          by (metis aligned.simps(2) aligned_split_right inbetween.simps(2) r_split rs_Node)
        then have "aligned_up\<^sub>i lsep (node\<^sub>i k (mts@(mt,sep)#rts) rt) rsep"
          using sorted_leaves node\<^sub>i_aligned assms(4) by blast
        then show ?thesis
          using False t_node sub_node rs_Cons ls_Cons assms rs_Node
          using aligned_subst_merge[of l ls' lsub lsep sub sep rsub rsep rs]
          using aligned_subst_merge_two[of l ls' lsub lsep sub sep rsub rsep rs t u]
          by (auto simp del: node\<^sub>i.simps split!: up\<^sub>i.split)
      qed
    qed
  qed
qed

lemma Node_merge_Laligned: "
    Laligned (Node mts mt) sep \<Longrightarrow>
    inbetween aligned sep tts tt u \<Longrightarrow>
    Laligned (Node (mts @ (mt, sep) # tts) tt) u"
  apply(induction mts)
  apply auto
  using Node_merge_aligned by blast

lemma Laligned_subst_last_merge: "Laligned (Node (ts'@[(sub', sep'),(sub,sep)]) t) u \<Longrightarrow> aligned sep' t' u \<Longrightarrow>
  Laligned (Node (ts'@[(sub', sep')]) t') u" 
  apply (induction ts')
  apply auto
  by (metis (no_types, opaque_lifting) Node_merge_aligned aligned.simps(2) aligned_split_left inbetween.simps(1))

lemma Laligned_subst_last_merge_two: "Laligned (Node (ts@[(sub',sep'),(sub,sep)]) t) u \<Longrightarrow> aligned sep' lt a \<Longrightarrow> aligned a rt u \<Longrightarrow> Laligned (Node (ts@[(sub',sep'),(lt,a)]) rt) u" 
  apply(induction ts)
  apply auto
  by (meson aligned.simps(2) aligned_subst_last_merge_two)

lemma Laligned_subst_merge: "Laligned (Node (ls@(lsub, lsep)#(sub,sep)#(rsub,rsep)#rs) t) u \<Longrightarrow> aligned lsep sub' rsep \<Longrightarrow>
  Laligned (Node (ls@(lsub, lsep)#(sub', rsep)#rs) t) u" 
  apply (induction ls)
  apply auto
  by (meson aligned.simps(2) aligned_subst_merge)

lemma Laligned_subst_merge_two: "Laligned (Node (ls@(lsub, lsep)#(sub,sep)#(rsub,rsep)#rs) t) u \<Longrightarrow> aligned lsep sub' a \<Longrightarrow>
  aligned a rsub' rsep \<Longrightarrow> Laligned (Node (ls@(lsub, lsep)#(sub',a)#(rsub', rsep)#rs) t) u" 
  apply(induction ls)
  apply auto
  by (meson aligned.simps(2) aligned_subst_merge_two)

lemma xs_front: "xs @ [(a,b)] = (x,y)#xs' \<Longrightarrow> xs @ [(a,b),(c,d)] = (z,zz)#xs'' \<Longrightarrow> (x,y) = (z,zz)" 
  apply(induction xs)
  apply auto
  done

lemma rebalance_middle_tree_Laligned:
  assumes "Laligned (Node (ls@(sub,sep)#rs) t) u"
    and "height t = height sub"
    and "sorted_less (leaves (Node (ls@(sub,sep)#rs) t))"
    and "k > 0"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "Laligned (rebalance_middle_tree k ls sub sep rs t) u"
proof (cases t)
  case t_node: (Leaf txs)
  then obtain mxs where sub_node: "sub = Leaf mxs"
    using assms by (cases sub) (auto simp add: t_node)
  show ?thesis
  proof (cases "length mxs \<ge> k \<and> length txs \<ge> k")
    case True
    then show ?thesis
      using t_node sub_node assms
      by auto
  next
    case False
    then show ?thesis
    proof (cases rs)
      case rs_nil: Nil
      then have sorted_leaves: "sorted_less (mxs@txs)"
        using assms(3) rs_nil t_node sub_node sorted_wrt_append
        by auto 
      then show ?thesis
      proof (cases ls)
        case ls_nil: Nil
        then have "Laligned (Leaf (mxs@txs)) u"
          using t_node sub_node assms rs_nil False
          using assms
          by auto
        then  have "Laligned_up\<^sub>i (Lnode\<^sub>i k (mxs@txs)) u"
          using Lnode\<^sub>i_Laligned sorted_leaves assms by blast
        then show ?thesis
          using False t_node sub_node rs_nil ls_nil
          by (auto simp del: Lnode\<^sub>i.simps split!: up\<^sub>i.split)
      next
        case Cons
        then obtain ls' lsub lsep where ls_Cons: "ls = ls'@[(lsub,lsep)]"
          by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
        then have "aligned lsep (Leaf (mxs@txs)) u"
          using Leaf_merge_aligned Lalign_last Laligned_split_left assms(1) rs_nil sub_node t_node
          by blast
        moreover have "sorted_less (mxs@txs)"
          using assms(3) rs_nil t_node sub_node
          by (auto simp add: sorted_wrt_append) 
        ultimately have "aligned_up\<^sub>i lsep (Lnode\<^sub>i k (mxs@txs)) u"
          using Lnode\<^sub>i_aligned assms(4) by blast
        then show ?thesis
          using False t_node sub_node rs_nil ls_Cons assms
          using Laligned_subst_last_merge[of ls' lsub lsep sub sep t u]
          using Laligned_subst_last_merge_two[of ls' lsub lsep sub sep t u]
          by (auto simp del: Lnode\<^sub>i.simps split!: up\<^sub>i.split)
      qed
    next
      case rs_Cons: (Cons r rs)
      then obtain rsub rsep where r_split[simp]: "r = (rsub,rsep)" by (cases r)
      then have "height rsub = 0"
        using \<open>\<And>thesis. (\<And>mxs. sub = Leaf mxs \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(2) assms(5) rs_Cons
        by fastforce
      then obtain rxs where rs_Leaf[simp]: "rsub = Leaf rxs"
        by (cases rsub) auto
      then have sorted_leaves: "sorted_less (mxs@rxs)"
        using assms(3) rs_Cons sub_node sorted_wrt_append r_split
        by (auto simp add: sorted_wrt_append) 
      then show ?thesis
      proof (cases ls)
        case ls_nil: Nil
        then have "Laligned (Leaf (mxs@rxs)) rsep"
          using sub_node assms rs_Cons False
          by auto
        then  have "Laligned_up\<^sub>i (Lnode\<^sub>i k (mxs@rxs)) rsep"
          using Lnode\<^sub>i_Laligned sorted_leaves assms by blast
        then show ?thesis
          using False t_node sub_node rs_Cons ls_nil assms
          by (auto simp del: Lnode\<^sub>i.simps split!: up\<^sub>i.split)
      next
        case Cons
        then obtain ls' lsub lsep where ls_Cons: "ls = ls'@[(lsub,lsep)]"
          by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
        then have "aligned lsep (Leaf (mxs@rxs)) rsep"
          using Leaf_merge_aligned
          using assms(1) t_node rs_Cons sub_node
          by (metis Lalign_last Laligned_split_left Laligned_split_right aligned.elims(2) bplustree.distinct(1) bplustree.inject(2) inbetween.simps(2) r_split rs_Leaf)
        then have "aligned_up\<^sub>i lsep (Lnode\<^sub>i k (mxs@rxs)) rsep"
          using Lnode\<^sub>i_aligned assms(4) sorted_leaves by blast
        then show ?thesis
          using False t_node sub_node rs_Cons ls_Cons assms
          using Laligned_subst_merge[of ls' lsub lsep sub sep rsub rsep rs]
          using Laligned_subst_merge_two[of ls' lsub lsep sub sep rsub rsep rs t u]
          by (auto simp del: Lnode\<^sub>i.simps split!: up\<^sub>i.split)
      qed
    qed
  qed
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto simp add: t_node)
  show ?thesis
  proof (cases "length tts \<ge> k \<and> length mts \<ge> k")
    case True
    then show ?thesis
      using t_node sub_node assms
      by (auto simp del: bal.simps)
  next
    case False
    then show ?thesis
    proof (cases rs)
      case rs_nil: Nil
      then have sorted_leaves: "sorted_less (leaves_list mts @ leaves mt @ leaves_list tts @ leaves tt)"
        using assms(3) rs_nil t_node sub_node
        by (auto simp add: sorted_wrt_append) 
      then show ?thesis
      proof (cases ls)
        case ls_nil: Nil
        then have "Laligned (Node (mts@(mt,sep)#tts) tt) u"
          using t_node sub_node assms rs_nil False 
          by (metis Lalign_last Laligned_nonempty_Node Node_merge_Laligned aligned.simps(2) append_self_conv2)
        then  have "Laligned_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt) u"
          using node\<^sub>i_Laligned sorted_leaves assms by blast
        then show ?thesis
          using False t_node sub_node rs_nil ls_nil
          by (auto simp del: node\<^sub>i.simps split!: up\<^sub>i.split)
      next
        case Cons
        then obtain ls' lsub lsep where ls_Cons: "ls = ls'@[(lsub,lsep)]"
          by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
        then have "aligned lsep (Node (mts@(mt,sep)#tts) tt) u"
          using t_node sub_node assms rs_nil False ls_Cons
          by (metis Lalign_last Laligned_split_left Node_merge_aligned aligned.simps(2))
        then have "aligned_up\<^sub>i lsep (node\<^sub>i k (mts@(mt,sep)#tts) tt) u"
          using node\<^sub>i_aligned assms(4) sorted_leaves by blast
        then show ?thesis
          using False t_node sub_node rs_nil ls_Cons assms 
          using Laligned_subst_last_merge[of ls' lsub lsep sub sep t u]
          using Laligned_subst_last_merge_two[of ls' lsub lsep sub sep t u]
          by (auto simp del: node\<^sub>i.simps bal.simps height_bplustree.simps split!: up\<^sub>i.split list.splits)
      qed
    next
      case rs_Cons: (Cons r rs)
      then obtain rsub rsep where r_split[simp]: "r = (rsub,rsep)"
        by (cases r)
      then have "height rsub \<noteq> 0"
        using assms rs_Cons t_node by auto
      then obtain rts rt where rs_Node: "rsub = Node rts rt"
        by (cases rsub) auto
      have "sorted_less (leaves sub @ leaves rsub)"
        using assms(3) rs_Cons r_split 
        by (simp add: sorted_wrt_append) 
      then have sorted_leaves: "sorted_less (leaves_list mts @ leaves mt @ leaves_list rts @ leaves rt)" 
        by (simp add: rs_Node sub_node)
      then show ?thesis
      proof (cases ls)
        case ls_nil: Nil
        then have "Laligned (Node (mts@(mt,sep)#rts) rt) rsep"
          using sub_node assms rs_Cons False rs_Node
          by (metis Laligned_nonempty_Node Node_merge_Laligned aligned.simps(2) append_self_conv2 inbetween.simps(2) r_split)
        then  have "Laligned_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt) rsep"
          using node\<^sub>i_Laligned by blast
        then show ?thesis
          using False t_node sub_node rs_Cons ls_nil assms rs_Node
          by (auto simp del: node\<^sub>i.simps split!: up\<^sub>i.split)
      next
        case Cons
        then obtain ls' lsub lsep where ls_Cons: "ls = ls'@[(lsub,lsep)]"
          by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
        then have "aligned lsep (Node (mts@(mt,sep)#rts) rt) rsep"
          using Node_merge_aligned
          using assms(1) t_node rs_Cons sub_node
          by (metis Lalign_last Laligned_split_left Laligned_split_right aligned.simps(2) inbetween.simps(2) r_split rs_Node)
        then have "aligned_up\<^sub>i lsep (node\<^sub>i k (mts@(mt,sep)#rts) rt) rsep"
          using sorted_leaves node\<^sub>i_aligned assms(4) by blast
        then show ?thesis
          using False t_node sub_node rs_Cons ls_Cons assms rs_Node
          using Laligned_subst_merge[of ls' lsub lsep sub sep rsub rsep rs]
          using Laligned_subst_merge_two[of ls' lsub lsep sub sep rsub rsep rs t u]
          by (auto simp del: node\<^sub>i.simps split!: up\<^sub>i.split)
      qed
    qed
  qed
qed

lemma rebalance_last_tree_aligned:
  assumes "aligned l (Node (ls@[(sub,sep)]) t) u"
    and "height t = height sub"
    and "sorted_less (leaves (Node (ls@[(sub,sep)]) t))"
    and "k > 0"
  shows "aligned l (rebalance_last_tree k (ls@[(sub,sep)]) t) u"
  using rebalance_middle_tree_aligned[of l ls sub sep "[]" t u k] assms
  by auto

lemma rebalance_last_tree_Laligned:
  assumes "Laligned (Node (ls@[(sub,sep)]) t) u"
    and "height t = height sub"
    and "sorted_less (leaves (Node (ls@[(sub,sep)]) t))"
    and "k > 0"
  shows "Laligned (rebalance_last_tree k (ls@[(sub,sep)]) t) u"
  using rebalance_middle_tree_Laligned[of ls sub sep "[]" t u k] assms
  by auto

lemma del_bal: 
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
  shows "bal (del k x t)"
  using assms
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls rs where list_split: "split ts x = (ls,rs)"
    by (cases "split ts x")
  then show ?case
  proof (cases rs)
    case Nil
    then have "bal (del k x t)" using 2 list_split
      by (simp add: order_impl_root_order)
    moreover have "height (del k x t) = height t"
      using 2 del_height by (simp add: order_impl_root_order)
    moreover have "ts \<noteq> []" using 2 by auto
    ultimately have "bal (rebalance_last_tree k ts (del k x t))"
      using 2 Nil rebalance_last_tree_bal
      by simp
    then have "bal (rebalance_last_tree k ls (del k x t))" 
      using list_split split_conc Nil by fastforce
    then show ?thesis
      using 2 list_split Nil
      by auto
  next
    case (Cons r rs)
    then obtain sub sep where r_split: "r = (sub,sep)" by (cases r)
    then have sub_height: "height sub = height t" "bal sub"
      using 2 Cons list_split split_set(1) by fastforce+
    then have "bal (del k x sub)" "height (del k x sub) = height sub" using sub_height
       apply (metis "2.IH"(2) "2.prems"(1) "2.prems"(2) list_split local.Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_set(1))
      by (metis "2.prems"(1) "2.prems"(2) list_split Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) del_height split_set(1) sub_height(2))
    moreover have "bal (Node (ls@(sub,sep)#rs) t)"
      using "2.prems"(3) list_split Cons r_split split_conc by blast
    ultimately have "bal (Node (ls@(del k x sub,sep)#rs) t)"
      using bal_substitute_subtree[of ls sub sep rs t "del k x sub"] by metis
    then have "bal (rebalance_middle_tree k ls (del k x sub) sep rs t)"
      using rebalance_middle_tree_bal[of ls "del k x sub" sep rs t k] by metis
    then show ?thesis
      using 2 list_split Cons r_split by auto
  qed
qed simp


lemma rebalance_middle_tree_order:
  assumes "almost_order k sub"
    and "\<forall>s \<in> set (subtrees (ls@rs)). order k s" "order k t"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
    and "length (ls@(sub,sep)#rs) \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_middle_tree k ls sub sep rs t)"
proof(cases t)
  case (Leaf txs)
  then obtain subxs where "sub = Leaf subxs"
    using height_Leaf assms by metis
  then show ?thesis
    using assms Leaf
    by (auto split!: list.splits bplustree.splits)
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto)
  then show ?thesis
  proof(cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then have "order k sub" using assms
      by (simp add: sub_node)
    then show ?thesis
      using True t_node sub_node assms by auto
  next
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      have "order_up\<^sub>i k (node\<^sub>i k (mts@(mt,sep)#tts) tt)"
        using node\<^sub>i_order[of k "mts@(mt,sep)#tts" tt] assms(1,3) t_node sub_node
        by (auto simp del: order_up\<^sub>i.simps node\<^sub>i.simps)
      then show ?thesis
        apply(cases "node\<^sub>i k (mts@(mt,sep)#tts) tt")
        using assms t_node sub_node False Nil apply (auto simp del: node\<^sub>i.simps)
        done
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split: "r = (rsub,rsep)" by (cases r)
      then have rsub_height: "height rsub = height t"
        using assms Cons by auto
      then obtain rts rt where r_node: "rsub = (Node rts rt)"
        apply(cases rsub) using t_node by simp
      have "order_up\<^sub>i k (node\<^sub>i k (mts@(mt,sep)#rts) rt)"
        using node\<^sub>i_order[of k "mts@(mt,sep)#rts" rt] assms(1,2) t_node sub_node r_node r_split Cons
        by (auto simp del: order_up\<^sub>i.simps node\<^sub>i.simps)
      then show ?thesis        
        apply(cases "node\<^sub>i k (mts@(mt,sep)#rts) rt")
        using assms t_node sub_node False Cons r_split r_node apply (auto simp del: node\<^sub>i.simps)
        done
    qed
  qed
qed

(* we have to proof the order invariant once for an underflowing last tree *)
lemma rebalance_middle_tree_last_order:
  assumes "almost_order k t"
    and  "\<forall>s \<in> set (subtrees (ls@(sub,sep)#rs)). order k s"
    and "rs = []"
    and "length (ls@(sub,sep)#rs) \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_middle_tree k ls sub sep rs t)"
proof (cases t)
  case (Leaf txs)
  then obtain subxs where "sub = Leaf subxs"
    using height_Leaf assms by metis
  then show ?thesis
    using assms Leaf
    by (auto split!: list.splits bplustree.splits)
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto)
  then show ?thesis
  proof(cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then have "order k sub" using assms
      by (simp add: sub_node)
    then show ?thesis
      using True t_node sub_node assms by auto
  next
    case False
    have "order_up\<^sub>i k (node\<^sub>i k (mts@(mt,sep)#tts) tt)"
      using node\<^sub>i_order[of k "mts@(mt,sep)#tts" tt] assms t_node sub_node
      by (auto simp del: order_up\<^sub>i.simps node\<^sub>i.simps)
    then show ?thesis
      apply(cases "node\<^sub>i k (mts@(mt,sep)#tts) tt")
      using assms t_node sub_node False Nil apply (auto simp del: node\<^sub>i.simps)
      done
  qed
qed

lemma rebalance_last_tree_order:
  assumes "ts = ls@[(sub,sep)]"
    and "\<forall>s \<in> set (subtrees (ts)). order k s" "almost_order k t"
    and "length ts \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_last_tree k ts t)"
  using rebalance_middle_tree_last_order assms by auto


lemma del_order: 
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
    and "sorted (leaves t)"
  shows "almost_order k (del k x t)"
  using assms
proof (induction k x t rule: del.induct)
  case (1 k x xs)
  then show ?case
    by auto
next
  case (2 k x ts t)
  then obtain ls list where list_split: "split ts x = (ls, list)" by (cases "split ts x")
  then show ?case
  proof (cases list)
    case Nil
    then have "almost_order k (del k x t)" using 2 list_split
      by (simp add: order_impl_root_order sorted_wrt_append)
    moreover obtain lls lsub lsep where ls_split: "ls = lls@[(lsub,lsep)]"
      using 2 Nil list_split
      by (metis append_Nil length_0_conv less_nat_zero_code old.prod.exhaust rev_exhaust root_order.simps(2) split_conc)
    moreover have "height t = height (del k x t)" using del_height 2
      by (simp add: order_impl_root_order)
    moreover have "length ls = length ts"
      using Nil list_split
      by (auto dest: split_length)
    ultimately have "almost_order k (rebalance_last_tree k ls (del k x t))"
      using rebalance_last_tree_order[of ls lls lsub lsep k "del k x t"]
      by (metis "2.prems"(2) "2.prems"(3) Un_iff append_Nil2 bal.simps(2) list_split Nil root_order.simps(2) singletonI split_conc subtrees_split)
    then show ?thesis
      using 2 list_split Nil by auto 
  next
    case (Cons r rs)

    from Cons obtain sub sep where r_split: "r = (sub,sep)" by (cases r)

    have inductive_help:
      "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t"
      "\<forall>s\<in>set (subtrees (ls @ rs)). order k s"
      "Suc (length (ls @ rs)) \<le> 2 * k"
      "order k t"
      using Cons r_split "2.prems" list_split split_set
      by (auto dest: split_conc split!: list.splits)
    then have "almost_order k (del k x sub)" using 2 list_split Cons r_split order_impl_root_order
      by (metis bal.simps(2) root_order.simps(2) some_child_sub(1) sorted_leaves_induct_subtree split_conc split_set(1))
    moreover have "height (del k x sub) = height t"
      by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) list_split Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) del_height split_set(1))
    ultimately have "almost_order k (rebalance_middle_tree k ls (del k x sub) sep rs t)"
      using rebalance_middle_tree_order[of k "del k x sub" ls rs t sep]
      using inductive_help
      using Cons r_split list_split by auto
    then show ?thesis using 2 Cons r_split list_split by auto
  qed
qed

(* sortedness of delete by inorder *)
(* generalize del_list_sorted since its cumbersome to express inorder_list ts as xs @ [a]
note that the proof scheme is almost identical to ins_list_sorted
 *)
(* TODO lift to leaves *)
thm del_list_sorted

lemma del_list_split:
  assumes "Laligned (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, rs)"
  shows "del_list x (leaves (Node ts t)) = leaves_list ls @ del_list x (leaves_list rs @ leaves t)"
proof (cases ls)
  case Nil
  then show ?thesis
    using assms by (auto dest!: split_conc)
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.distinct(1) rev_exhaust surj_pair)
  have sorted_inorder: "sorted_less (inorder (Node ts t))"
    using Laligned_sorted_inorder assms(1) sorted_cons sorted_snoc by blast
  moreover have "sep < x"
    using split_req(2)[of ts x ls' sub sep rs]
    using assms ls_tail_split sorted_inorder sorted_inorder_separators
    by blast
  moreover have leaves_split: "leaves (Node ts t) = leaves_list ls @ leaves_list rs @ leaves t"
    using assms(3) split_tree.leaves_split by blast
  then show ?thesis
  proof (cases "leaves_list ls")
    case Nil
    then show ?thesis
      by (metis append_self_conv2 leaves_split)
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
        using Laligned_split_left
        by simp
      ultimately show ?thesis
        using Laligned_leaves_inbetween[of "Node ls' sub" sep]
        by blast
    qed
  moreover have "sorted_less (leaves (Node ts t))"
    using assms sorted_wrt_append split_conc by fastforce
  ultimately show ?thesis using assms(2) split_conc[OF assms(3)] leaves_tail_split
    using del_list_sorted[of "leavesls'" l' "leaves_list rs @ leaves t" x] \<open>sep < x\<close>
    by auto
  qed
qed

corollary del_list_split_aligned:
  assumes "aligned l (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, rs)"
  shows "del_list x (leaves (Node ts t)) = leaves_list ls @ del_list x (leaves_list rs @ leaves t)"
  using aligned_imp_Laligned assms(1) assms(2) assms(3) del_list_split by blast

(* del sorted requires sortedness of the full list so we need to change the right specialization a bit *)

lemma del_list_split_right:
  assumes "Laligned (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, (sub,sep)#rs)"
  shows "del_list x (leaves_list ((sub,sep)#rs) @ leaves t) = del_list x (leaves sub) @ leaves_list rs @ leaves t"
proof -
  have sorted_inorder: "sorted_less (inorder (Node ts t))"
    using Laligned_sorted_inorder assms(1) sorted_cons sorted_snoc by blast
  from assms have "x \<le> sep"
  proof -
    from assms have "sorted_less (separators ts)"
      using sorted_inorder_separators sorted_inorder by blast
    then show ?thesis
      using split_req(3)
      using assms
      by fastforce
  qed
  then show ?thesis
  proof (cases "leaves_list rs @ leaves t")
    case Nil
    moreover have "leaves_list ((sub,sep)#rs) @ leaves t = leaves sub @ leaves_list rs @ leaves t"
      by simp
    ultimately show ?thesis 
      by (metis self_append_conv)
  next
    case (Cons r' rs')
    then have "sep < r'"
      by (metis aligned_leaves_inbetween Laligned_split_right assms(1) assms(3) leaves.simps(2) list.set_intros(1) split_set.split_conc split_set_axioms)
    then have  "x < r'"
      using \<open>x \<le> sep\<close> by auto
    moreover have "sorted_less (leaves sub @ leaves_list rs @ leaves t)"
    proof -
      have "sorted_less (leaves_list ls @ leaves sub @ leaves_list rs @ leaves t)"
        using assms
        by (auto dest!: split_conc)
      then show ?thesis
        using assms 
        by (metis Cons sorted_wrt_append)
    qed
    ultimately show ?thesis
      using del_list_sorted[of "leaves sub" r' rs'] Cons
      by auto
  qed
qed

corollary del_list_split_right_aligned:
  assumes "aligned l (Node ts t) u"
    and "sorted_less (leaves (Node ts t))"
    and "split ts x = (ls, (sub,sep)#rs)"
  shows "del_list x (leaves_list ((sub,sep)#rs) @ leaves t) = del_list x (leaves sub) @ leaves_list rs @ leaves t"
  using aligned_imp_Laligned assms(1) assms(2) assms(3) split_set.del_list_split_right split_set_axioms by blast

thm del_list_idem

lemma del_inorder:
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
    and "sorted_less (leaves t)"
    and "aligned l t u"
    and "l < x" "x \<le> u"
  shows "leaves (del k x t) = del_list x (leaves t) \<and> aligned l (del k x t) u"
  using assms
proof (induction k x t arbitrary: l u rule: del.induct)
  case (1 k x xs)
  then have "leaves (del k x (Leaf xs)) = del_list x (leaves (Leaf xs))"
    by (simp add: insert_list_req)
  moreover have "aligned l (del k x (Leaf xs)) u"
  proof -
    have "l < u"
      using "1.prems"(6) "1.prems"(7) by auto
    moreover have "\<forall>x \<in> set xs - {x}. l < x \<and> x \<le> u"
      using "1.prems"(5) by auto
    ultimately show ?thesis
      using set_del_list insert_list_req
      by (metis "1"(4) aligned.simps(1) del.simps(1) leaves.simps(1))
  qed
  ultimately show ?case
    by simp
next
  case (2 k x ts t l u)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs"
    using split_set.split_conc split_set_axioms by blast
  show ?case
  proof (cases rs)
    case Nil
    then obtain ls' lsub lsep where ls_split: "ls = ls' @ [(lsub,lsep)]"
      by (metis "2.prems"(2) append_Nil2 list.size(3) list_conc old.prod.exhaust root_order.simps(2) snoc_eq_iff_butlast zero_less_iff_neq_zero)
    then have IH: "leaves (del k x t) = del_list x (leaves t) \<and>  aligned lsep (del k x t) u"
        using "2.IH"(1)[OF list_split[symmetric] Nil, of lsep u]
        by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) "2.prems"(3) "2.prems"(4) "2.prems"(5) "2.prems"(7) \<open>ls = ls' @ [(lsub, lsep)]\<close> align_last aligned_sorted_separators bal.simps(2) list_conc list_split local.Nil order_impl_root_order root_order.simps(2) self_append_conv sorted_cons sorted_leaves_induct_last sorted_snoc split_set.split_req(2) split_set_axioms)
    have "leaves (del k x (Node ts t)) = leaves (rebalance_last_tree k ts (del k x t))"
      using list_split Nil list_conc by auto
    also have "\<dots> = leaves_list ts @ leaves (del k x t)"
    proof -
      obtain ts' sub sep where ts_split: "ts = ts' @ [(sub, sep)]"
        using \<open>ls = ls' @ [(lsub, lsep)]\<close> list_conc local.Nil by blast
      then have "height sub = height t"
        using "2.prems"(3) by auto
      moreover have "height t = height (del k x t)"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) del_height order_impl_root_order root_order.simps(2))
      ultimately show ?thesis
        using rebalance_last_tree_inorder
        using ts_split by auto
    qed
    also have "\<dots> = leaves_list ts @ del_list x (leaves t)"
      using IH by blast
    also have "\<dots> = del_list x (leaves (Node ts t))"
      by (metis "2.prems"(4) "2.prems"(5) aligned_imp_Laligned append_self_conv2 concat.simps(1) list.simps(8) list_conc list_split local.Nil self_append_conv split_set.del_list_split split_set_axioms)
    finally have 0: "leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))" .
    moreover have "aligned l (del k x (Node ts t)) u"
    proof -
      have "aligned l (Node ls (del k x t)) u"
        using IH list_conc Nil "2.prems" ls_split
        using aligned_subst_last
        by (metis self_append_conv)
      moreover have "sorted_less (leaves (Node ls (del k x t)))"
        using "2.prems"(4) \<open>leaves_list ts @ del_list x (leaves t) = del_list x (leaves (Node ts t))\<close> \<open>leaves_list ts @ leaves (del k x t) = leaves_list ts @ del_list x (leaves t)\<close> list_conc local.Nil sorted_del_list
        by auto
      ultimately have "aligned l (rebalance_last_tree k ls (del k x t)) u"
        using rebalance_last_tree_aligned
        by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) "2.prems"(3) UnCI bal.simps(2) del_height list.set_intros(1) list_conc ls_split order_impl_root_order root_order.simps(2) set_append some_child_sub(1))
      then show ?thesis using list_split ls_split "2.prems" Nil
        by simp
    qed
    ultimately show ?thesis
      by simp
  next
    case (Cons h rs)
    then obtain sub sep where h_split: "h = (sub,sep)"
      by (cases h)
    then have node_sorted_split: 
      "sorted_less (leaves (Node (ls@(sub,sep)#rs) t))"
      "root_order k (Node (ls@(sub,sep)#rs) t)"
      "bal (Node (ls@(sub,sep)#rs) t)"
      using "2.prems" h_split list_conc Cons by blast+
    {
      assume IH: "leaves (del k x sub) = del_list x (leaves sub)"
      have "leaves (del k x (Node ts t)) = leaves (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using Cons list_split h_split "2.prems"
        by auto
      also have "\<dots> = leaves (Node (ls@(del k x sub, sep)#rs) t)"
        using rebalance_middle_tree_inorder[of t "del k x sub" rs]
        by (smt (verit) "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) bal_sub_height del_height h_split list_split local.Cons node_sorted_split(3) order_impl_root_order rebalance_middle_tree_inorder root_order.simps(2) some_child_sub(1) split_set(1))
      also have "\<dots> = leaves_list ls @ leaves (del k x sub) @ leaves_list rs @ leaves t"
        by auto
      also have "\<dots> = leaves_list ls @ del_list x (leaves sub @ leaves_list rs @ leaves t)"
        using del_list_split_right_aligned[of l ts t u x ls sub sep rs]
        using list_split Cons "2.prems"(4,5) h_split IH list_conc
        by auto
      also have "\<dots> = del_list x (leaves_list ls @ leaves sub @ leaves_list rs @ leaves t)"
        using del_list_split_aligned[of l ts t u x ls "(sub,sep)#rs"]
        using list_split Cons "2.prems"(4,5) h_split IH list_conc
        by auto
      finally have "leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))"
        using list_conc Cons h_split
        by auto
    }
    then show ?thesis
    proof (cases ls)
      case Nil
      then have IH: "leaves (del k x sub) = del_list x (leaves sub) \<and> aligned l (del k x sub) sep"
        using "2.IH"(2)[OF list_split[symmetric] Cons h_split[symmetric], of l sep]
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(5) "2.prems"(6) aligned.simps(2) aligned_sorted_separators append_self_conv2 bal.simps(2) h_split inbetween.simps(2) list.set_intros(1) list_conc list_split local.Cons local.Nil node_sorted_split(1) node_sorted_split(3) order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_cons sorted_leaves_induct_subtree sorted_snoc split_set.split_req(3) split_set_axioms)
      then have "leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))"
        using \<open>leaves (del k x sub) = del_list x (leaves sub) \<Longrightarrow> leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> by blast
      then have "sorted_less (leaves (del k x (Node ts t)))"
        using "2.prems"(4) sorted_del_list by auto
      then have sorted_leaves: "sorted_less (leaves (Node (ls@(del k x sub, sep)#rs) t))"
        using list_split Cons h_split
        using rebalance_middle_tree_inorder[of t "del k x sub" rs k ls sep]
        using "2.prems"(4) "2.prems"(5) IH \<open>leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> del_list_split_aligned del_list_split_right_aligned
        by auto
      from IH have "aligned l (del k x (Node ts t)) u"
      proof -
        have "aligned l (Node (ls@(del k x sub, sep)#rs) t) u"
          using "2.prems"(5) IH h_split list_conc local.Cons local.Nil by auto
        then have "aligned l (rebalance_middle_tree k ls (del k x sub) sep rs t) u"
          using rebalance_middle_tree_aligned sorted_leaves
          by (smt (verit, best) "2.prems"(1) "2.prems"(2) "2.prems"(3) append_self_conv2 bal.simps(2) bal_sub_height del_height h_split list.set_intros(1) list_conc local.Cons local.Nil order_impl_root_order root_order.simps(2) some_child_sub(1))
        then show ?thesis
          using list_split Cons h_split
          by auto
      qed
      then show ?thesis
        using \<open>leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> by blast
    next
      case _: (Cons a list)
      then obtain ls' lsub lsep where l_split: "ls = ls'@[(lsub,lsep)]"
        by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
      then have "aligned lsep sub sep"
        using "2.prems"(5) align_last aligned_split_left h_split list_conc local.Cons
        by blast
      then have IH: "leaves (del k x sub) = del_list x (leaves sub) \<and> aligned lsep (del k x sub) sep"
        using "2.IH"(2)[OF list_split[symmetric] Cons h_split[symmetric], of lsep sep]
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(5) aligned_sorted_separators bal.simps(2) bal_split_left(1) h_split l_split list_split local.Cons node_sorted_split(1) node_sorted_split(3) order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_cons sorted_leaves_induct_subtree sorted_snoc split_set.split_req(2) split_set.split_req(3) split_set_axioms split_set(1))
      then have "leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))"
        using \<open>leaves (del k x sub) = del_list x (leaves sub) \<Longrightarrow> leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> by blast
      then have "sorted_less (leaves (del k x (Node ts t)))"
        using "2.prems"(4) sorted_del_list by auto
      then have sorted_leaves: "sorted_less (leaves (Node (ls@(del k x sub, sep)#rs) t))"
        using list_split Cons h_split
        using rebalance_middle_tree_inorder[of t "del k x sub" rs k ls sep]
        using "2.prems"(4) "2.prems"(5) IH \<open>leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> del_list_split_aligned del_list_split_right_aligned
        by auto
      from IH have "aligned l (del k x (Node ts t)) u"
      proof -
        have "aligned l (Node (ls@(del k x sub, sep)#rs) t) u"
          using "2.prems"(5) IH h_split list_conc local.Cons l_split
          using aligned_subst by fastforce
        then have "aligned l (rebalance_middle_tree k ls (del k x sub) sep rs t) u"
          using rebalance_middle_tree_aligned sorted_leaves
          by (smt (verit, best) "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) bal_sub_height del_height h_split list_split local.Cons node_sorted_split(3) order_impl_root_order root_order.simps(2) some_child_sub(1) split_set(1))
        then show ?thesis
          using list_split Cons h_split
          by auto
      qed
      then show ?thesis
        using \<open>leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> by blast
    qed
  qed
qed

lemma del_Linorder:
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
    and "sorted_less (leaves t)"
    and "Laligned t u"
    and "x \<le> u"
  shows "leaves (del k x t) = del_list x (leaves t) \<and> Laligned (del k x t) u"
  using assms
proof (induction k x t arbitrary: u rule: del.induct)
  case (1 k x xs)
  then have "leaves (del k x (Leaf xs)) = del_list x (leaves (Leaf xs))"
    by (simp add: insert_list_req)
  moreover have "Laligned (del k x (Leaf xs)) u"
  proof -
    have "\<forall>x \<in> set xs - {x}. x \<le> u"
      using "1.prems"(5) by auto
    then show ?thesis
      using set_del_list insert_list_req
      by (metis "1"(4) Laligned.simps(1) del.simps(1) leaves.simps(1))
  qed
  ultimately show ?case
    by simp
next
  case (2 k x ts t u)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs"
    using split_set.split_conc split_set_axioms by blast
  show ?case
  proof (cases rs)
    case Nil
    then obtain ls' lsub lsep where ls_split: "ls = ls' @ [(lsub,lsep)]"
      by (metis "2.prems"(2) append_Nil2 list.size(3) list_conc old.prod.exhaust root_order.simps(2) snoc_eq_iff_butlast zero_less_iff_neq_zero)
    then have IH: "leaves (del k x t) = del_list x (leaves t) \<and>  aligned lsep (del k x t) u"
        by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) "2.prems"(3) "2.prems"(4) "2.prems"(5) "2.prems"(6) Lalign_last Laligned_sorted_separators bal.simps(2) del_inorder list_conc list_split local.Nil order_impl_root_order root_order.simps(2) self_append_conv sorted_leaves_induct_last sorted_snoc split_set.split_req(2) split_set_axioms)
    have "leaves (del k x (Node ts t)) = leaves (rebalance_last_tree k ts (del k x t))"
      using list_split Nil list_conc by auto
    also have "\<dots> = leaves_list ts @ leaves (del k x t)"
    proof -
      obtain ts' sub sep where ts_split: "ts = ts' @ [(sub, sep)]"
        using \<open>ls = ls' @ [(lsub, lsep)]\<close> list_conc local.Nil by blast
      then have "height sub = height t"
        using "2.prems"(3) by auto
      moreover have "height t = height (del k x t)"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) del_height order_impl_root_order root_order.simps(2))
      ultimately show ?thesis
        using rebalance_last_tree_inorder
        using ts_split by auto
    qed
    also have "\<dots> = leaves_list ts @ del_list x (leaves t)"
      using IH by blast
    also have "\<dots> = del_list x (leaves (Node ts t))"
      by (metis "2.prems"(4) "2.prems"(5) append_self_conv2 concat.simps(1) list.simps(8) list_conc list_split local.Nil self_append_conv split_set.del_list_split split_set_axioms)
    finally have 0: "leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))" .
    moreover have "Laligned (del k x (Node ts t)) u"
    proof -
      have "Laligned (Node ls (del k x t)) u"
        using IH list_conc Nil "2.prems" ls_split
        by (metis Laligned_subst_last self_append_conv)
      moreover have "sorted_less (leaves (Node ls (del k x t)))"
        using "2.prems"(4) \<open>leaves_list ts @ del_list x (leaves t) = del_list x (leaves (Node ts t))\<close> \<open>leaves_list ts @ leaves (del k x t) = leaves_list ts @ del_list x (leaves t)\<close> list_conc local.Nil sorted_del_list
        by auto
      ultimately have "Laligned (rebalance_last_tree k ls (del k x t)) u"
        using rebalance_last_tree_Laligned
        by (metis (no_types, lifting) "2.prems"(1) "2.prems"(2) "2.prems"(3) UnCI bal.simps(2) del_height list.set_intros(1) list_conc ls_split order_impl_root_order root_order.simps(2) set_append some_child_sub(1))
      then show ?thesis using list_split ls_split "2.prems" Nil
        by simp
    qed
    ultimately show ?thesis
      by simp
  next
    case (Cons h rs)
    then obtain sub sep where h_split: "h = (sub,sep)"
      by (cases h)
    then have node_sorted_split: 
      "sorted_less (leaves (Node (ls@(sub,sep)#rs) t))"
      "root_order k (Node (ls@(sub,sep)#rs) t)"
      "bal (Node (ls@(sub,sep)#rs) t)"
      using "2.prems" h_split list_conc Cons by blast+
    {
      assume IH: "leaves (del k x sub) = del_list x (leaves sub)"
      have "leaves (del k x (Node ts t)) = leaves (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using Cons list_split h_split "2.prems"
        by auto
      also have "\<dots> = leaves (Node (ls@(del k x sub, sep)#rs) t)"
        using rebalance_middle_tree_inorder[of t "del k x sub" rs]
        by (smt (verit) "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) bal_sub_height del_height h_split list_split local.Cons node_sorted_split(3) order_impl_root_order rebalance_middle_tree_inorder root_order.simps(2) some_child_sub(1) split_set(1))
      also have "\<dots> = leaves_list ls @ leaves (del k x sub) @ leaves_list rs @ leaves t"
        by auto
      also have "\<dots> = leaves_list ls @ del_list x (leaves sub @ leaves_list rs @ leaves t)"
        using del_list_split_right[of ts t u x ls sub sep rs]
        using list_split Cons "2.prems"(4,5) h_split IH list_conc
        by auto
      also have "\<dots> = del_list x (leaves_list ls @ leaves sub @ leaves_list rs @ leaves t)"
        using del_list_split[of ts t u x ls "(sub,sep)#rs"]
        using list_split Cons "2.prems"(4,5) h_split IH list_conc
        by auto
      finally have "leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))"
        using list_conc Cons h_split
        by auto
    }
    then show ?thesis
    proof (cases ls)
      case Nil
      then have IH: "leaves (del k x sub) = del_list x (leaves sub) \<and> Laligned (del k x sub) sep"
        by (smt (verit, ccfv_threshold) "2.IH"(2) "2.prems"(1) "2.prems"(2) "2.prems"(5) Laligned_nonempty_Node Laligned_sorted_separators append_self_conv2 bal.simps(2) h_split list.set_intros(1) list_conc list_split local.Cons node_sorted_split(1) node_sorted_split(3) order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_leaves_induct_subtree sorted_wrt_append split_set.split_req(3) split_set_axioms)
      then have "leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))"
        using \<open>leaves (del k x sub) = del_list x (leaves sub) \<Longrightarrow> leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> by blast
      then have "sorted_less (leaves (del k x (Node ts t)))"
        using "2.prems"(4) sorted_del_list by auto
      then have sorted_leaves: "sorted_less (leaves (Node (ls@(del k x sub, sep)#rs) t))"
        using list_split Cons h_split
        using rebalance_middle_tree_inorder[of t "del k x sub" rs k ls sep]
        using "2.prems"(4) "2.prems"(5) IH \<open>leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> del_list_split del_list_split_right
        by auto
      from IH have "Laligned (del k x (Node ts t)) u"
      proof -
        have "Laligned (Node (ls@(del k x sub, sep)#rs) t) u"
          using "2.prems"(5) IH h_split list_conc local.Cons local.Nil by auto
        then have "Laligned (rebalance_middle_tree k ls (del k x sub) sep rs t) u"
          using rebalance_middle_tree_Laligned sorted_leaves
          by (smt (verit, best) "2.prems"(1) "2.prems"(2) "2.prems"(3) append_self_conv2 bal.simps(2) bal_sub_height del_height h_split list.set_intros(1) list_conc local.Cons local.Nil order_impl_root_order root_order.simps(2) some_child_sub(1))
        then show ?thesis
          using list_split Cons h_split
          by auto
      qed
      then show ?thesis
        using \<open>leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> by blast
    next
      case _: (Cons a list)
      then obtain ls' lsub lsep where l_split: "ls = ls'@[(lsub,lsep)]"
        by (metis list.discI old.prod.exhaust snoc_eq_iff_butlast)
      then have "aligned lsep sub sep"
        using "2.prems"(5) Lalign_last Laligned_split_left h_split list_conc local.Cons by blast
      then have IH: "leaves (del k x sub) = del_list x (leaves sub) \<and> aligned lsep (del k x sub) sep"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(5) Laligned_sorted_separators bal.simps(2) bal_split_left(1) del_inorder h_split l_split list_split local.Cons node_sorted_split(1) node_sorted_split(3) order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_leaves_induct_subtree sorted_snoc split_set.split_req(2) split_set.split_req(3) split_set_axioms split_set(1))
      then have "leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))"
        using \<open>leaves (del k x sub) = del_list x (leaves sub) \<Longrightarrow> leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> by blast
      then have "sorted_less (leaves (del k x (Node ts t)))"
        using "2.prems"(4) sorted_del_list by auto
      then have sorted_leaves: "sorted_less (leaves (Node (ls@(del k x sub, sep)#rs) t))"
        using list_split Cons h_split
        using rebalance_middle_tree_inorder[of t "del k x sub" rs k ls sep]
        using "2.prems"(4) "2.prems"(5) IH \<open>leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> del_list_split del_list_split_right
        by auto
      from IH have "Laligned (del k x (Node ts t)) u"
      proof -
        have "Laligned (Node (ls@(del k x sub, sep)#rs) t) u"
          using "2.prems"(5) IH h_split list_conc local.Cons l_split
          using Laligned_subst by fastforce
        then have "Laligned (rebalance_middle_tree k ls (del k x sub) sep rs t) u"
          using rebalance_middle_tree_Laligned sorted_leaves
          by (smt (verit, best) "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) bal_sub_height del_height h_split list_split local.Cons node_sorted_split(3) order_impl_root_order root_order.simps(2) some_child_sub(1) split_set(1))
        then show ?thesis
          using list_split Cons h_split
          by auto
      qed
      then show ?thesis
        using \<open>leaves (del k x (Node ts t)) = del_list x (leaves (Node ts t))\<close> by blast
    qed
  qed
qed

lemma reduce_root_order: "\<lbrakk>k > 0; almost_order k t\<rbrakk> \<Longrightarrow> root_order k (reduce_root t)"
  apply(cases t)
   apply(auto split!: list.splits simp add: order_impl_root_order)
  done

lemma reduce_root_bal: "bal (reduce_root t) = bal t"
  apply(cases t)
   apply(auto split!: list.splits)
  done


lemma reduce_root_inorder: "leaves (reduce_root t) = leaves t"
  apply (cases t)
   apply (auto split!: list.splits)
  done

lemma reduce_root_Laligned: "Laligned (reduce_root t) u = Laligned t u"
  apply(cases t)
  apply (auto split!: list.splits)
  done

lemma delete_order: "\<lbrakk>k > 0; bal t; root_order k t; sorted_less (leaves t)\<rbrakk> \<Longrightarrow>
    root_order k (delete k x t)"
  using del_order
  by (simp add: reduce_root_order)

lemma delete_bal: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> bal (delete k x t)"
  using del_bal
  by (simp add: reduce_root_bal)


lemma delete_Linorder:
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "Laligned t u" "bal t" "x \<le> u"
  shows "leaves (delete k x t) = del_list x (leaves t)"
    and "Laligned (delete k x t) u"
  using reduce_root_Laligned[of "del k x t" u] reduce_root_inorder[of "del k x t"]
  using del_Linorder[of k t u x]
  using assms
  by simp_all

corollary delete_Linorder_top:
  assumes "k > 0" "root_order k t" "sorted_less (leaves t)" "Laligned t top" "bal t"
  shows "leaves (delete k x t) = del_list x (leaves t)"
    and "Laligned (delete k x t) top"
  using assms delete_Linorder top_greatest
  by simp_all

(* TODO (opt) runtime wrt runtime of split *)

(* we are interested in a) number of comparisons b) number of fetches c) number of writes *)
(* a) is dependent on t_split, the remainder is not (we assume the number of fetches and writes
for split fun is 0 *)


(* TODO simpler induction schemes /less boilerplate isabelle/src/HOL/ex/Induction_Schema *)

subsection "Set specification by inorder"

fun invar_leaves where "invar_leaves k t = ( 
  bal t \<and>
  root_order k t \<and>
  Laligned t top
)"

interpretation S_ordered: Set_by_Ordered where
  empty = empty_bplustree and
  insert = "insert (Suc k)" and 
  delete = "delete (Suc k)" and
  isin = "isin" and
  inorder = "leaves"   and
  inv = "invar_leaves (Suc k)"
proof (standard, goal_cases)
  case (2 s x)
  then show ?case
    using isin_set_Linorder_top
    by simp
next
  case (3 s x)
  then show ?case
    using insert_Linorder_top
    by simp
next
  case (4 s x)
  then show ?case using delete_Linorder_top
    by auto
next
  case (6 s x)
  then show ?case using insert_order insert_bal insert_Linorder_top
    by auto
next
  case (7 s x)
  then show ?case using delete_order delete_bal delete_Linorder_top
    by auto
qed (simp add: empty_bplustree_def)+


(* if we remove this, it is not possible to remove the simp rules in subsequent contexts... *)
declare node\<^sub>i.simps[simp del]

end

  (* copied from comment in List_Ins_Del *)
lemma sorted_ConsD: "sorted_less (y # xs) \<Longrightarrow> x \<le> y \<Longrightarrow> x \<notin> set xs"
  by (auto simp: sorted_Cons_iff)

lemma sorted_snocD: "sorted_less (xs @ [y]) \<Longrightarrow> y \<le> x \<Longrightarrow> x \<notin> set xs"
  by (auto simp: sorted_snoc_iff)


lemmas isin_simps2 = sorted_lems sorted_ConsD sorted_snocD
  (*-----------------------------*)

lemma isin_sorted: "sorted_less (xs@a#ys) \<Longrightarrow>
  (x \<in> set (xs@a#ys)) = (if x < a then x \<in> set xs else x \<in> set (a#ys))"
  by (auto simp: isin_simps2)

context split_list
begin

fun isin_list :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "isin_list x ks = (case split_list ks x of 
    (ls,Nil) \<Rightarrow> False |
    (ls,sep#rs) \<Rightarrow> sep = x
)"

fun insert_list where
  "insert_list x ks = (case split_list ks x of 
    (ls,Nil) \<Rightarrow> ls@[x] |
    (ls,sep#rs) \<Rightarrow> if sep = x then ks else ls@x#sep#rs
)"

fun delete_list where
  "delete_list x ks = (case split_list ks x of 
    (ls,Nil) \<Rightarrow> ks |
    (ls,sep#rs) \<Rightarrow> if sep = x then ls@rs else ks
)"

lemmas split_list_conc = split_list_req(1)
lemmas split_list_sorted = split_list_req(2,3)


(* lift to split *)

lemma isin_sorted_split_list:
assumes "sorted_less xs"
    and "split_list xs x = (ls, rs)"
  shows "(x \<in> set xs) = (x \<in> set rs)"
proof (cases ls)
  case Nil
  then have "xs = rs"
    using assms by (auto dest!: split_list_conc)
  then show ?thesis by simp
next
  case Cons
  then obtain ls' sep where ls_tail_split: "ls = ls' @ [sep]"
    by (metis list.simps(3) rev_exhaust)
  then have x_sm_sep: "sep < x"
    using split_list_req(2)[of xs x ls' sep rs]
    using assms sorted_cons sorted_snoc 
    by blast
  moreover have "xs = ls@rs"
    using assms split_list_conc by simp
  ultimately show ?thesis
    using isin_sorted[of ls' sep rs]
    using assms ls_tail_split
    by auto
qed

lemma isin_sorted_split_list_right:
  assumes "split_list ts x = (ls, sep#rs)"
    and "sorted_less ts"
  shows "x \<in> set (sep#rs) = (x = sep)"
proof (cases rs)
  case Nil
  then show ?thesis
    by simp
next
  case (Cons sep' rs)
  from assms have "x < sep'"
    by (metis le_less less_trans list.set_intros(1) local.Cons sorted_Cons_iff sorted_wrt_append split_list_conc split_list_sorted(2))
  moreover have "ts = ls@sep#sep'#rs"
    using split_list_conc[OF assms(1)] Cons by auto
  moreover have "sorted_less (sep#sep'#rs)" 
    using Cons assms calculation(2) sorted_wrt_append by blast
  ultimately show ?thesis
    using isin_sorted[of "[sep]" sep' rs x] Cons
    by simp
qed


theorem isin_list_set: 
  assumes "sorted_less xs"
  shows "isin_list x xs = (x \<in> set xs)"
  using assms
  using isin_sorted_split_list[of xs x]
  using isin_sorted_split_list_right[of xs x]
  by (auto split!: list.splits)

lemma insert_sorted_split_list:
assumes "sorted_less xs"
    and "split_list xs x = (ls, rs)"
  shows "ins_list x xs = ls @ ins_list x rs"
proof (cases ls)
  case Nil
  then have "xs = rs"
    using assms by (auto dest!: split_list_conc)
  then show ?thesis 
    using Nil by simp
next
  case Cons
  then obtain ls' sep where ls_tail_split: "ls = ls' @ [sep]"
    by (metis list.simps(3) rev_exhaust)
  then have x_sm_sep: "sep < x"
    using split_list_req(2)[of xs x ls' sep rs]
    using assms sorted_cons sorted_snoc 
    by blast
  moreover have "xs = ls@rs"
    using assms split_list_conc by simp
  ultimately show ?thesis
    using ins_list_sorted[of ls' sep x rs]
    using assms ls_tail_split sorted_wrt_append[of "(<)" ls rs]
    by auto
qed

lemma insert_sorted_split_list_right:
  assumes "split_list ts x = (ls, sep#rs)"
    and "sorted_less ts"
    and "x \<noteq> sep"
  shows "ins_list x (sep#rs) = (x#sep#rs)"
proof -
  have "x < sep"
    by (meson assms(1) assms(2) assms(3) le_neq_trans split_list_sorted(2))
  then show ?thesis
    using ins_list_sorted[of "[]" sep]
    using assms
    by auto
qed


theorem insert_list_set: 
  assumes "sorted_less xs"
  shows "insert_list x xs = ins_list x xs"
  using assms split_list_conc
  using insert_sorted_split_list[of xs x]
  using insert_sorted_split_list_right[of xs x]
  by (auto split!: list.splits prod.splits)

lemma delete_sorted_split_list:
assumes "sorted_less xs"
    and "split_list xs x = (ls, rs)"
  shows "del_list x xs = ls @ del_list x rs"
proof (cases ls)
  case Nil
  then have "xs = rs"
    using assms by (auto dest!: split_list_conc)
  then show ?thesis 
    using Nil by simp
next
  case Cons
  then obtain ls' sep where ls_tail_split: "ls = ls' @ [sep]"
    by (metis list.simps(3) rev_exhaust)
  then have x_sm_sep: "sep < x"
    using split_list_req(2)[of xs x ls' sep rs]
    using assms sorted_cons sorted_snoc 
    by blast
  moreover have "xs = ls@rs"
    using assms split_list_conc by simp
  ultimately show ?thesis
    using del_list_sorted[of ls' sep rs]
    using assms ls_tail_split sorted_wrt_append[of "(<)" ls rs]
    by auto
qed

lemma delete_sorted_split_list_right:
  assumes "split_list ts x = (ls, sep#rs)"
    and "sorted_less ts"
    and "x \<noteq> sep"
  shows "del_list x (sep#rs) = sep#rs"
proof -
  have "sorted_less (sep#rs)"
    by (metis assms(1) assms(2) sorted_wrt_append split_list.split_list_conc split_list_axioms)
  moreover have "x < sep"
    by (meson assms(1) assms(2) assms(3) le_neq_trans split_list_sorted(2))
  ultimately show ?thesis
    using del_list_sorted[of "[]" sep rs x]
    by simp
qed


theorem delete_list_set: 
  assumes "sorted_less xs"
  shows "delete_list x xs = del_list x xs"
  using assms split_list_conc[of xs x]
  using delete_sorted_split_list[of xs x]
  using delete_sorted_split_list_right[of xs x]
  by (auto split!: list.splits prod.splits)

end

context split_full
begin

sublocale split_set split isin_list insert_list delete_list 
  using isin_list_set insert_list_set delete_list_set
  by unfold_locales auto

end


end
