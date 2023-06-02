section \<open>Enumeration of Rooted Trees\<close>

theory Rooted_Tree_Enumeration
  imports Rooted_Tree
begin

text \<open>Algorithm inspired by works of Beyer and Hedetniemi~\cite{beyer}, performing the same
  operations but directly on a recursive tree data structure instead of level sequences.\<close>

definition n_rtree_graphs :: "nat \<Rightarrow> nat rpregraph set" where
  "n_rtree_graphs n = {(V,E,r). rtree V E r \<and> card V = n}"

text \<open>Recursive definition on the tree structure without using level sequences\<close>

fun trim_tree :: "nat \<Rightarrow> tree \<Rightarrow> nat \<times> tree" where
  "trim_tree 0 t = (0, t)"
| "trim_tree (Suc 0) t = (0, Node [])"
| "trim_tree (Suc n) (Node []) = (n, Node [])"
| "trim_tree n (Node (t#ts)) =
  (case trim_tree n (Node ts) of
    (0, t') \<Rightarrow> (0, t') |
    (n1, Node ts') \<Rightarrow>
      let (n2, t') = trim_tree n1 t
      in (n2, Node (t'#ts')))"

lemma fst_trim_tree_lt[termination_simp]: "n \<noteq> 0 \<Longrightarrow> fst (trim_tree n t) < n"
  by (induction n t rule: trim_tree.induct, auto split: prod.split nat.split tree.split, fastforce)

fun fill_tree :: "nat \<Rightarrow> tree \<Rightarrow> tree list" where
  "fill_tree 0 _ = []"
| "fill_tree n t =
    (let (n', t') = trim_tree n t
    in fill_tree n' t' @ [t'])"

fun next_tree_aux :: "nat \<Rightarrow> tree \<Rightarrow> tree option" where
  "next_tree_aux n (Node []) = None"
| "next_tree_aux n (Node (Node [] # ts)) = next_tree_aux (Suc n) (Node ts)"
| "next_tree_aux n (Node (Node (Node [] # rs) # ts)) = Some (Node (fill_tree (Suc n) (Node rs) @ (Node rs) # ts))"
| "next_tree_aux n (Node (t # ts)) = Some (Node (the (next_tree_aux n t) # ts))"

fun next_tree :: "tree \<Rightarrow> tree option" where
  "next_tree t = next_tree_aux 0 t"


lemma next_tree_aux_None_iff: "next_tree_aux n t = None \<longleftrightarrow> height t < 2"
proof (induction n t rule: next_tree_aux.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 n ts)
  then show ?case by (cases ts) auto
next
  case (3 n rs ts)
  then show ?case by (auto simp: Max_gr_iff)
next
  case (4 n vc vd vb ts)
  then show ?case 
    by (metis One_nat_def Suc_n_not_le_n dual_order.trans height_Node_cons le_add1 less_2_cases
        next_tree_aux.simps(4) option.simps(3) plus_1_eq_Suc)
qed

lemma next_tree_Some_iff: "(\<exists>t'. next_tree t = Some t') \<longleftrightarrow> height t \<ge> 2"
  using next_tree_aux_None_iff by (metis linorder_not_less next_tree.simps not_Some_eq)

subsection \<open>Enumeration is monotonically decreasing\<close>

lemma trim_id: "trim_tree n t = (Suc n', t') \<Longrightarrow> t = t'"
  by (induction n t arbitrary: n' t' rule: trim_tree.induct) (auto split: prod.splits nat.splits tree.splits)

lemma trim_tree_le: "(n', t') = trim_tree n t \<Longrightarrow> t' \<le> t"
  using trim_id by (induction n t arbitrary: n' t' rule: trim_tree.induct)
    (auto split: prod.splits tree.splits nat.splits simp: order_less_imp_le tree_less_cons', fastforce)

lemma fill_tree_le: "r \<in> set (fill_tree n t) \<Longrightarrow> r \<le> t"
  using trim_tree_le by (induction n t rule: fill_tree.induct) (auto, fastforce)

lemma next_tree_aux_lt: "height t \<ge> 2 \<Longrightarrow> the (next_tree_aux n t) < t"
proof (induction n t rule: next_tree_aux.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 n ts)
  then show ?case using tree_less_cons' by (cases ts) auto
next
  case (3 n rs ts)
  then show ?case using tree_less_comm_suffix2 tree_less_cons by simp
next
  case (4 n vc vd vb ts)
  have "height (Node (Node (vc # vd) # vb)) \<ge> 2" unfolding numeral_2_eq_2
    by (metis dual_order.antisym height_Node_cons less_eq_nat.simps(1) not_less_eq_eq)
  then show ?case using 4 tree_less_cons2 by simp
qed

lemma next_tree_lt: "height t \<ge> 2 \<Longrightarrow> the (next_tree t) < t"
  using next_tree_aux_lt by simp

lemma next_tree_lt': "next_tree t = Some t' \<Longrightarrow> t' < t"
  using next_tree_lt next_tree_Some_iff by fastforce

subsection \<open>Size preservation\<close>

lemma size_trim_tree: "n \<noteq> 0 \<Longrightarrow> trim_tree n t = (n', t') \<Longrightarrow> n' + tree_size t' = n"
  by (induction n t arbitrary: n' t' rule: trim_tree.induct) (auto split: prod.splits nat.splits tree.splits)

lemma size_fill_tree: "sum_list (map tree_size (fill_tree n t)) = n"
  using size_trim_tree by (induction n t rule: fill_tree.induct) (auto split: prod.split)

lemma size_next_tree_aux: "height t \<ge> 2 \<Longrightarrow> tree_size (the (next_tree_aux n t)) = tree_size t + n"
proof (induction n t rule: next_tree_aux.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 n ts)
  then show ?case by (cases ts) auto
next
  case (3 n rs ts)
  then show ?case using size_fill_tree by (auto simp del: fill_tree.simps)
next
  case (4 n vc vd vb ts)
  have height_t: "height (Node (Node (vc # vd) # vb)) \<ge> 2" unfolding numeral_2_eq_2
    by (metis dual_order.antisym height_Node_cons less_eq_nat.simps(1) not_less_eq_eq)
  then show ?case using 4 by auto
qed

lemma size_next_tree: "height t \<ge> 2 \<Longrightarrow> tree_size (the (next_tree t)) = tree_size t"
  using size_next_tree_aux by simp

lemma size_next_tree': "next_tree t = Some t' \<Longrightarrow> tree_size t' = tree_size t"
  using size_next_tree next_tree_Some_iff by fastforce

subsection \<open>Setup for termination proof\<close>

definition "lt_n_trees n \<equiv> {t. tree_size t \<le> n}"

lemma n_trees_eq: "n_trees n = Node ` {ts. tree_size (Node ts) = n}"
proof-
  have "n_trees n = {Node ts | ts. tree_size (Node ts) = n}" unfolding n_trees_def by (metis tree_size.cases)
  then show ?thesis by blast
qed

lemma lt_n_trees_eq: "lt_n_trees (Suc n) = Node ` {ts. tree_size (Node ts) \<le> Suc n}"
proof-
  have "lt_n_trees (Suc n) = {Node ts | ts. tree_size (Node ts) \<le> Suc n}" unfolding lt_n_trees_def by (metis tree_size.cases)
  then show ?thesis by blast
qed

lemma finite_lt_n_trees: "finite (lt_n_trees n)"
proof (induction n)
  case 0
  then show ?case unfolding lt_n_trees_def using not_finite_existsD not_less_eq_eq tree_size_ge_1 by auto
next
  case (Suc n)
  have "\<forall>ts\<in>{ts. tree_size (Node ts) \<le> Suc n}. set ts \<subseteq> lt_n_trees n" unfolding lt_n_trees_def using tree_size_children by fastforce

  have "{ts. tree_size (Node ts) \<le> Suc n} = {ts. tree_size (Node ts) \<le> Suc n \<and> set ts \<subseteq> lt_n_trees n \<and> length ts \<le> n}" unfolding lt_n_trees_def using tree_size_children length_children by fastforce
  then have "finite {ts. tree_size (Node ts) \<le> Suc n}" using finite_lists_length_le[OF Suc.IH] by auto
  then show ?case unfolding lt_n_trees_eq by blast
qed

lemma n_trees_subset_lt_n_trees: "n_trees n \<subseteq> lt_n_trees n"
  unfolding n_trees_def lt_n_trees_def by blast

lemma finite_n_trees: "finite (n_trees n)"
  using n_trees_subset_lt_n_trees finite_lt_n_trees rev_finite_subset by metis

subsection \<open>Algorithms for enumeration\<close>

fun greatest_tree :: "nat \<Rightarrow> tree" where
  "greatest_tree (Suc 0) = Node []"
| "greatest_tree (Suc n) = Node [greatest_tree n]"

function n_tree_enum_aux :: "tree \<Rightarrow> tree list" where
  "n_tree_enum_aux t =
    (case next_tree t of None \<Rightarrow> [t] | Some t' \<Rightarrow> t # n_tree_enum_aux t')"
  by pat_completeness auto

fun n_tree_enum :: "nat \<Rightarrow> tree list" where
  "n_tree_enum 0 = []"
| "n_tree_enum n = n_tree_enum_aux (greatest_tree n)"

termination n_tree_enum_aux
proof (relation "measure (\<lambda>t. card {r. r < t \<and> tree_size r = tree_size t})", auto)
  fix t t' assume t_t': "next_tree_aux 0 t = Some t'"
  then have height_t: "height t \<ge> 2" using next_tree_Some_iff by auto
  then have "t' < t" using t_t' next_tree_lt by fastforce
  have size_t'_t: "tree_size t' = tree_size t" using size_next_tree height_t t_t' by fastforce
  let ?meas_t' = "{r. r < t' \<and> tree_size r = tree_size t'}"
  let ?meas_t = "{r. r < t \<and> tree_size r = tree_size t}"
  have fin: "finite ?meas_t" using finite_n_trees unfolding n_trees_def by auto
  have "?meas_t' \<subseteq> ?meas_t" using \<open>t' < t\<close> size_t'_t by auto
  then show "card {r. r < t' \<and> tree_size r = tree_size t'} < card {r. r < t \<and> tree_size r = tree_size t}"
    using fin \<open>t' < t\<close> psubset_card_mono size_t'_t by auto
qed

definition n_rtree_graph_enum :: "nat \<Rightarrow> nat rpregraph list" where
  "n_rtree_graph_enum n = map tree_graph (n_tree_enum n)"

subsection \<open>Regularity\<close>

lemma regular_trim_tree: "regular t \<Longrightarrow> regular (snd (trim_tree n t))" 
  by (induction n t rule: trim_tree.induct, auto split: prod.split nat.split tree.split,
      metis dual_order.trans tree.inject trim_id trim_tree_le)

lemma regular_trim_tree': "regular t \<Longrightarrow> (n', t') = trim_tree n t \<Longrightarrow> regular t'"
  using regular_trim_tree by (metis snd_eqD)

lemma sorted_fill_tree: "sorted (fill_tree n t)"
  using fill_tree_le by (induction n t rule: fill_tree.induct) (auto simp: sorted_append split: prod.split)

lemma regular_fill_tree: "regular t \<Longrightarrow> r \<in> set (fill_tree n t) \<Longrightarrow> regular r"
  using regular_trim_tree' by (induction n t rule: fill_tree.induct) auto

lemma regular_next_tree_aux: "regular t \<Longrightarrow> height t \<ge> 2 \<Longrightarrow> regular (the (next_tree_aux n t))"
proof (induction n t rule: next_tree_aux.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 n ts)
  then show ?case by (cases ts) auto
next
  case (3 n rs ts)
  then have regular_rs: "regular (Node rs)" by simp
  have "\<forall>t \<in> set ts. Node (rs) < t" using 3(1) tree_less_cons[of rs "Node []"] by auto
  then show ?case using 3 sorted_fill_tree regular_fill_tree[OF regular_rs] fill_tree_le
    by (auto simp del: fill_tree.simps simp: sorted_append, meson dual_order.trans tree_le_cons)
next
  case (4 n vc vd vb ts)
  have height_t: "height (Node (Node (vc # vd) # vb)) \<ge> 2" unfolding numeral_2_eq_2
    by (metis dual_order.antisym height_Node_cons less_eq_nat.simps(1) not_less_eq_eq)
  then show ?case using 4 by (auto, meson height_t dual_order.strict_trans1 next_tree_aux_lt nless_le)
qed

lemma regular_next_tree: "regular t \<Longrightarrow> height t \<ge> 2 \<Longrightarrow> regular (the (next_tree t))"
  using regular_next_tree_aux by simp

lemma regular_next_tree': "regular t \<Longrightarrow> next_tree t = Some t' \<Longrightarrow> regular t'"
  using regular_next_tree next_tree_Some_iff by fastforce

lemma regular_n_tree_enum_aux: "regular t \<Longrightarrow> r \<in> set (n_tree_enum_aux t) \<Longrightarrow> regular r"
proof (induction t rule: n_tree_enum_aux.induct)
  case (1 t)
  then show ?case
  proof (cases "next_tree_aux 0 t")
    case None
    then show ?thesis using 1 by auto
  next
    case (Some a)
    then show ?thesis using 1 regular_next_tree' by auto
  qed
qed

lemma regular_n_tree_greatest_tree: "n \<noteq> 0 \<Longrightarrow> greatest_tree n \<in> regular_n_trees n"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case unfolding regular_n_trees_def n_trees_def by (cases n) auto
qed

lemma regular_n_tree_enum: "t \<in> set (n_tree_enum n) \<Longrightarrow> regular t"
  using regular_n_tree_enum_aux regular_n_tree_greatest_tree unfolding regular_n_trees_def by (cases n) auto


lemma size_n_tree_enum_aux: "n \<noteq> 0 \<Longrightarrow> r \<in> set (n_tree_enum_aux t) \<Longrightarrow> tree_size r = tree_size t"
proof (induction t rule: n_tree_enum_aux.induct)
  case (1 t)
  then show ?case
  proof (cases "next_tree_aux 0 t")
    case None
    then show ?thesis using 1 by auto
  next
    case (Some a)
    then show ?thesis using 1 size_next_tree' by auto
  qed
qed

lemma size_greatest_tree[simp]: "n \<noteq> 0 \<Longrightarrow> tree_size (greatest_tree n) = n"
  by (induction n rule: greatest_tree.induct) auto

lemma size_n_tree_enum: "t \<in> set (n_tree_enum n) \<Longrightarrow> tree_size t = n"
  using size_n_tree_enum_aux size_greatest_tree by (cases n, auto, fastforce)

subsection \<open>Totality\<close>

lemma "set (n_tree_enum n) \<subseteq> regular_n_trees n"
  using regular_n_tree_enum size_n_tree_enum unfolding regular_n_trees_def n_trees_def by blast

lemma greatest_tree_lt_Suc: "n \<noteq> 0 \<Longrightarrow> greatest_tree n < greatest_tree (Suc n)"
  by (induction n rule: greatest_tree.induct) (auto simp: tree_less_nested)

lemma greatest_tree_ge: "tree_size t \<le> n \<Longrightarrow> t \<le> greatest_tree n"
proof (induction n arbitrary: t rule: greatest_tree.induct)
  case 1
  then show ?case by (cases t rule: tree_cons_exhaust) (auto simp: tree_size_ne_0)
next
  case (2 v)
  then show ?case
  proof (cases t rule: tree_rev_exhaust)
    case Nil
    then show ?thesis by simp
  next
    case (Snoc ts r)
    then have r_le_greatest_Suc_v: "r \<le> greatest_tree (Suc v)" using 2 by auto
    then show ?thesis
    proof (cases "r = greatest_tree (Suc v)")
      case True
      then have "ts = []" using 2(2) Snoc by (simp add: tree_size_ne_0)
      then show ?thesis using Snoc r_le_greatest_Suc_v by auto
    next
      case False
      then show ?thesis using r_le_greatest_Suc_v Snoc by auto
    qed
  qed
next
  case 3
  then show ?case by (simp add: tree_size_ne_0)
qed

fun least_tree :: "nat \<Rightarrow> tree" where
  "least_tree (Suc n) = Node (replicate n (Node []))"

lemma regular_n_tree_least_tree: "n \<noteq> 0 \<Longrightarrow> least_tree n \<in> regular_n_trees n"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case unfolding regular_n_trees_def n_trees_def by (cases n) auto
qed

lemma height_lt_2_least_tree: "t \<in> regular_n_trees n \<Longrightarrow> height t < 2 \<Longrightarrow> t = least_tree n"
proof (induction n arbitrary: t)
  case 0
  have "regular_n_trees 0 = {}" unfolding regular_n_trees_def n_trees_def using tree_size.elims by auto
  then show ?case using 0 by blast
next
  case (Suc n)
  then show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis using Suc tree_size.elims unfolding regular_n_trees_def n_trees_def
        by (auto, metis leD length_children length_greater_0_conv)
  next
    case False
    then have t_non_empty: "t \<noteq> Node []" using Suc(2) unfolding regular_n_trees_def n_trees_def by auto
    then have height_t: "height t = 1" using Suc(3)
      by (metis One_nat_def gr0_conv_Suc height.elims less_2_cases less_numeral_extra(3))
    obtain s ts where s_ts: "t = Node (s # ts)" using t_non_empty by (meson height.elims)
    then have "height s = 0" by (metis Suc_le_eq height_Node_cons less_one height_t)
    then have s: "s = Node []" using height_0_iff by simp
    then have regular_ts: "Node ts \<in> regular_n_trees n" using Suc(2) unfolding s_ts regular_n_trees_def n_trees_def by auto
    have "height (Node ts) < 2" using height_t height_children height_children_le_height unfolding s_ts One_nat_def by fastforce
    then have "Node ts = least_tree n" using Suc(1) regular_ts by blast
    then show ?thesis using False gr0_conv_Suc s s_ts by auto
  qed
qed

lemma least_tree_le: "n \<noteq> 0 \<Longrightarrow> tree_size t \<ge> n \<Longrightarrow> least_tree n \<le> t"
proof (induction n arbitrary: t rule: less_induct)
  case (less n)
  then obtain n' where n: "n = Suc n'" using least_tree.cases by blast
  then obtain ts where t: "t = Node ts" by (cases t) auto
  then show ?case
  proof (cases n')
    case 0
    then show ?thesis using n by simp
  next
    case (Suc n'')
    then show ?thesis
    proof (cases ts rule: rev_exhaust)
      case Nil
      then show ?thesis using less t n by auto
    next
      case (snoc rs r)
      then show ?thesis
      proof (cases "r = Node []")
        case True
        then have "tree_size (Node rs) \<ge> n''" using less(3) unfolding n t Suc snoc by auto
        then show ?thesis using less True unfolding n t Suc snoc
          by (auto simp: simp: replicate_append_same[symmetric], force)
      next
        case False
        then show ?thesis using less False unfolding n t Suc snoc
          by (auto simp: replicate_append_same[symmetric] tree_less_empty_iff)
      qed
    qed
  qed
qed

lemma trim_id': "n \<ge> tree_size t \<Longrightarrow> trim_tree n t = (n', t') \<Longrightarrow> t' = t"
proof (induction n t arbitrary: n' t' rule: trim_tree.induct)
  case (1 t)
  then show ?case by auto
next
  case (2 t)
  then have "t = Node []" using le_Suc_eq tree_size_1_iff tree_size_ne_0 by simp
  then show ?case using 2 by auto
next
  case (3 v)
  then show ?case by auto
next
  case (4 va t ts)
  then show ?case using size_trim_tree[OF _ 4(4)] size_trim_tree
    by (auto split: prod.splits nat.splits simp: tree_size_ne_0, fastforce)
qed

lemma tree_ge_lt_suffix: "Node ts \<le> r \<Longrightarrow> r < Node (t#ts) \<Longrightarrow> \<exists>ss. r = Node (ss @ ts)"
proof (induction ts arbitrary: r rule: rev_induct)
  case Nil
  then show ?case by (cases r rule: tree_rev_exhaust) auto
next
  case (snoc x xs)
  then show ?case using tree_le_empty2_iff
    by (cases r rule: tree_rev_exhaust)
      (simp_all, metis Cons_eq_appendI tree.inject tree_less_antisym tree_less_snoc2_iff)
qed

lemma trim_tree_0_iff: "fst (trim_tree n t) = 0 \<longleftrightarrow> n \<le> tree_size t"
  using size_trim_tree trim_id tree_size_ge_1
  by (induction n t rule: trim_tree.induct, auto split: prod.split nat.split tree.split, fastforce+)

lemma trim_tree_greatest_le: "tree_size r \<le> n \<Longrightarrow> r \<le> t \<Longrightarrow> r \<le> snd (trim_tree n t)"
proof (induction n t arbitrary: r rule: trim_tree.induct)
  case (1 t)                   
  then show ?case by auto                               
next
  case (2 t)
  then show ?case using tree_size_ne_0 tree_size_1_iff by (simp add: le_Suc_eq)
next
  case (3 v)
  then show ?case by auto
next
  case (4 va t ts)
  obtain n1 t1 where nt1: "trim_tree (Suc (Suc va)) (Node ts) = (n1, t1)" by fastforce
  then show ?case
  proof (cases n1)
    case 0
    then show ?thesis
    proof (cases "r \<le> Node ts")
      case True
      then show ?thesis using 4 0 nt1 by simp
    next
      case False
      then obtain ss s where r: "r = Node (ss @ s # ts)" using 4(4) tree_ge_lt_suffix
        by (metis append.assoc append_Cons append_Nil nle_le rev_exhaust tree_le_def)
      then have "tree_size (Node ts) \<ge> Suc (Suc va)" using nt1 trim_tree_0_iff unfolding 0 by fastforce
      then have "tree_size r > Suc (Suc va)" using tree_size_ne_0 unfolding r
        by (auto simp: add_strict_increasing trans_less_add2)
      then show ?thesis using 4(3) by auto
    qed
  next
    case (Suc nat)  
    then have t1: "t1 = Node ts" using trim_id nt1 by blast
    then obtain n2 t2 where nt2: "trim_tree n1 t = (n2, t2)" by fastforce
    then show ?thesis
    proof (cases "r \<le> Node ts")
      case True
      then show ?thesis using 4 Suc nt1 t1
        by (auto split: prod.split simp: tree_le_cons, meson dual_order.trans tree_le_cons)
    next
      case False
      then obtain ss s where r: "r = Node (ss @ s # ts)" using 4(4) tree_ge_lt_suffix
        by (metis append.assoc append_Cons append_Nil nle_le rev_exhaust tree_le_def)
      have size_s: "tree_size s \<le> Suc nat" using 4(3) Suc size_trim_tree[OF _ nt1] t1 unfolding r by auto
      have "s \<le> t" using 4(4) unfolding r by (meson order.trans tree_le_append tree_le_cons2)
      have "s \<le> t2" using "4.IH"(2)[OF nt1[symmetric] Suc t1 size_s \<open>s\<le>t\<close>] nt2 unfolding Suc by auto
      then show ?thesis
      proof (cases "s = t2")
        case True
        then have "ss = []"
        proof (cases "t2 = t")
          case True
          then show ?thesis using 4(4) nle_le tree_le_append unfolding r \<open>s=t2\<close> True by auto
        next
          case False
          then have "n2 = 0" using nt2 trim_id by (cases n2) auto
          then show ?thesis using size_trim_tree[OF _ nt1] size_trim_tree[OF _ nt2] Suc 4(3) tree_size_ne_0 unfolding r t1 \<open>s=t2\<close> by auto
        qed
        then show ?thesis using nt1 Suc t1 nt2 unfolding r True by auto
      next
        case False
        then show ?thesis using \<open>s\<le>t2\<close> nt1 nt2 t1 Suc unfolding r
          by (auto simp: order_less_imp_le tree_less_comm_suffix2)
      qed
    qed
  qed
qed

lemma fill_tree_next_smallest: "tree_size (Node rs) \<le> Suc n \<Longrightarrow> \<forall>r\<in>set rs. r \<le> t \<Longrightarrow> Node rs \<le> Node (fill_tree n t)"
proof (induction n t arbitrary: rs rule: fill_tree.induct)
  case (1 uu)
  have "rs = []" using tree_size_1_iff 1(1) tree.inject by fastforce
  then show ?case by auto
next
  case (2 v t)
  obtain n' t' where nt': "trim_tree (Suc v) t = (n', t')" by fastforce
  then show ?case
  proof (cases rs rule: rev_exhaust)
    case Nil
    then show ?thesis by auto
  next
    case (snoc rs' r')
    then show ?thesis
    proof (cases n')
      case 0
      then show ?thesis
      proof (cases "r' = t'")
        case True
        then have "rs' = []" using 0 2(2) size_trim_tree[OF _ nt'] unfolding snoc by (auto simp: tree_size_ne_0)
        then show ?thesis using nt' 0 unfolding snoc True by simp
      next
        case False
        then show ?thesis using 2 trim_tree_greatest_le nt' 0 tree_less_comm_suffix2 unfolding snoc
          by (auto, metis nless_le not_less_eq_eq snd_eqD trans_le_add2)
      qed
    next
      case (Suc nat)
      then show ?thesis using 2 nt' trim_id[OF nt'[unfolded Suc]] size_trim_tree[OF _ nt'] unfolding snoc by auto
    qed
  qed
qed

fun fill_twos :: "nat \<Rightarrow> tree \<Rightarrow> tree" where
  "fill_twos n (Node ts) = Node (replicate n (Node []) @ ts)"

lemma size_fill_twos: "tree_size (fill_twos n t) = n + tree_size t"
  by (cases t) (auto simp: sum_list_replicate)

lemma regular_fill_twos: "regular t \<Longrightarrow> regular (fill_twos n t)"
  by (cases t) (auto simp: sorted_append)

lemma fill_twos_lt: "n \<noteq> 0 \<Longrightarrow> t < fill_twos n t"
  using tree_less_append by (cases t) auto

lemma fill_twos_less: "r < Node (t#ts) \<Longrightarrow> t \<noteq> Node [] \<Longrightarrow> fill_twos n r < Node (t#ts)"
proof (induction n)
  case 0
  then show ?case by (cases r) auto
next
  case (Suc n)
  then show ?case by (cases r rule: tree.exhaust, simp,
        meson leD linorder_less_linear list.inject tree.inject tree_empty_cons_lt_le)
qed

lemma next_tree_aux_successor: "tree_size r = tree_size t + n \<Longrightarrow> regular r \<Longrightarrow> r < t \<Longrightarrow> height t \<ge> 2 \<Longrightarrow> r \<le> the (next_tree_aux n t)"
proof (induction n t arbitrary: r rule: next_tree_aux.induct)
  case (1 n)
  then show ?case by auto
next
  case (2 n ts)
  have size_r: "tree_size r \<le> tree_size (Node ts) + Suc n" using 2(2) by auto
  have height_ts: "height (Node ts) \<ge> 2" using 2(5) by (cases ts) auto
  then show ?case using 2 size_r tree_empty_cons_lt_le by fastforce
next
  case (3 n rs ts)
  then show ?case
  proof (cases "r < Node ts")
    case True
    then show ?thesis by (auto, meson dual_order.trans order.strict_implies_order tree_le_append tree_le_cons)
  next
    case False
    then obtain ss where r: "r = Node (ss @ ts)" using 3(3) tree_ge_lt_suffix by fastforce
    show ?thesis
    proof (cases ss rule: rev_exhaust)
      case Nil
      then show ?thesis unfolding r by (simp, meson order_trans tree_le_append tree_le_cons)
    next
      case (snoc ss' s')
      have s'_le_rs: "s' \<le> Node rs" using 3(3) tree_empty_cons_lt_le unfolding r snoc
        by (metis (mono_tags, lifting) append.assoc append_Cons append_self_conv2
            dual_order.order_iff_strict linorder_not_less order_less_le_trans tree_le_append tree_less_cons2)
      show ?thesis
      proof (cases "s' = Node rs")
        case True
        then show ?thesis using 3(1,2) fill_tree_next_smallest unfolding r snoc
          by (auto simp del: fill_tree.simps simp: sorted_append)
      next
        case False
        then show ?thesis using s'_le_rs unfolding r snoc by (auto, meson tree_le_def tree_less_iff)
      qed
    qed
  qed
next
  case (4 n vc vd vb ts)
  define t where "t = Node (Node (vc # vd) # vb)"
  have height_t: "height t \<ge> 2" unfolding numeral_2_eq_2 t_def
    by (metis dual_order.antisym height_Node_cons less_eq_nat.simps(1) not_less_eq_eq)
  then show ?case
  proof (cases "r < Node ts")
    case True
    then show ?thesis by (auto, meson dual_order.trans order.strict_implies_order tree_le_append tree_le_cons)
  next
    case False
    then obtain ss where r: "r = Node (ss @ ts)" using 4(4) tree_ge_lt_suffix by fastforce
    then show ?thesis
    proof (cases ss rule: rev_exhaust)
      case Nil
      then show ?thesis using tree_le_cons unfolding r by auto
    next
      case (snoc ss' s')
      have "s' < t" using 4(4)[folded t_def] unfolding r snoc
        by (auto, metis antisym_conv3 append.left_neutral dual_order.strict_trans less_tree_comm_suffix not_tree_less_empty tree_less_cons2)
      show ?thesis
      proof (cases "tree_size s' = tree_size t + n")
        case True
        then have "ss' = []" using 4(2)[folded t_def] tree_size_ne_0 unfolding r snoc by auto
        then show ?thesis using "4.IH" True 4(3) \<open>s'<t\<close> height_t tree_le_cons2 unfolding r snoc t_def by auto
      next
        case False
        obtain us where s': "s' = Node us" using tree.exhaust by blast
        \<comment> \<open>s'' is greater than s' but has the same size as t so the IH can be used on it.\<close>
        define s'' where "s'' = fill_twos (tree_size t + n - tree_size s') s'"
        have size_s': "tree_size s' \<le> tree_size t + n" using 4(2)[folded t_def] unfolding r snoc by simp
        then have size_s'': "tree_size s'' = tree_size t + n" unfolding s''_def using size_fill_twos by auto
        have regular_s'': "regular s''" using regular_fill_twos 4(3) unfolding s''_def r snoc by auto
        have "s'' < t" using fill_twos_less \<open>s'<t\<close> unfolding t_def s''_def by auto
        have "s' < s''" using fill_twos_lt False size_fill_twos size_s'' unfolding s''_def by auto
        then show ?thesis using "4.IH"[folded t_def, OF size_s'' regular_s'' \<open>s''<t\<close> height_t]
          unfolding r snoc t_def by (simp add: order_less_imp_le tree_less_comm_suffix2)
      qed
    qed
  qed
qed

lemma next_tree_successor: "tree_size r = tree_size t \<Longrightarrow> regular r \<Longrightarrow> r < t \<Longrightarrow> next_tree t = Some t' \<Longrightarrow> r \<le> t'"
  using next_tree_aux_successor next_tree_Some_iff by force

lemma set_n_tree_enum_aux: "t \<in> regular_n_trees n \<Longrightarrow> set (n_tree_enum_aux t) = {r\<in>regular_n_trees n. r \<le> t}"
proof (induction t rule: n_tree_enum_aux.induct)
  case (1 t)
  then show ?case
  proof (cases "next_tree t")
    case None
    have "n \<noteq> 0" using 1(2) tree_size_ne_0 unfolding regular_n_trees_def n_trees_def by auto
    have "t = least_tree n" using height_lt_2_least_tree next_tree_aux_None_iff 1 None by simp
    then show ?thesis using next_tree_Some_iff 1 None least_tree_le \<open>n\<noteq>0\<close>
      unfolding regular_n_trees_def n_trees_def by (auto simp: antisym)
  next
    case (Some t')
    then have "set (n_tree_enum_aux t) = insert t {r \<in> regular_n_trees n. r \<le> t'}"
      using 1 regular_next_tree' size_next_tree' unfolding regular_n_trees_def n_trees_def by auto
    also have "\<dots> = {r\<in>regular_n_trees n. r \<le> t}" using next_tree_successor 1(2) Some unfolding regular_n_trees_def n_trees_def
      by (auto, meson Some less_le_not_le next_tree_lt' order.trans)
    finally show ?thesis .
  qed
qed

theorem set_n_tree_enum: "set (n_tree_enum n) = regular_n_trees n"
proof (cases n)
  case 0
  then show ?thesis unfolding regular_n_trees_def n_trees_def using tree_size_ne_0 by simp
next
  case (Suc nat)
  then show ?thesis using set_n_tree_enum_aux regular_n_tree_greatest_tree greatest_tree_ge
    unfolding regular_n_trees_def n_trees_def by auto
qed

theorem n_rtree_graph_enum_n_rtree_graphs: "G \<in> set (n_rtree_graph_enum n) \<Longrightarrow> G \<in> n_rtree_graphs n"
  using set_n_tree_enum rtree_tree_graph card_tree_graph
  unfolding n_rtree_graph_enum_def n_rtree_graphs_def regular_n_trees_def n_trees_def
  by (auto, metis)

theorem n_rtree_graph_enum_surj:
  assumes n_rtree_graph: "G \<in> n_rtree_graphs n"
  shows "\<exists>G' \<in> set (n_rtree_graph_enum n). G' \<simeq>\<^sub>r G"
proof-
  obtain V E r where "G = (V,E,r)" using prod.exhaust by metis
  then show ?thesis using n_rtree_graph set_n_tree_enum rtree.ex_regular_n_tree
    unfolding n_rtree_graphs_def n_rtree_graph_enum_def by (auto simp: rtree.ex_regular_n_tree)
qed

subsection \<open>Distinctness\<close>

lemma n_tree_enum_aux_le: "r \<in> set (n_tree_enum_aux t) \<Longrightarrow> r \<le> t"
proof (induction t rule: n_tree_enum_aux.induct)
  case (1 t)
  then show ?case
  proof (cases "next_tree t")
    case None
    then show ?thesis using 1 by auto
  next
    case (Some a)
    then show ?thesis using next_tree_lt' 1 by fastforce
  qed
qed

lemma sorted_n_tree_enum_aux: "sorted_wrt (>) (n_tree_enum_aux t)"
proof (induction t rule: n_tree_enum_aux.induct)
  case (1 t)
  then show ?case
  proof (cases "next_tree t")
    case None
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis using 1 Some next_tree_lt' n_tree_enum_aux_le by fastforce
  qed
qed

lemma distinct_n_tree_enum_aux: "distinct (n_tree_enum_aux t)"
  using sorted_n_tree_enum_aux strict_sorted_iff distinct_rev sorted_wrt_rev by blast

theorem distinct_n_tree_enum: "distinct (n_tree_enum n)"
  using distinct_n_tree_enum_aux by (cases n) auto

theorem distinct_n_rtree_graph_enum: "distinct (n_rtree_graph_enum n)"
  using tree_graph_inj distinct_n_tree_enum set_n_tree_enum unfolding n_rtree_graph_enum_def regular_n_trees_def
  by (simp add: distinct_map inj_on_def)

theorem inj_iso_n_rtree_graph_enum:
  assumes G_in_n_rtree_graph_enum: "G \<in> set (n_rtree_graph_enum n)"
    and H_in_n_rtree_graph_enum: "H \<in> set (n_rtree_graph_enum n)"
    and "G \<simeq>\<^sub>r H"
  shows "G = H"
proof-
  obtain t\<^sub>G where t_G: "regular t\<^sub>G" "tree_graph t\<^sub>G = G" using G_in_n_rtree_graph_enum regular_n_tree_enum
    unfolding n_rtree_graph_enum_def by auto
  obtain t\<^sub>H where t_H: "regular t\<^sub>H" "tree_graph t\<^sub>H = H" using H_in_n_rtree_graph_enum regular_n_tree_enum
    unfolding n_rtree_graph_enum_def by auto
  then show ?thesis using t_G tree_graph_inj_iso \<open>G \<simeq>\<^sub>r H\<close> by auto
qed

theorem ex1_iso_n_rtree_graph_enum: "G \<in> n_rtree_graphs n \<Longrightarrow> \<exists>!G' \<in> set (n_rtree_graph_enum n). G' \<simeq>\<^sub>r G"
  using inj_iso_n_rtree_graph_enum rgraph_isomorph_trans rgraph_isomorph_sym n_rtree_graph_enum_surj unfolding transp_def by blast

end