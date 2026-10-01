section "Strongly Joinable AVL Trees"

theory StronglyJoinableAVL
imports
  "StronglyJoinable"
  "HOL-Data_Structures.AVL_Set"
begin

text \<open>
  As a proof of concept, the @{locale StronglyJoinable} framework is instantiated for
  the AVL trees of the standard library, with the height as rank and balance constants
  $c_l = 1$ and $c_u = 2$. Instantiating the abstract results then yields fully 
  numeric running-time bounds for union, intersection and difference on AVL trees.
\<close>

subsection "Join for AVL Trees"

text \<open>
  Following \<^cite>\<open>blelloch2022joinable\<close>, \<open>join\<close> walks down the spine of the taller tree until it
  reaches a subtree whose height is within one of the smaller tree, attaches the
  smaller tree together with the pivot there, and rebalances on the way back up with
  the standard AVL rotations (@{const balL}, @{const balR}).
\<close>

fun joinR where
"joinR L a R = (case L of Node l (k,_) r \<Rightarrow> 
 if ht r \<le> ht R + 1 
 then balR l k (node r a R)
 else balR l k (joinR r a R))"

declare joinR.simps[simp del]

fun joinL where
"joinL L a R = (case R of Node l (k,_) r \<Rightarrow> 
 if ht l \<le> ht L + 1 
 then balL (node L a l) k r
 else balL (joinL L a l) k r)"

declare joinL.simps[simp del]

fun join where 
"join l a r = 
(if      ht l > ht r + 1 then joinR l a r
 else if ht r > ht l + 1 then joinL l a r
 else    node l a r)"

subsection "Proof of Correctness"

text \<open>
  The @{locale Set2_Join} interpretation requires the set semantics of \<open>join\<close>,
  preservation of the search-tree order, and preservation of the AVL invariant.
\<close>

subsubsection "Set Preservation"

lemma balR_set:"set_tree (balR l a r) = set_tree 
  l \<union> {a} \<union> set_tree r"
  by (auto simp: balR_def node_def split!: if_splits tree.splits)

lemma joinR_set:"ht l > ht r + 1 \<Longrightarrow> set_tree (joinR l a r) = set_tree 
  l \<union> {a} \<union> set_tree r"
proof(induction l a r rule: joinR.induct)
  case (1 L a R)
  then show ?case 
    by (auto simp: joinR.simps[of L a R] balR_set node_def split!: if_splits tree.splits)
qed

lemma balL_set:"set_tree (balL l a r) = set_tree 
  l \<union> {a} \<union> set_tree r"
  by (auto simp: balL_def node_def split!: if_splits tree.splits)

lemma joinL_set:"ht r > ht l + 1 \<Longrightarrow> set_tree (joinL l a r) = set_tree 
  l \<union> {a} \<union> set_tree r"
proof(induction l a r rule: joinL.induct)
  case (1 L a R)
  then show ?case 
    by (auto simp: joinL.simps[of L a R]  balL_set node_def split!: if_splits tree.splits)
qed

corollary set_join:"set_tree (join l a r) = set_tree l \<union> {a} \<union> set_tree r"
  by(auto simp: node_def joinR_set joinL_set split!: if_splits)

subsubsection "BST Preservation"

lemma balR_bst:"\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y\<rbrakk>
  \<Longrightarrow> bst (balR l a r)"
  by (auto simp: balR_def node_def split!: if_splits tree.splits)

lemma joinR_bst:"\<lbrakk>ht l > ht r + 1; bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y\<rbrakk>
  \<Longrightarrow> bst (joinR l a r)"
proof(induction l a r arbitrary: b rule: joinR.induct)
  case (1 L a R)
  then show ?case
    by (auto simp: joinR.simps[of L a R] node_def balR_bst joinR_set ball_Un 
      intro!: balR_bst split!: if_splits tree.splits) 
qed

lemma balL_bst:"\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y\<rbrakk>
  \<Longrightarrow> bst (balL l a r)"
  by (auto simp: balL_def node_def split!: if_splits tree.splits)

lemma joinL_bst:"\<lbrakk>ht r > ht l + 1; bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>y\<in>set_tree r. a < y\<rbrakk>
\<Longrightarrow> bst (joinL l a r)"
proof(induction l a r arbitrary: b rule: joinL.induct)
  case (1 L a R)
  then show ?case
    by (auto simp: joinL.simps[of L a R] node_def balL_bst joinL_set ball_Un 
      intro!: balL_bst split!: if_splits tree.splits) 
qed

corollary bst_join:"bst (Node l (a, b) r) \<Longrightarrow> bst (join l a r)"
  by(auto simp: node_def joinR_bst joinL_bst split!: if_splits)

subsubsection "Preservation of AVL Predicate"

lemma avl_joinR_height:"\<lbrakk>avl l; avl r; height l > height r + 1\<rbrakk> 
\<Longrightarrow> avl (joinR l a r) \<and> height (joinR l a r) \<in> {height l, height l + 1}"
proof(induction l a r rule: joinR.induct)
  case (1 L a R)
  then show ?case 
    by(fastforce simp: joinR.simps[of L a R] balR_def node_def max_absorb2 split!: if_splits tree.splits)
qed

lemma avl_joinL_height:"\<lbrakk>avl l; avl r; height r > height l + 1\<rbrakk> 
\<Longrightarrow> avl (joinL l a r) \<and> height (joinL l a r) \<in> {height r, height r + 1}"
proof(induction l a r rule: joinL.induct)
  case (1 L a R)
  then show ?case 
    by(fastforce simp: joinL.simps[of L a R] balL_def node_def max_absorb2 split!: if_splits tree.splits)
qed

corollary inv_join:"\<lbrakk>avl l; avl r\<rbrakk> \<Longrightarrow> avl (join l a r)"
  by(auto simp: node_def avl_joinR_height avl_joinL_height split: if_splits)

text \<open>To finish the proof of functional correctness, instantiate the \<open>Set2_Join\<close> locale.\<close>

interpretation tree_ht: Set2_Join
where join = join and inv = avl
proof (standard, goal_cases)
  case 1 show ?case by (rule set_join)
next
  case 2 then show ?case by (rule bst_join)
next
  case 3 show ?case by simp
next
  case 4 then show ?case by (rule inv_join)
next
  case 5 then show ?case by simp
qed

subsection "Proof of Strongly Joinable Properties"

text \<open>
  The additional obligations of @{locale StronglyJoinable} are discharged with
  @{const height} as rank. The central fact is \<open>join_height\<close> below i.e. a join has the
  height of its taller argument or one more. Monotonicity and the submodularity rule
  are elementary consequences. The balance predicate holds for AVL trees with
  $c_l = 1$ and $c_u = 2$.
\<close>

subsubsection "Monotonicity Rule"

corollary join_height: 
assumes "avl l \<and> avl r"
shows "height (join l a r) \<in> {max (height l) (height r), max (height l) (height r) + 1}"
proof-
  consider 
    (Right) R  where "R = joinR l a r" and "ht l > ht r + 1" and 
                     "join l a r = R"
  | (Left)  L  where "L = joinL l a r" and "ht r > ht l + 1" and 
                     "join l a r = L"
  | (Node)  EQ where "EQ = node l a r" and "ht r \<le> ht l + 1" and 
                     "ht l \<le> ht r + 1" and "join l a r = EQ"
    by(auto split!: if_splits)linarith
  then show ?thesis
  proof cases
    case Right
    from this assms show ?thesis 
      by (metis add_lessD1 avl_joinR_height ht_height max.absorb3)
  next
    case Left
    from this assms show ?thesis 
      by (metis add_lessD1 ht_height avl_joinL_height max.absorb4)
  next
    case Node
    then show ?thesis 
      by simp
  qed
qed

corollary rule_mono: "\<lbrakk>avl l; avl r\<rbrakk> \<Longrightarrow> max (height l) (height r) \<le> height (join l a r)"
  using join_height 
  by (metis insertE le_add_same_cancel1 zero_le_one nle_le singletonD)

subsubsection "Submodularity Rule"

text \<open>
  A join adds at most one to the larger input height, while a node adds exactly one
  to the larger child height. Hence, whatever the replacement subtrees are, the join
  can exceed the original node by no more than the replacements exceed the original
  subtrees. This also covers the mixed case where one subtree shrinks.\<close>

lemma rule_sub:
  assumes "real (height l') \<le> real (height l) + x" "real (height r') \<le> real (height r) + x"
  assumes "avl l'" "avl r'"
  shows "real (height (join l' a r')) \<le> real (height (Node l (a,b) r)) + x"
proof -
  have "height (join l' a r') \<le> max (height l') (height r') + 1"
    using join_height[of l' r' a] assms(3,4) by auto
  then have "real (height (join l' a r')) \<le> max (real (height l')) (real (height r')) + 1"
    by (metis of_nat_le_iff of_nat_max of_nat_1 of_nat_add)
  moreover have "max (real (height l')) (real (height r')) \<le> max (real (height l)) (real (height r)) + x"
    using assms(1,2) by linarith
  moreover have "real (height (Node l (a,b) r)) = max (real (height l)) (real (height r)) + 1"
    by force
  ultimately show ?thesis
    by linarith
qed
subsubsection "Balancing Rule" 

interpretation tree_ht: BalancedShape
where rank = height and c\<^sub>l = 1 and c\<^sub>u = 2
  by (standard, goal_cases) auto

lemma rule_bal: "avl t \<Longrightarrow> tree_ht.balanced t "
  by(induction t) auto

interpretation tree_ht: BalancedTree
where rank = height and c\<^sub>l = 1 and c\<^sub>u = 2 and inv = avl
  by standard (rule rule_bal)

subsubsection "Cost Rule"

time_fun ht
time_fun node
time_fun balL
time_fun balR

lemma T_ht_0[simp]: "T_ht t = 0"
  by (cases t rule: tree2_cases) auto

lemma T_node_0[simp]: "T_node l a r = 0"
  by simp

lemma T_balL_0[simp]: "T_balL l a r = 0"
  by (auto split!: tree.splits if_splits)

lemma T_balR_0[simp]: "T_balR l a r = 0"
  by (auto split!: tree.splits if_splits)

time_fun joinR
time_fun joinL
time_fun join

declare T_joinR.simps[simp del]
declare T_joinL.simps[simp del]

lemma T_joinR:"\<lbrakk>avl l; avl r; ht l > ht r + 1\<rbrakk> \<Longrightarrow> T_joinR l a r \<le> 1 + height l - height r"
proof(induction l a r rule: T_joinR.induct)
  case (1 L a R)
  then show ?case 
    using T_joinR.simps[of L a R]
    by(auto simp: max_absorb2 split!: if_splits tree.splits) fastforce+
qed

lemma T_joinL:"\<lbrakk>avl l; avl r; ht r > ht l + 1\<rbrakk> \<Longrightarrow> T_joinL l a r \<le> 1 + height r - height l"
proof(induction l a r rule: T_joinL.induct)
  case (1 L a R)
  then show ?case 
    by(auto simp: T_joinL.simps[of L a R] max_absorb1 split!: if_splits tree.splits) fastforce+
qed

corollary rule_cost:
assumes "avl l \<and> avl r" 
shows "T_join l a r \<le> 1 + nat(abs(int(height l) - int(height r)))"
proof-
  consider
    (Right) R where "R = T_joinR l a r" and "ht l > ht r + 1" and
                    "T_join l a r = R"
  | (Left)  L where "L = T_joinL l a r" and "ht r > ht l + 1" and
                    "T_join l a r = L"
  | (Node)  EQ where "EQ = 0" and "ht r \<le> ht l + 1" and
                     "ht l \<le> ht r + 1" and "T_join l a r = EQ"
    by(auto split!: if_splits)linarith
  then show ?thesis 
  proof cases
    case Right
    then have "max (height l) (height r) = height l"
      using assms by simp
    then moreover have "nat(abs(int(height l) - int(height r))) = height l - height r"
      by simp
    ultimately show ?thesis 
      using Right T_joinR assms by (metis Nat.add_diff_assoc max.orderI)
  next
    case Left
    then have "max (height l) (height r) = height r"
      using assms by simp
    then moreover have "nat(abs(int(height l) - int(height r))) = height r - height l"
      by simp
    ultimately show ?thesis 
      using Left T_joinL assms by (metis Nat.add_diff_assoc max.cobounded1)
  next
    case Node
    then show ?thesis 
      by simp
  qed
qed

subsection \<open>Instantiation of \<open>StronglyJoinable\<close>\<close>

text \<open>By functional correctness, every join adds exactly one element.\<close>

lemma balR_size:"size (balR l a r) = size l + size r + 1"
  by(auto simp: balR_def node_def split!: if_split tree.split)

lemma balL_size:"size (balL l a r) = size l + size r + 1"
  by(auto simp: balL_def node_def split!: if_split tree.split)

lemma joinR_size:"ht l > ht r + 1 \<Longrightarrow> size (joinR l a r) = size l + size r + 1"
proof(induction l a r rule: joinR.induct)
  case (1 L a R)
  then show ?case 
    by (auto simp: joinR.simps[of L a R] balR_size node_def split!: if_splits tree.splits)
qed
  
lemma joinL_size:"ht r > ht l + 1 \<Longrightarrow> size (joinL l a r) = size l + size r + 1"
proof(induction l a r rule: joinL.induct)
  case (1 L a R)
  then show ?case 
    by (auto simp: joinL.simps[of L a R] balL_size node_def split!: if_splits tree.splits)
qed

lemma join_size:"size (join l a r) = size l + size r + 1"
  by(auto simp: node_def joinR_size joinL_size split!: if_splits)

text \<open>All obligations of @{locale StronglyJoinable} are now in place.\<close>

interpretation tree_ht: StronglyJoinable
where join = join and inv = avl
and rank = height and c\<^sub>l = 1 and c\<^sub>u = 2
and T_join = T_join and k\<^sub>0 = 1 and k\<^sub>1 = 1
proof (standard, goal_cases)
  case (1 l r a)
  then show ?case
    by (metis of_nat_le_iff of_nat_max rule_mono)
next
  case (2 l' l x r' r a b)
  then show ?case
    by (intro rule_sub)
next
  case (3 l a r)
  then show ?case
    by (metis join_size)
next
  case (4 l r a)
  have "real (T_join l a r) \<le> 1 + real (nat \<bar>int (height l) - int (height r)\<bar>)"
    using rule_cost 4 by (metis of_nat_1 of_nat_add of_nat_le_iff)
  also have "real (nat \<bar>int (height l) - int (height r)\<bar>)
             = \<bar>real (height l) - real (height r)\<bar>"
    by linarith
  finally show ?case by simp
next
  case 5
  then show ?case by simp
qed

subsection \<open>Concrete constants for AVL\<close>

text \<open>
  All abstract constants are evaluated for the AVL instantiation.
\<close>

lemma avl_c_delta: "tree_ht.c\<^sub>\<delta> = 1"
  unfolding tree_ht.c\<^sub>\<delta>_def by simp

lemma avl_C: "tree_ht.C = 1"
  unfolding tree_ht.C_def by simp

lemma avl_K_split: "tree_ht.K_split = 8"
  unfolding tree_ht.K_split_def by simp

lemma avl_K_T: "tree_ht.K_T = 4"
  unfolding tree_ht.K_T_def by simp

lemma avl_K_min: "tree_ht.K_min = 4"
  unfolding tree_ht.c\<^sub>1_def avl_c_delta tree_ht.K_min_def by auto

lemma avl_K_lin_union: "tree_ht.K_T * tree_ht.K_lin 2 3 \<le> 1238"
proof -
  have "tree_ht.K_T * tree_ht.K_lin 2 3 = 756 + 340 * sqrt 2"
    unfolding tree_ht.K_lin_def
    by (simp add: avl_K_T avl_C avl_K_split S1_two S2_two algebra_simps)
  also have "\<dots> \<le> 756 + 340 * 1.415"
    using sqrt2_bounds(3) by (auto intro: add_left_mono mult_left_mono)
  also have "756 + 340 * (1.415::real) \<le> 1238"
    by simp
  finally show ?thesis .
qed

lemma avl_K_log_union: "tree_ht.K_T * tree_ht.K_log 2 3 \<le> 629"
proof -
  have "tree_ht.K_T * tree_ht.K_log 2 3 = 504 + 88 * sqrt 2"
    unfolding tree_ht.K_log_def
    by (simp add: avl_K_T avl_C avl_K_split S1_two algebra_simps)
  also have "\<dots> \<le> 504 + 88 * 1.415"
    using sqrt2_bounds(3) by (auto intro: add_left_mono mult_left_mono)
  also have "504 + 88 * (1.415::real) \<le> 629"
    by simp
  finally show ?thesis .
qed

lemma avl_K_lin_inter: "tree_ht.K_T * tree_ht.K_lin 16 12 \<le> 2222"
proof -
  have "tree_ht.K_T * tree_ht.K_lin 16 12 = 1356 + 612 * sqrt 2"
    unfolding tree_ht.K_lin_def
    by (simp add: avl_K_T avl_C avl_K_split S1_two S2_two algebra_simps)
  also have "\<dots> \<le> 1356 + 612 * 1.415"
    using sqrt2_bounds(3) by (auto intro: add_left_mono mult_left_mono)
  also have "1356 + 612 * (1.415::real) \<le> 2222"
    by simp
  finally show ?thesis .
qed

lemma avl_K_log_inter: "tree_ht.K_T * tree_ht.K_log 16 12 \<le> 1131"
proof -
  have "tree_ht.K_T * tree_ht.K_log 16 12 = 904 + 160 * sqrt 2"
    unfolding tree_ht.K_log_def
    by (simp add: avl_K_T avl_C avl_K_split S1_two algebra_simps)
  also have "\<dots> \<le> 904 + 160 * 1.415"
    using sqrt2_bounds(3) by (auto intro: add_left_mono mult_left_mono)
  also have "904 + 160 * (1.415::real) \<le> 1131"
    by simp
  finally show ?thesis .
qed

text \<open>
  This yields fully numeric running-time bounds for the three set operations on AVL
  trees.\<close>

corollary avl_T_union_linlog:
  assumes "avl t1" "avl t2"
  shows "real (tree_ht.T_union t1 t2)
       \<le> 4 + 1238 * size_min t1 t2
         + 629 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (tree_ht.T_union t1 t2)
      \<le> tree_ht.K_T + (tree_ht.K_T * tree_ht.K_lin 2 3) * size_min t1 t2
        + (tree_ht.K_T * tree_ht.K_log 2 3)
          * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using tree_ht.T_union_bound[OF assms]
    by (simp add: avl_c_delta)
  also have "\<dots> \<le> 4 + 1238 * size_min t1 t2
        + 629 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using avl_K_lin_union avl_K_log_union avl_K_T
    by (intro add_mono mult_right_mono) (auto simp: log_def)
  finally show ?thesis .
qed

corollary avl_T_inter_linlog:
  assumes "avl t1" "avl t2"
  shows "real (tree_ht.T_inter t1 t2)
       \<le> 4 + 2222 * size_min t1 t2
         + 1131 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (tree_ht.T_inter t1 t2)
      \<le> tree_ht.K_T + (tree_ht.K_T * tree_ht.K_lin 16 12) * size_min t1 t2
        + (tree_ht.K_T * tree_ht.K_log 16 12)
          * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using tree_ht.T_inter_bound[OF assms]
    by (simp add: avl_K_min)
  also have "\<dots> \<le> 4 + 2222 * size_min t1 t2
        + 1131 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using avl_K_lin_inter avl_K_log_inter avl_K_T
    by (intro add_mono mult_right_mono) (auto simp: log_def)
  finally show ?thesis .
qed

corollary avl_T_diff_linlog:
  assumes "avl t1" "avl t2"
  shows "real (tree_ht.T_diff t1 t2)
       \<le> 4 + 2222 * size_min t1 t2
         + 1131 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (tree_ht.T_diff t1 t2)
      \<le> tree_ht.K_T + (tree_ht.K_T * tree_ht.K_lin 16 12) * size_min t1 t2
        + (tree_ht.K_T * tree_ht.K_log 16 12)
          * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using tree_ht.T_diff_bound[OF assms]
    by (simp add: avl_K_min)
  also have "\<dots> \<le> 4 + 2222 * size_min t1 t2
        + 1131 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using avl_K_lin_inter avl_K_log_inter avl_K_T
    by (intro add_mono mult_right_mono) (auto simp: log_def)
  finally show ?thesis .
qed

text \<open>
  The asymptotic statements are inherited through the interpretation. On pairs of
  growing AVL trees of sizes $m \le n$, in either argument order, all three operations
  run in $O(m \ln(n/m + 1))$.\<close>

corollary avl_T_union_bigo:
  "(\<lambda>(t1, t2). real (tree_ht.T_union t1 t2)) \<in> O[tree_ht.tree_pair_filter](\<lambda>(t1, t2).
     size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
  using tree_ht.T_union_bigo .

corollary avl_T_inter_bigo:
  "(\<lambda>(t1, t2). real (tree_ht.T_inter t1 t2)) \<in> O[tree_ht.tree_pair_filter](\<lambda>(t1, t2).
     size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
  using tree_ht.T_inter_bigo .

corollary avl_T_diff_bigo:
  "(\<lambda>(t1, t2). real (tree_ht.T_diff t1 t2)) \<in> O[tree_ht.tree_pair_filter](\<lambda>(t1, t2).
     size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
  using tree_ht.T_diff_bigo .

end
