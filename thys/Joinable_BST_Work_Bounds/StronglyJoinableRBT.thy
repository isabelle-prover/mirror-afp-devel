section "Strongly Joinable Red-Black Trees"

theory StronglyJoinableRBT
imports
  "StronglyJoinable"
begin

text \<open>
  The second instantiation of @{locale StronglyJoinable} covers red-black trees. The
  \<open>join\<close> of \<^cite>\<open>blelloch2022joinable\<close> stores the black height in every node and
  reads it in constant time, so the metadata field of the trees holds the colour together
  with the black height. The library implementation in
  \<open>HOL-Data_Structures.Set2_Join_RBT\<close> recomputes the black height on every step
  instead, which would charge \<open>join\<close> a cost linear in the ranks of its inputs rather than
  in their difference. Its rebalancing steps are, however, taken over unchanged.

  Two further deviations from the library concern the colour of the root. The library
  \<open>join\<close> paints the root black unconditionally and creates a black node whenever the two
  inputs have equal black height. Following the paper, the root is painted black only when
  it is red with a red child, and two black inputs of equal black height are combined by
  a red node. Both are necessary for the rank of a join to exceed the larger input rank by
  at most one.
\<close>

subsection "Red-black trees with stored black height"

datatype color = Red | Black

type_synonym 'a rbt = "('a * (color * nat)) tree"

text \<open>Both the colour and the black height are read from the node.\<close>

fun col :: "'a rbt \<Rightarrow> color" where
"col Leaf = Black" |
"col (Node _ (_, (c, _)) _) = c"

fun bh :: "'a rbt \<Rightarrow> nat" where
"bh Leaf = 0" |
"bh (Node _ (_, (_, h)) _) = h"

fun R :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"R l a r = Node l (a, (Red, bh l)) r"

fun B :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"B l a r = Node l (a, (Black, bh l + 1)) r"

lemma neq_Black[simp]: "(c \<noteq> Black) = (c = Red)"
  by (cases c) auto

lemma neq_Red[simp]: "(c \<noteq> Red) = (c = Black)"
  by (cases c) auto

subsubsection "Invariants"

fun invc :: "'a rbt \<Rightarrow> bool" where
"invc Leaf = True" |
"invc (Node l (_, (c, _)) r) = ((c = Red \<longrightarrow> col l = Black \<and> col r = Black) \<and> invc l \<and> invc r)"

text \<open>The weaker colour invariant allows a red root with a red child.\<close>

fun invc2 :: "'a rbt \<Rightarrow> bool" where
"invc2 Leaf = True" |
"invc2 (Node l _ r) = (invc l \<and> invc r)"

fun invh :: "'a rbt \<Rightarrow> bool" where
"invh Leaf = True" |
"invh (Node l (_, (c, h)) r) =
  (bh l = bh r \<and> h = (if c = Black then bh l + 1 else bh l) \<and> invh l \<and> invh r)"

abbreviation rbt :: "'a rbt \<Rightarrow> bool" where
"rbt t \<equiv> invc t \<and> invh t"

lemma invc2I: "invc t \<Longrightarrow> invc2 t"
  by (cases t rule: tree2_cases) auto

subsubsection "Rebalancing"

text \<open>The rotations \<open>baliL\<close> and \<open>baliR\<close> of the library, restated for the stored
  black heights.\<close>

fun baliL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baliL (Node (Node t1 (a, (Red, _)) t2) (b, (Red, _)) t3) c t4 = R (B t1 a t2) b (B t3 c t4)" |
"baliL (Node t1 (a, (Red, _)) (Node t2 (b, (Red, _)) t3)) c t4 = R (B t1 a t2) b (B t3 c t4)" |
"baliL t1 a t2 = B t1 a t2"

fun baliR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"baliR t1 a (Node t2 (b, (Red, _)) (Node t3 (c, (Red, _)) t4)) = R (B t1 a t2) b (B t3 c t4)" |
"baliR t1 a (Node (Node t2 (b, (Red, _)) t3) (c, (Red, _)) t4) = R (B t1 a t2) b (B t3 c t4)" |
"baliR t1 a t2 = B t1 a t2"

lemma inv_baliL:
  "\<lbrakk> invh l; invh r; invc2 l; invc r; bh l = bh r \<rbrakk>
   \<Longrightarrow> invc (baliL l a r) \<and> invh (baliL l a r) \<and> bh (baliL l a r) = bh l + 1"
  by (induct l a r rule: baliL.induct) auto

lemma inv_baliR:
  "\<lbrakk> invh l; invh r; invc l; invc2 r; bh l = bh r \<rbrakk>
   \<Longrightarrow> invc (baliR l a r) \<and> invh (baliR l a r) \<and> bh (baliR l a r) = bh l + 1"
  by (induct l a r rule: baliR.induct) auto

lemma set_baliL: "set_tree (baliL l a r) = set_tree l \<union> {a} \<union> set_tree r"
  by (cases "(l,a,r)" rule: baliL.cases) auto

lemma set_baliR: "set_tree (baliR l a r) = set_tree l \<union> {a} \<union> set_tree r"
  by (cases "(l,a,r)" rule: baliR.cases) auto

lemma bst_baliL:
  "\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>x\<in>set_tree r. a < x\<rbrakk> \<Longrightarrow> bst (baliL l a r)"
  by (cases "(l,a,r)" rule: baliL.cases) (auto simp: ball_Un)

lemma bst_baliR:
  "\<lbrakk>bst l; bst r; \<forall>x\<in>set_tree l. x < a; \<forall>x\<in>set_tree r. a < x\<rbrakk> \<Longrightarrow> bst (baliR l a r)"
  by (cases "(l,a,r)" rule: baliR.cases) (auto simp: ball_Un)

lemma size_baliL: "size (baliL l a r) = size l + size r + 1"
  by (cases "(l,a,r)" rule: baliL.cases) auto

lemma size_baliR: "size (baliR l a r) = size l + size r + 1"
  by (cases "(l,a,r)" rule: baliR.cases) auto

subsection "Join for Red-Black Trees"

fun joinL :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"joinL l x r =
  (if bh r \<le> bh l then R l x r
   else case r of Node l' (x', (c, _)) r' \<Rightarrow>
     (if c = Black then baliL (joinL l x l') x' r' else R (joinL l x l') x' r'))"

fun joinR :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"joinR l x r =
  (if bh l \<le> bh r then R l x r
   else case l of Node l' (x', (c, _)) r' \<Rightarrow>
     (if c = Black then baliR l' x' (joinR r' x r) else R l' x' (joinR r' x r)))"

declare joinL.simps[simp del]
declare joinR.simps[simp del]

fun blacken :: "'a rbt \<Rightarrow> 'a rbt" where
"blacken (Node l (a, (Red, h)) r) =
  (if col l = Red \<or> col r = Red then B l a r else Node l (a, (Red, h)) r)" |
"blacken t = t"

fun join :: "'a rbt \<Rightarrow> 'a \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
"join l x r =
  (if bh r < bh l then blacken (joinR l x r)
   else if bh l < bh r then blacken (joinL l x r)
   else if col l = Black \<and> col r = Black then R l x r else B l x r)"

subsection "Proof of Correctness"

subsubsection "Colour and height invariants"

lemma inv_joinL:
  "\<lbrakk> invc l; invc r; invh l; invh r; bh l \<le> bh r \<rbrakk> \<Longrightarrow>
   invc2 (joinL l x r) \<and> (bh l \<noteq> bh r \<and> col r = Black \<longrightarrow> invc (joinL l x r))
   \<and> invh (joinL l x r) \<and> bh (joinL l x r) = bh r"
proof (induct l x r rule: joinL.induct)
  case (1 l x r)
  then show ?case
    by (auto simp: inv_baliL invc2I joinL.simps[of l x r] split!: tree.splits if_splits)
qed

lemma inv_joinR:
  "\<lbrakk> invc l; invc r; invh l; invh r; bh r \<le> bh l \<rbrakk> \<Longrightarrow>
   invc2 (joinR l x r) \<and> (bh l \<noteq> bh r \<and> col l = Black \<longrightarrow> invc (joinR l x r))
   \<and> invh (joinR l x r) \<and> bh (joinR l x r) = bh l"
proof (induct l x r rule: joinR.induct)
  case (1 l x r)
  then show ?case
    by (auto simp: inv_baliR invc2I joinR.simps[of l x r] split!: tree.splits if_splits)
qed

text \<open>A red root is passed upwards unchanged.\<close>

lemma col_joinL: "\<lbrakk>bh l < bh r; col r = Red\<rbrakk> \<Longrightarrow> col (joinL l x r) = Red"
  by (auto simp: joinL.simps[of l x r] split!: tree.splits if_splits)

lemma col_joinR: "\<lbrakk>bh r < bh l; col l = Red\<rbrakk> \<Longrightarrow> col (joinR l x r) = Red"
  by (auto simp: joinR.simps[of l x r] split!: tree.splits if_splits)

lemma inv_blacken: "\<lbrakk>invc2 t; invh t\<rbrakk> \<Longrightarrow> invc (blacken t) \<and> invh (blacken t)"
  by (cases t rule: blacken.cases) auto

lemma blacken_id: "invc t \<Longrightarrow> blacken t = t"
  by (cases t rule: blacken.cases) auto

lemma inv_join:
  assumes "rbt l" "rbt r"
  shows "rbt (join l x r)"
proof -
  have "rbt (blacken (joinR l x r))" if "bh r < bh l"
    using inv_joinR[of l r x] inv_blacken[of "joinR l x r"] assms that by auto
  moreover have "rbt (blacken (joinL l x r))" if "bh l < bh r"
    using inv_joinL[of l r x] inv_blacken[of "joinL l x r"] assms that by auto
  ultimately show ?thesis
    using assms by auto
qed

subsubsection "Set and search-tree properties"

lemma set_joinL: "set_tree (joinL l x r) = set_tree l \<union> {x} \<union> set_tree r"
proof (induction l x r rule: joinL.induct)
  case (1 l x r)
  then show ?case
    by (auto simp: set_baliL joinL.simps[of l x r] split!: tree.splits if_splits)
qed

lemma set_joinR: "set_tree (joinR l x r) = set_tree l \<union> {x} \<union> set_tree r"
proof (induction l x r rule: joinR.induct)
  case (1 l x r)
  then show ?case
    by (auto simp: set_baliR joinR.simps[of l x r] split!: tree.splits if_splits)
qed

lemma set_blacken: "set_tree (blacken t) = set_tree t"
  by (cases t rule: blacken.cases) auto

lemma set_join: "set_tree (join l x r) = set_tree l \<union> {x} \<union> set_tree r"
  by (auto simp: set_joinL set_joinR set_blacken)

lemma bst_joinL: "bst (Node l (a, n) r) \<Longrightarrow> bst (joinL l a r)"
proof (induction l a r rule: joinL.induct)
  case (1 l a r)
  then show ?case
    by (auto simp: set_baliL joinL.simps[of l a r] set_joinL ball_Un intro!: bst_baliL
             split!: tree.splits if_splits)
qed

lemma bst_joinR: "bst (Node l (a, n) r) \<Longrightarrow> bst (joinR l a r)"
proof (induction l a r rule: joinR.induct)
  case (1 l a r)
  then show ?case
    by (auto simp: set_baliR joinR.simps[of l a r] set_joinR ball_Un intro!: bst_baliR
             split!: tree.splits if_splits)
qed

lemma bst_blacken: "bst (blacken t) = bst t"
  by (cases t rule: blacken.cases) auto

lemma bst_join: "bst (Node l (a, n) r) \<Longrightarrow> bst (join l a r)"
  by (auto simp: bst_blacken bst_joinL bst_joinR)

subsubsection "Size"

lemma size_joinL: "size (joinL l x r) = size l + size r + 1"
proof (induction l x r rule: joinL.induct)
  case (1 l x r)
  then show ?case
    by (auto simp: size_baliL joinL.simps[of l x r] split!: tree.splits if_splits)
qed

lemma size_joinR: "size (joinR l x r) = size l + size r + 1"
proof (induction l x r rule: joinR.induct)
  case (1 l x r)
  then show ?case
    by (auto simp: size_baliR joinR.simps[of l x r] split!: tree.splits if_splits)
qed

lemma size_blacken: "size (blacken t) = size t"
  by (cases t rule: blacken.cases) auto

lemma join_size: "size (join l x r) = size l + size r + 1"
  by (auto simp: size_joinL size_joinR size_blacken)

text \<open>Functional correctness is established by instantiating @{locale Set2_Join}.\<close>

interpretation tree_rb: Set2_Join
where join = join and inv = rbt
proof (standard, goal_cases)
  case 1 show ?case by (rule set_join)
next
  case 2 then show ?case by (rule bst_join)
next
  case 3 show ?case by simp
next
  case 4 then show ?case by (rule inv_join)
next
  case (5 l a b r) then show ?case by (cases b) auto
qed

subsection "Proof of Strongly Joinable Properties"

definition rk :: "'a rbt \<Rightarrow> nat" where
"rk t = 2 * bh t + (if col t = Red then 1 else 0)"

lemma rk_Leaf[simp]: "rk Leaf = 0"
  by (simp add: rk_def)

lemma rk_Node[simp]: "rk (Node l (a, (c, h)) r) = 2 * h + (if c = Red then 1 else 0)"
  by (simp add: rk_def)

subsubsection "Balancing Rule"

lemma rk_children:
  assumes "rbt (Node l (a, (c, h)) r)"
  shows "max (rk l) (rk r) + 1 \<le> rk (Node l (a, (c, h)) r)"
    and "rk (Node l (a, (c, h)) r) \<le> min (rk l) (rk r) + 2"
  using assms by (cases c; cases "col l"; cases "col r"; simp add: rk_def)+

interpretation tree_rb: BalancedShape
where rank = "\<lambda>t. real (rk t)" and c\<^sub>l = 1 and c\<^sub>u = 2
  by (standard, goal_cases) auto

lemma rule_bal: "rbt t \<Longrightarrow> tree_rb.balanced t"
proof (induction t rule: tree2_induct)
  case (Node l a b r)
  obtain c h where b: "b = (c, h)"
    by (cases b)
  have "max (real (rk l)) (real (rk r)) + 1 \<le> real (rk (Node l (a, b) r))"
   and "real (rk (Node l (a, b) r)) \<le> min (real (rk l)) (real (rk r)) + 2"
    using rk_children[of l a c h r] Node.prems b
    by (simp_all flip: of_nat_max of_nat_min)
  then show ?case
    using Node b by auto
qed simp

interpretation tree_rb: BalancedTree
where rank = "\<lambda>t. real (rk t)" and c\<^sub>l = 1 and c\<^sub>u = 2 and inv = rbt
  by standard (rule rule_bal)

subsubsection "Monotonicity and Submodularity Rules"

lemma rk_blacken:
  assumes "invh t"
  shows "rk t \<le> rk (blacken t)" and "rk (blacken t) \<le> 2 * bh t + 2"
  using assms by (cases t rule: blacken.cases; simp)+

lemma rk_joinR:
  assumes "rbt l" "rbt r" "bh r < bh l"
  shows "max (rk l) (rk r) \<le> rk (blacken (joinR l x r))"
    and "rk (blacken (joinR l x r)) \<le> max (rk l) (rk r) + 1"
proof -
  let ?t = "joinR l x r"
  have t: "invc2 ?t" "col l = Black \<longrightarrow> invc ?t" "invh ?t" "bh ?t = bh l"
    using inv_joinR[of l r x] assms by auto
  have rk_t: "rk ?t = 2 * bh l + (if col ?t = Red then 1 else 0)"
    by (simp add: rk_def t(4))
  have rk_r: "rk r \<le> 2 * bh l"
    using assms(3) by (simp add: rk_def)
  show "max (rk l) (rk r) \<le> rk (blacken ?t)"
  proof (cases "col l")
    case Red
    then have "rk l = 2 * bh l + 1" and "col ?t = Red"
      using col_joinR[OF assms(3)] by (simp_all add: rk_def)
    then show ?thesis
      using rk_blacken(1)[OF t(3)] rk_t rk_r by simp
  next
    case Black
    then have "rk l = 2 * bh l"
      by (simp add: rk_def)
    then show ?thesis
      using rk_blacken(1)[OF t(3)] rk_t rk_r by simp
  qed
  show "rk (blacken ?t) \<le> max (rk l) (rk r) + 1"
  proof (cases "col l")
    case Red
    then have "rk l = 2 * bh l + 1"
      by (simp add: rk_def)
    then show ?thesis
      using rk_blacken(2)[OF t(3)] t(4) max.cobounded1[of "rk l" "rk r"] by linarith
  next
    case Black
    then have "rk l = 2 * bh l"
      by (simp add: rk_def)
    moreover have "rk (blacken ?t) = rk ?t"
      using blacken_id[OF t(2)[THEN mp, OF Black]] by simp
    moreover have "rk ?t \<le> 2 * bh l + 1"
      using rk_t by simp
    ultimately show ?thesis
      using max.cobounded1[of "rk l" "rk r"] by linarith
  qed
qed

lemma rk_joinL:
  assumes "rbt l" "rbt r" "bh l < bh r"
  shows "max (rk l) (rk r) \<le> rk (blacken (joinL l x r))"
    and "rk (blacken (joinL l x r)) \<le> max (rk l) (rk r) + 1"
proof -
  let ?t = "joinL l x r"
  have t: "invc2 ?t" "col r = Black \<longrightarrow> invc ?t" "invh ?t" "bh ?t = bh r"
    using inv_joinL[of l r x] assms by auto
  have rk_t: "rk ?t = 2 * bh r + (if col ?t = Red then 1 else 0)"
    by (simp add: rk_def t(4))
  have rk_l: "rk l \<le> 2 * bh r"
    using assms(3) by (simp add: rk_def)
  show "max (rk l) (rk r) \<le> rk (blacken ?t)"
  proof (cases "col r")
    case Red
    then have "rk r = 2 * bh r + 1" and "col ?t = Red"
      using col_joinL[OF assms(3)] by (simp_all add: rk_def)
    then show ?thesis
      using rk_blacken(1)[OF t(3)] rk_t rk_l by simp
  next
    case Black
    then have "rk r = 2 * bh r"
      by (simp add: rk_def)
    then show ?thesis
      using rk_blacken(1)[OF t(3)] rk_t rk_l by simp
  qed
  show "rk (blacken ?t) \<le> max (rk l) (rk r) + 1"
  proof (cases "col r")
    case Red
    then have "rk r = 2 * bh r + 1"
      by (simp add: rk_def)
    then show ?thesis
      using rk_blacken(2)[OF t(3)] t(4) max.cobounded2[of "rk r" "rk l"] by linarith
  next
    case Black
    then have "rk r = 2 * bh r"
      by (simp add: rk_def)
    moreover have "rk (blacken ?t) = rk ?t"
      using blacken_id[OF t(2)[THEN mp, OF Black]] by simp
    moreover have "rk ?t \<le> 2 * bh r + 1"
      using rk_t by simp
    ultimately show ?thesis
      using max.cobounded2[of "rk r" "rk l"] by linarith
  qed
qed

lemma rk_join:
  assumes "rbt l" "rbt r"
  shows "max (rk l) (rk r) \<le> rk (join l x r) \<and> rk (join l x r) \<le> max (rk l) (rk r) + 1"
proof -
  consider (R) "bh r < bh l" | (L) "bh l < bh r" | (EQ) "bh l = bh r"
    by linarith
  then show ?thesis
  proof cases
    case R
    then show ?thesis
      using rk_joinR[OF assms R] by simp
  next
    case L
    then show ?thesis
      using rk_joinL[OF assms L] by simp
  next
    case EQ
    then show ?thesis
      by (cases "col l"; cases "col r"; simp add: rk_def)
  qed
qed

lemmas rk_join_lower = rk_join[THEN conjunct1]
   and rk_join_upper = rk_join[THEN conjunct2]

corollary rule_mono:
  "\<lbrakk>rbt l; rbt r\<rbrakk> \<Longrightarrow> max (real (rk l)) (real (rk r)) \<le> real (rk (join l a r))"
  using rk_join_lower by (metis of_nat_le_iff of_nat_max)

lemma rule_sub:
  assumes "real (rk l') \<le> real (rk l) + x" "real (rk r') \<le> real (rk r) + x"
  assumes "rbt l'" "rbt r'" "rbt (Node l (a, b) r)"
  shows "real (rk (join l' a r')) \<le> real (rk (Node l (a, b) r)) + x"
proof -
  obtain c h where b: "b = (c, h)"
    by (cases b)
  have 1: "real (rk (join l' a r')) \<le> max (real (rk l')) (real (rk r')) + 1"
    using rk_join_upper[OF assms(3,4)]
    by (metis of_nat_le_iff of_nat_max of_nat_1 of_nat_add)
  have 2: "max (real (rk l')) (real (rk r')) \<le> max (real (rk l)) (real (rk r)) + x"
    using assms(1,2) by (auto simp: max_def)
  have 3: "max (real (rk l)) (real (rk r)) + 1 \<le> real (rk (Node l (a, b) r))"
    using rk_children(1)[of l a c h r] assms(5) b
    by (simp flip: of_nat_max)
  show ?thesis
    using 1 2 3 by linarith
qed

subsubsection "Cost Rule"

time_fun col
time_fun bh
time_fun R
time_fun B
time_fun baliL
time_fun baliR
time_fun blacken
time_fun joinL
time_fun joinR
time_fun join

lemma T_col_0[simp]: "T_col t = 0"
  by (cases t rule: tree2_cases) auto

lemma T_bh_0[simp]: "T_bh t = 0"
  by (cases t rule: tree2_cases) auto

lemma T_R_0[simp]: "T_R l a r = 0" and T_B_0[simp]: "T_B l a r = 0"
  by simp_all

lemma T_baliL_0[simp]: "T_baliL l a r = 0"
  by (induction l a r rule: baliL.induct) auto

lemma T_baliR_0[simp]: "T_baliR l a r = 0"
  by (induction l a r rule: baliR.induct) auto

lemma T_blacken_0[simp]: "T_blacken t = 0"
  by (cases t rule: blacken.cases) auto

declare T_joinL.simps[simp del]
declare T_joinR.simps[simp del]

lemma T_joinL:
  assumes "invc r" "invh r" "bh l \<le> bh r"
  shows "T_joinL l x r + 2 * bh l \<le> 2 * bh r + 1 + (if col r = Red then 1 else 0)"
  using assms
proof (induction r rule: tree2_induct)
  case Leaf
  then show ?case
    by (simp add: T_joinL.simps)
next
  case (Node l' x' b r')
  obtain c h where b: "b = (c, h)"
    by (cases b)
  let ?r = "Node l' (x', b) r'"
  show ?case
  proof (cases "bh ?r \<le> bh l")
    case True
    then show ?thesis
      using Node.prems(3) unfolding b
      by (simp add: T_joinL.simps[of l x "Node l' (x', (c, h)) r'"])
  next
    case False
    have T: "T_joinL l x ?r = T_joinL l x l' + 1"
      using False unfolding b
      by (simp add: T_joinL.simps[of l x "Node l' (x', (c, h)) r'"])
    have IH: "T_joinL l x l' + 2 * bh l \<le> 2 * bh l' + 1 + (if col l' = Red then 1 else 0)"
      using Node.IH(1) Node.prems False b by (auto split: if_splits)
    show ?thesis
      using IH T Node.prems b by (cases c; cases "col l'"; simp)
  qed
qed

lemma T_joinR:
  assumes "invc l" "invh l" "bh r \<le> bh l"
  shows "T_joinR l x r + 2 * bh r \<le> 2 * bh l + 1 + (if col l = Red then 1 else 0)"
  using assms
proof (induction l rule: tree2_induct)
  case Leaf
  then show ?case
    by (simp add: T_joinR.simps)
next
  case (Node l' x' b r')
  obtain c h where b: "b = (c, h)"
    by (cases b)
  let ?l = "Node l' (x', b) r'"
  show ?case
  proof (cases "bh ?l \<le> bh r")
    case True
    then show ?thesis
      using Node.prems(3) unfolding b
      by (simp add: T_joinR.simps[of "Node l' (x', (c, h)) r'" x r])
  next
    case False
    have T: "T_joinR ?l x r = T_joinR r' x r + 1"
      using False unfolding b
      by (simp add: T_joinR.simps[of "Node l' (x', (c, h)) r'" x r])
    have IH: "T_joinR r' x r + 2 * bh r \<le> 2 * bh r' + 1 + (if col r' = Red then 1 else 0)"
      using Node.IH(2) Node.prems False b by (auto split: if_splits)
    show ?thesis
      using IH T Node.prems b by (cases c; cases "col r'"; simp)
  qed
qed

lemma rule_cost_R:
  assumes "rbt l" "rbt r" "bh r < bh l"
  shows "T_join l x r + rk r \<le> rk l + 2"
proof -
  have "T_joinR l x r + 2 * bh r \<le> 2 * bh l + 1 + (if col l = Red then 1 else 0)"
    using T_joinR[of l r x] assms by simp
  moreover have "T_join l x r = T_joinR l x r"
    using assms(3) by simp
  ultimately show ?thesis
    by (cases "col l"; cases "col r"; simp add: rk_def)
qed

lemma rule_cost_L:
  assumes "rbt l" "rbt r" "bh l < bh r"
  shows "T_join l x r + rk l \<le> rk r + 2"
proof -
  have "T_joinL l x r + 2 * bh l \<le> 2 * bh r + 1 + (if col r = Red then 1 else 0)"
    using T_joinL[of r l x] assms by simp
  moreover have "T_join l x r = T_joinL l x r"
    using assms(3) by simp
  ultimately show ?thesis
    by (cases "col l"; cases "col r"; simp add: rk_def)
qed

lemma rule_cost_EQ: "bh l = bh r \<Longrightarrow> T_join l x r = 0"
  by simp

declare T_join.simps[simp del]

lemma rule_cost:
  assumes "rbt l" "rbt r"
  shows "real (T_join l x r) \<le> 2 + \<bar>real (rk l) - real (rk r)\<bar>"
proof -
  consider (R) "bh r < bh l" | (L) "bh l < bh r" | (EQ) "bh l = bh r"
    by linarith
  then show ?thesis
  proof cases
    case R
    have "real (T_join l x r) + real (rk r) \<le> real (rk l) + 2"
      using rule_cost_R[OF assms R, of x]
      by (metis of_nat_add of_nat_le_iff of_nat_numeral)
    then show ?thesis
      using abs_ge_self[of "real (rk l) - real (rk r)"] by linarith
  next
    case L
    have "real (T_join l x r) + real (rk l) \<le> real (rk r) + 2"
      using rule_cost_L[OF assms L, of x]
      by (metis of_nat_add of_nat_le_iff of_nat_numeral)
    then show ?thesis
      using abs_ge_minus_self[of "real (rk l) - real (rk r)"] by linarith
  next
    case EQ
    then show ?thesis
      by (simp add: rule_cost_EQ)
  qed
qed

subsection \<open>Instantiation of \<open>StronglyJoinable\<close>\<close>

interpretation tree_rb: StronglyJoinable
where join = join and inv = rbt
and rank = "\<lambda>t. real (rk t)" and c\<^sub>l = 1 and c\<^sub>u = 2
and T_join = T_join and k\<^sub>0 = 2 and k\<^sub>1 = 1
proof (standard, goal_cases)
  case (1 l r a)
  then show ?case
    by (rule rule_mono)
next
  case (2 l' l x r' r a b)
  then show ?case
    by (intro rule_sub)
next
  case (3 l a r)
  show ?case
    by (rule join_size)
next
  case (4 l r a)
  then show ?case
    using rule_cost[of l r a] by simp
next
  case 5
  then show ?case by simp
next
  case 6
  then show ?case by simp
qed

subsection \<open>Concrete constants for red-black trees\<close>

lemma rbt_c_delta: "tree_rb.c\<^sub>\<delta> = 1"
  unfolding tree_rb.c\<^sub>\<delta>_def by simp

lemma rbt_C: "tree_rb.C = 1"
  unfolding tree_rb.C_def by simp

lemma rbt_K_split: "tree_rb.K_split = 8"
  unfolding tree_rb.K_split_def by simp

lemma rbt_K_T: "tree_rb.K_T = 6"
  unfolding tree_rb.K_T_def by simp

lemma rbt_K_min: "tree_rb.K_min = 4"
  unfolding tree_rb.c\<^sub>1_def rbt_c_delta tree_rb.K_min_def by auto

lemma rbt_K_lin_union: "tree_rb.K_T * tree_rb.K_lin 2 3 \<le> 1856"
proof -
  have "tree_rb.K_T * tree_rb.K_lin 2 3 = 1134 + 510 * sqrt 2"
    unfolding tree_rb.K_lin_def
    by (simp add: rbt_K_T rbt_C rbt_K_split S1_two S2_two algebra_simps)
  also have "\<dots> \<le> 1134 + 510 * 1.415"
    using sqrt2_bounds(3) by (auto intro: add_left_mono mult_left_mono)
  also have "1134 + 510 * (1.415::real) \<le> 1856"
    by simp
  finally show ?thesis .
qed

lemma rbt_K_log_union: "tree_rb.K_T * tree_rb.K_log 2 3 \<le> 943"
proof -
  have "tree_rb.K_T * tree_rb.K_log 2 3 = 756 + 132 * sqrt 2"
    unfolding tree_rb.K_log_def
    by (simp add: rbt_K_T rbt_C rbt_K_split S1_two algebra_simps)
  also have "\<dots> \<le> 756 + 132 * 1.415"
    using sqrt2_bounds(3) by (auto intro: add_left_mono mult_left_mono)
  also have "756 + 132 * (1.415::real) \<le> 943"
    by simp
  finally show ?thesis .
qed

lemma rbt_K_lin_inter: "tree_rb.K_T * tree_rb.K_lin 16 12 \<le> 3333"
proof -
  have "tree_rb.K_T * tree_rb.K_lin 16 12 = 2034 + 918 * sqrt 2"
    unfolding tree_rb.K_lin_def
    by (simp add: rbt_K_T rbt_C rbt_K_split S1_two S2_two algebra_simps)
  also have "\<dots> \<le> 2034 + 918 * 1.415"
    using sqrt2_bounds(3) by (auto intro: add_left_mono mult_left_mono)
  also have "2034 + 918 * (1.415::real) \<le> 3333"
    by simp
  finally show ?thesis .
qed

lemma rbt_K_log_inter: "tree_rb.K_T * tree_rb.K_log 16 12 \<le> 1696"
proof -
  have "tree_rb.K_T * tree_rb.K_log 16 12 = 1356 + 240 * sqrt 2"
    unfolding tree_rb.K_log_def
    by (simp add: rbt_K_T rbt_C rbt_K_split S1_two algebra_simps)
  also have "\<dots> \<le> 1356 + 240 * 1.415"
    using sqrt2_bounds(3) by (auto intro: add_left_mono mult_left_mono)
  also have "1356 + 240 * (1.415::real) \<le> 1696"
    by simp
  finally show ?thesis .
qed

corollary rbt_T_union_linlog:
  assumes "rbt t1" "rbt t2"
  shows "real (tree_rb.T_union t1 t2)
       \<le> 6 + 1856 * size_min t1 t2
         + 943 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (tree_rb.T_union t1 t2)
      \<le> tree_rb.K_T + (tree_rb.K_T * tree_rb.K_lin 2 3) * size_min t1 t2
        + (tree_rb.K_T * tree_rb.K_log 2 3)
          * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using tree_rb.T_union_bound[OF assms]
    by (simp add: rbt_c_delta)
  also have "\<dots> \<le> 6 + 1856 * size_min t1 t2
        + 943 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using rbt_K_lin_union rbt_K_log_union rbt_K_T
    by (intro add_mono mult_right_mono) (auto simp: log_def)
  finally show ?thesis .
qed

corollary rbt_T_inter_linlog:
  assumes "rbt t1" "rbt t2"
  shows "real (tree_rb.T_inter t1 t2)
       \<le> 6 + 3333 * size_min t1 t2
         + 1696 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (tree_rb.T_inter t1 t2)
      \<le> tree_rb.K_T + (tree_rb.K_T * tree_rb.K_lin 16 12) * size_min t1 t2
        + (tree_rb.K_T * tree_rb.K_log 16 12)
          * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using tree_rb.T_inter_bound[OF assms]
    by (simp add: rbt_K_min)
  also have "\<dots> \<le> 6 + 3333 * size_min t1 t2
        + 1696 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using rbt_K_lin_inter rbt_K_log_inter rbt_K_T
    by (intro add_mono mult_right_mono) (auto simp: log_def)
  finally show ?thesis .
qed

corollary rbt_T_diff_linlog:
  assumes "rbt t1" "rbt t2"
  shows "real (tree_rb.T_diff t1 t2)
       \<le> 6 + 3333 * size_min t1 t2
         + 1696 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (tree_rb.T_diff t1 t2)
      \<le> tree_rb.K_T + (tree_rb.K_T * tree_rb.K_lin 16 12) * size_min t1 t2
        + (tree_rb.K_T * tree_rb.K_log 16 12)
          * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using tree_rb.T_diff_bound[OF assms]
    by (simp add: rbt_K_min)
  also have "\<dots> \<le> 6 + 3333 * size_min t1 t2
        + 1696 * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    using rbt_K_lin_inter rbt_K_log_inter rbt_K_T
    by (intro add_mono mult_right_mono) (auto simp: log_def)
  finally show ?thesis .
qed

corollary rbt_T_union_bigo:
  "(\<lambda>(t1, t2). real (tree_rb.T_union t1 t2)) \<in> O[tree_rb.tree_pair_filter](\<lambda>(t1, t2).
     size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
  using tree_rb.T_union_bigo .

corollary rbt_T_inter_bigo:
  "(\<lambda>(t1, t2). real (tree_rb.T_inter t1 t2)) \<in> O[tree_rb.tree_pair_filter](\<lambda>(t1, t2).
     size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
  using tree_rb.T_inter_bigo .

corollary rbt_T_diff_bigo:
  "(\<lambda>(t1, t2). real (tree_rb.T_diff t1 t2)) \<in> O[tree_rb.tree_pair_filter](\<lambda>(t1, t2).
     size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
  using tree_rb.T_diff_bigo .

end
