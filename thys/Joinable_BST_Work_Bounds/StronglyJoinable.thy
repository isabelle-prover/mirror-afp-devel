section \<open>Strongly Joinable Trees\<close>

theory StronglyJoinable
imports
  "Analytical"
  "BalancedBinary"
  "HOL-Data_Structures.Set2_Join"
  "HOL-Library.Time_Commands"
  "HOL-Library.Landau_Symbols"
  "HOL-Library.Going_To_Filter"
begin

text \<open>
  The @{text "StronglyJoinable"} locale combines the functional correctness setting of
  @{locale "Set2_Join"} with the balancing scheme of @{locale "BalancedTree"} and adds
  the remaining strongly joinable rules of \<^cite>\<open>blelloch2022joinable\<close>:

  \<^item> \<open>rule_mono\<close>: the rank of a join dominates the ranks of both arguments
  \<^item> \<open>rule_sub\<close>: replacing the subtrees of a node by trees whose rank exceeds
    the original by at most \<open>x\<close> yields a join whose rank exceeds the rank of the
    original node by at most \<open>x\<close>
  \<^item> \<open>rule_cost\<close>: the cost of a join is linear in the
    rank difference of its arguments\<close>

text \<open>
  The submodularity rule \<open>rule_sub\<close> deviates from the definition in
  \<^cite>\<open>blelloch2022joinable\<close>. The reason is support for flag-free \<open>join\<close>
  implementations of the type fixed by @{locale Set2_Join} and the price is a larger constant in 
  the lower bound on the rank of union. See the appendix for details.

  Finally, the added sanity rule \<open>join_size\<close> demands that \<open>join\<close> is not
  degenerate i.e. it adds exactly the pivot element and nothing else. Under
  \<open>bst\<close> preconditions this is already implied by functional correctness, but
  stating it directly avoids threading the \<open>bst\<close> assumption through the entire
  work analysis. It trivially holds for any correct implementation of \<open>join\<close>.

  Note that for \<open>rule_cost\<close> there is no guarantee that \<open>T_join\<close> is the actual 
  timing function corresponding to \<open>join\<close>. The analysis is therefore stated 
  relative to the function supplied by an instantiation.

  The final bounds are stated in terms of the smaller size $m$ and the larger size $n$ of
  the two inputs.
  \<close>

abbreviation size_min :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> real" where
  "size_min ta tb \<equiv> real (min (size1 ta) (size1 tb))"
abbreviation size_max :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> real" where
  "size_max ta tb \<equiv> real (max (size1 ta) (size1 tb))"

locale StronglyJoinable =
  Set2_Join join inv +
  BalancedTree rank c\<^sub>l c\<^sub>u inv
  for rank :: "('a::linorder * 'b) tree \<Rightarrow> real"
  and c\<^sub>l c\<^sub>u :: real 
  and join :: "('a*'b) tree \<Rightarrow> 'a \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree"
  and inv :: "('a*'b) tree \<Rightarrow> bool"
  +
  fixes T_join :: "('a*'b) tree \<Rightarrow> 'a \<Rightarrow> ('a*'b) tree \<Rightarrow> nat"
  and k\<^sub>0 k\<^sub>1 :: real
  assumes rule_mono:
    "\<lbrakk>inv l; inv r\<rbrakk> \<Longrightarrow> max (rank l) (rank r) \<le> rank (join l a r)"
  assumes rule_sub:
    "\<lbrakk> rank l' \<le> rank l + x; rank r' \<le> rank r + x;
       inv l'; inv r'; inv (Node l (a,b) r) \<rbrakk> \<Longrightarrow>
       rank (join l' a r') \<le> rank (Node l (a,b) r) + x"
   assumes join_size: "\<lbrakk>inv l; inv r\<rbrakk> \<Longrightarrow> size (join l a r) = size l + size r + 1"
   assumes rule_cost:
     "\<lbrakk>inv l; inv r\<rbrakk> \<Longrightarrow> real (T_join l a r) \<le> k\<^sub>0 + k\<^sub>1 * \<bar>rank l - rank r\<bar>"
   assumes k\<^sub>0_nonneg: "0 \<le> k\<^sub>0"
   assumes k\<^sub>1_nonneg: "0 \<le> k\<^sub>1"
begin

lemma split_invL[dest]: "\<lbrakk>split x t = (l,b,r); inv t\<rbrakk> \<Longrightarrow> inv l"
  using split_inv by blast

lemma split_invR[dest]: "\<lbrakk>split x t = (l,b,r); inv t\<rbrakk> \<Longrightarrow> inv r"
  using split_inv by blast

lemma split_invL_sym[dest]: "\<lbrakk>(l,b,r) = split x t; inv t\<rbrakk> \<Longrightarrow> inv l"
  using split_invL by metis

lemma split_invR_sym[dest]: "\<lbrakk>(l,b,r) = split x t; inv t\<rbrakk> \<Longrightarrow> inv r"
  using split_invR by metis

lemma obtain_inv[elim]:
assumes "inv (Node l (x,y) r)"
obtains "inv l" "inv r"
  using assms inv_Node by blast

text \<open>The decreasing side of the submodularity rule of \<^cite>\<open>blelloch2022joinable\<close>
  is the instance \<open>x = 0\<close>.\<close>

lemma rule_sub_dec:
  "\<lbrakk> rank l' \<le> rank l; rank r' \<le> rank r; inv l'; inv r'; inv (Node l (a,b) r) \<rbrakk> \<Longrightarrow>
     rank (join l' a r') \<le> rank (Node l (a,b) r)"
  using rule_sub[of l' l 0 r' r a b] by simp

text \<open>Since \<open>join\<close> can build a tree of any size out of the empty tree, the invariant
  holds for a singleton node with any pivot. Applying \<open>rule_sub\<close> to such a node bounds
  the rank increase of any join by a constant \<^cite>\<open>\<open>Property 6\<close> in blelloch2022joinable\<close>.\<close>

lemma inv_singleton: "\<exists>b. inv (Node Leaf (a,b) Leaf)"
proof -
  have "inv (join Leaf a Leaf)" and "size (join Leaf a Leaf) = 1"
    by (auto simp: inv_Leaf inv_join join_size)
  moreover have "set_tree (join Leaf a Leaf) = {a}"
    by simp
  ultimately show ?thesis
    by (cases "join Leaf a Leaf") auto
qed

lemma join_rank_upper:
  assumes "inv l" "inv r"
  shows "rank (join l a r) \<le> max (rank l) (rank r) + c\<^sub>u"
proof -
  obtain b where inv_s: "inv (Node Leaf (a,b) Leaf)"
    using inv_singleton by blast
  then have "rank (Node Leaf (a,b) Leaf) \<le> c\<^sub>u"
    using inv_children_explD(3)[OF inv_s] rule_empty by simp
  moreover have "rank (join l a r) \<le> rank (Node Leaf (a,b) Leaf) + max (rank l) (rank r)"
    using rule_sub rule_empty assms inv_s by force
  ultimately show ?thesis
    by argo
qed

subsection \<open>Work model for @{term join}\<close>

text \<open>
  All following work analyses are carried out against the idealized work measures
  in which every @{term join} is charged exactly
  @{term "W_join l a r"}. Through @{thm [source] rule_cost} every generated time 
  function is bounded by a constant multiple of its work-model counterpart. 
  It would be possible to use @{term T_join} directly,
  but the actual bounds will be calculated via real analysis, rather than just summation
  in @{term nat}. This way the constants do not need to be dragged around and conversions
  between @{term nat} and @{term real} happen exactly once.
  \<close>

definition W_join :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> ('a * 'b) tree \<Rightarrow> real" where
"W_join l a r = \<bar>rank l - rank r\<bar>"

definition K_T :: real where
"K_T = 1 + 2 * k\<^sub>0 + k\<^sub>1"

lemma K_T_ge_1: "1 \<le> K_T"
  using k\<^sub>0_nonneg k\<^sub>1_nonneg by (simp add: K_T_def)

lemma K_T_ge_k1: "k\<^sub>1 \<le> K_T"
  using k\<^sub>0_nonneg by (simp add: K_T_def)

lemma K_T_ge_1_plus_k0: "1 + k\<^sub>0 \<le> K_T"
  using k\<^sub>0_nonneg k\<^sub>1_nonneg by (simp add: K_T_def)

lemma W_join_nonneg[simp]: "0 \<le> W_join l a r"
  by (simp add: W_join_def)

lemma rule_cost_W:
  "\<lbrakk>inv l; inv r\<rbrakk> \<Longrightarrow> real (T_join l a r) \<le> k\<^sub>0 + k\<^sub>1 * W_join l a r"
  by (simp add: W_join_def rule_cost)

subsection \<open>Work bounds of helper functions\<close>
subsubsection \<open>@{term "split"}\<close>

text \<open>First, show that  @{term "split"} can be decomposed into two functions,
computing the left and right subtree respectively.\<close>

fun splitl :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> ('a * 'b) tree" where
"splitl Leaf x = Leaf" |
"splitl (Node l (a,_) r) x = (case (cmp x a) of
   LT \<Rightarrow> splitl l x |
   EQ \<Rightarrow> l |
   GT \<Rightarrow> join l a (splitl r x))"

fun splitr :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> ('a * 'b) tree" where
"splitr Leaf x = Leaf" |
"splitr (Node l (a, _) r) x = (case (cmp x a) of
   LT \<Rightarrow> join (splitr l x) a r |
   EQ \<Rightarrow> r |
   GT \<Rightarrow> splitr r x)"

lemma splitl_eq_l:"split x t = (l,b,r) \<Longrightarrow> splitl t x = l"
  by(induction t arbitrary: l b r)(auto simp: split.simps split!: prod.splits)
  
lemma splitr_eq_r:"split x t = (l,b,r) \<Longrightarrow> splitr t x = r"
  by(induction t arbitrary: l b r)(auto simp: split.simps split!: prod.splits)

corollary splitl_fst: "splitl t x = fst (split x t)"
  using splitl_eq_l by (cases "split x t") force

corollary splitr_snd: "splitr t x = snd (snd (split x t))"
  using splitr_eq_r by (cases "split x t") force

corollary inv_splitl:"inv t \<Longrightarrow> inv (splitl t x)"
  by (metis split_inv splitl_eq_l prod_cases3)

corollary inv_splitr:"inv t \<Longrightarrow> inv (splitr t x)"
  by (metis split_inv splitr_eq_r prod_cases3)

text \<open>The submodularity rule guarantees that the rank of either result trees can
never exceed the rank of the original input tree.\<close>

lemma splitl_rank:"inv t \<Longrightarrow> rank t \<ge> rank (splitl t x)"
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by simp
next
  case (Node l a b r)
  then have t_bal:"balanced (Node l (a,b) r)"
    using rule_bal by fast

  then show ?case 
  proof(cases "cmp x a")
    case GT
    have "rank r \<ge> rank (splitl r x)"
      using Node inv_Node by blast
    moreover have "rank l \<ge> rank l"
      by simp
    ultimately have "rank (Node l (a,b) r) \<ge> rank (join l a (splitl r x))"
      by (meson Node.prems inv_Node rule_sub_dec inv_splitl)
    then show ?thesis 
      using GT by simp
  qed (use Node t_bal c_vals in auto)
qed

lemma splitr_rank:"inv t \<Longrightarrow> rank t \<ge> rank (splitr t x)"
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by simp
next
  case (Node l a b r)
  then have t_bal:"balanced (Node l (a,b) r)"
    using rule_bal by fast
  then show ?case 
  proof(cases "cmp x a")
    case LT
    have "rank l \<ge> rank (splitr l x)"
      using Node inv_Node by blast
    moreover have "rank r \<ge> rank r"
      by simp
    ultimately have "rank (Node l (a,b) r) \<ge> rank (join (splitr l x) a r)"
      by (meson Node.prems inv_Node rule_sub_dec inv_splitr)
    then show ?thesis 
      using LT by simp
  qed (use Node t_bal c_vals in auto)
qed

corollary split_rank: "\<lbrakk>split x t = (l,b,r); inv t\<rbrakk> \<Longrightarrow> rank l \<le> rank t \<and> rank r \<le> rank t"
  using splitl_eq_l splitl_rank splitr_eq_r splitr_rank by blast

text \<open>At most one of the two results of a split can retain the full rank of the input.
  Splitting at the root returns the two subtrees, and otherwise the recursion descends
  into one subtree, whose share of the result is bounded by that subtree's rank.\<close>

lemma split_rank_min:
  assumes "inv t" "t \<noteq> Leaf" "split x t = (l, b, r)"
  shows "min (rank l) (rank r) \<le> rank t - c\<^sub>l"
proof -
  obtain tl a c tr where t: "t = Node tl (a,c) tr"
    using assms(2) by (cases t rule: tree2_cases) auto
  moreover have inv_sub: "inv tl" "inv tr"
    using assms(1) t inv_Node by blast+
  moreover have bl: "rank tl \<le> rank t - c\<^sub>l" "rank tr \<le> rank t - c\<^sub>l"
    using inv_children_explD assms t by auto
  moreover have l_eq: "l = splitl t x" and r_eq: "r = splitr t x"
    using assms(3) splitl_eq_l splitr_eq_r by auto
  ultimately show ?thesis
  by (cases "cmp x a") 
     (use splitl_rank splitr_rank splitl.simps in auto; metis min.absorb1 min_le_iff_disj)+
qed

text \<open>Furthermore, since @{term "split"} can only partition keys,
the combined sizes of the results never exceed the size of the input.\<close>

lemma split_size_sum:
  "\<lbrakk>(l, b, r) = split x t; inv t\<rbrakk> \<Longrightarrow>
     inv l \<and> inv r \<and> size t = size l + size r + (if b then 1 else 0)"
  by (induction t arbitrary: l b r rule: split.induct)
     (auto simp: split.simps join_size inv_join inv_Leaf dest!: inv_Node
        split: cmp_val.splits prod.splits if_splits)

corollary split_size: "\<lbrakk>(l, b, r) = split x t; inv t\<rbrakk> \<Longrightarrow> size l + size r \<le> size t"
using split_size_sum by simp

text \<open>And exactly one element is removed if the split key was contained in the original tree.\<close>

lemma split_size_true:
  "\<lbrakk>(l, True, r) = split x t; inv t\<rbrakk> \<Longrightarrow> size l + size r = size t - 1"
  using split_size_sum by simp

text \<open>The work of @{term "split"} is also partitioned by the work of computing the
left/right result.\<close>

fun W_split :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> real" where
"W_split Leaf x = 1" |
"W_split (Node l (a,_) r) x = (case (cmp x a) of
   LT \<Rightarrow> let (l1,_,l2) = split x l in 1 + W_join l2 a r + W_split l x |
   EQ \<Rightarrow> 1 |
   GT \<Rightarrow> let (r1,_,r2) = split x r in 1 + W_join l a r1 + W_split r x)"

fun W_splitl :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> real" where
"W_splitl Leaf x = 1" |
"W_splitl (Node l (a,_) r) x = (case (cmp x a) of
   LT \<Rightarrow> W_splitl l x |
   EQ \<Rightarrow> 1 |
   GT \<Rightarrow> 1 + W_join l a (splitl r x) + W_splitl r x)"

fun W_splitr :: "('a * 'b) tree \<Rightarrow> 'a \<Rightarrow> real" where
"W_splitr Leaf x = 1" |
"W_splitr (Node l (a,_) r) x = (case (cmp x a) of
   LT \<Rightarrow> 1 + W_join (splitr l x) a r + W_splitr l x |
   EQ \<Rightarrow> 1 |
   GT \<Rightarrow> W_splitr r x)"

lemma W_split_lr:"W_split t x \<le> W_splitl t x + W_splitr t x"
  by (induction t rule: tree2_induct)
     (auto simp: splitl_fst splitr_snd split: cmp_val.splits prod.splits)

text \<open>
  The bound on @{term W_splitl} is proved directly by induction, without the intermediary
  sum used in \<^cite>\<open>blelloch2022joinable\<close>. The key observation is an inverse relationship
  between the cost of a single join and the cost accumulated along the recursion path.
  At each recursive call, @{term W_splitl} computes @{term "splitl r x"} and then joins the
  result with @{term l}. Writing @{term "r' = splitl r x"}:

  \<^item> If @{term "rank r'"} is small (extreme: @{term "rank r' = 0"}), the join
    @{term "W_join l a r'"} is expensive (up to @{term "rank l"}), but by the monotonicity
    rule no expensive joins can have occurred along the path, so the accumulated cost is low
  \<^item> If @{term "rank r'"} is large (extreme: @{term "rank r' = rank r"}), the join cost
    decreases, while the accumulated path cost may be higher\<close>

text\<open>
  This tradeoff is captured by an induction hypothesis which introduces 
  @{term "rank (splitl t x)"} to absorb the credit left by cheap joins.
\<close>

definition "c\<^sub>1 = 2 * c\<^sub>\<delta> + 1"

lemma c1_pos:"c\<^sub>1 > 0"
  using c\<^sub>1_def c\<^sub>\<delta>_def c_vals by linarith

lemma W_splitl_bounded:
assumes "inv t"
shows "W_splitl t x \<le> 1 + c\<^sub>1 * height t + rank (splitl t x)"
using assms
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by (simp add: rule_empty)
next
  case (Node l a b r)
  let ?t = "(Node l (a,b) r)"

  have t_bal:"balanced ?t"
    using rule_bal Node by fast
  
  have inv_subtrees:"inv l \<and> inv r"
    using Node inv_Node by blast
  show ?case 
  proof(cases "cmp x a")
    case LT
    \<comment> \<open>follows directly from the IH\<close>
    have *:"height l \<le> height ?t"
      by simp
    have "W_splitl ?t x \<le> 1 + c\<^sub>1 * height l + rank (splitl ?t x)"
      using LT Node inv_subtrees by force
    also have "... \<le> 1 + c\<^sub>1 * height ?t + rank (splitl ?t x)"
      using c1_pos by simp
    finally show ?thesis .
  next
    case EQ
    then show ?thesis 
      using c1_pos inv_subtrees rank_pos rule_bal by auto 
  next
    case GT
    \<comment> \<open>since the rank of the split result is bounded\<close>
    have "rank r \<ge> rank (splitl r x)"
      using Node splitl_rank inv_subtrees by blast
    \<comment> \<open>and the tree is balanced\<close>
    then have "rank l + c\<^sub>\<delta> \<ge> rank (splitl r x)"
      using Node t_bal c\<^sub>\<delta>_def by force
    \<comment> \<open>there must be some \<open>\<delta>\<close> that satisfies the equation below\<close>
    moreover obtain \<delta> where hdiff:"rank l + c\<^sub>\<delta> = rank (splitl r x) + \<delta>"
      by (metis add.commute diff_add_cancel)
    \<comment> \<open>thus the time to join is bounded\<close>
    ultimately have "W_join l a (splitl r x) \<le> c\<^sub>\<delta> + \<delta>"
      using W_join_def c\<^sub>\<delta>_def c_vals by force
    \<comment> \<open>since \<open>x > a\<close>\<close>
    moreover have "W_splitl ?t x \<le> 1 + W_join l a (splitl r x) + W_splitl r x"
      using GT by simp
    \<comment> \<open>plugging in the bound for \<open>W_join l a (splitl r x)\<close>\<close>
    ultimately have "W_splitl ?t x \<le> 1 + c\<^sub>\<delta> + \<delta> + W_splitl r x"
      by simp
    \<comment> \<open>applying the induction hypothesis\<close>
    then have "W_splitl ?t x \<le> 1 + c\<^sub>\<delta> + \<delta> + 1 + c\<^sub>1 * height r + rank (splitl r x)"
      using Node inv_subtrees by fastforce
    \<comment> \<open>expressing @{term "rank (splitl t x)"} in terms of @{term "rank l + c\<^sub>\<delta>"} and @{term \<delta>}\<close>
    also have "... \<le> 1 + c\<^sub>\<delta> + \<delta> + 1 + c\<^sub>1 * height r + rank l + c\<^sub>\<delta> - \<delta>"
      using hdiff by simp
    \<comment> \<open>simplifying the expression\<close>
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height r + rank l"
      by simp
    \<comment> \<open>from the monotonicity rule\<close>
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height r + rank (splitl ?t x)"
      using inv_subtrees inv_splitl rule_mono inv_subtrees GT by fastforce
    \<comment> \<open>from the definition of height\<close>
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height ?t - c\<^sub>1 + rank (splitl ?t x)"
      using c1_pos by (simp add: distrib_left)
    \<comment> \<open>finally, because @{term "c\<^sub>1 = 2 * c\<^sub>\<delta> + 1"}\<close>
    also have "... \<le> 1 + c\<^sub>1 * height ?t + rank (splitl ?t x)"
      by (simp add: c\<^sub>1_def)
    finally show ?thesis .
  qed
qed

text \<open>The right side is mirrored.\<close>

lemma W_splitr_bounded:
assumes "inv t"
shows "W_splitr t x \<le> 1 + c\<^sub>1 * height t + rank (splitr t x)"
using assms
proof(induction t rule: tree2_induct)
  case Leaf
  then show ?case 
    by (simp add: rule_empty)
next
  case (Node l a b r)
  let ?t = "(Node l (a,b) r)"

  have t_bal:"balanced ?t"
    using rule_bal Node by fast
  
  have inv_subtrees:"inv l \<and> inv r"
    using Node inv_Node by blast
  show ?case 
  proof(cases "cmp x a")
    case LT
    have "rank l \<ge> rank (splitr l x)"
      using Node splitr_rank inv_subtrees by blast
    then have "rank r + c\<^sub>\<delta> \<ge> rank (splitr l x)"
      using Node t_bal c\<^sub>\<delta>_def by force
    then obtain \<delta> where hdiff:"rank r + c\<^sub>\<delta> = rank (splitr l x) + \<delta>"
      by (metis add.commute diff_add_cancel)
    then have "W_join (splitr l x) a r \<le> c\<^sub>\<delta> + \<delta>"
      using W_join_def hdiff using \<open>rank (splitr l x) \<le> rank r + c\<^sub>\<delta>\<close> c\<^sub>\<delta>_def c_vals by force
    then have "W_splitr ?t x \<le> 1 + c\<^sub>\<delta> + \<delta> + 1 + c\<^sub>1 * height l + rank (splitr l x)"
      using Node LT inv_subtrees by fastforce
    also have "... \<le> 1 + c\<^sub>\<delta> + \<delta> + 1 + c\<^sub>1 * height l + rank r + c\<^sub>\<delta> - \<delta>"
      using hdiff by simp
    also have "... \<le> 2 + 2*c\<^sub>\<delta>  + c\<^sub>1 * height l + rank r"
      by simp
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height l + rank (splitr ?t x)"
      using inv_subtrees inv_splitr rule_mono inv_subtrees LT by fastforce
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height ?t - c\<^sub>1 + rank (splitr ?t x)"
      using c1_pos by (simp add: distrib_left)
    finally show ?thesis 
      by (simp add: c\<^sub>1_def)
  next
    case EQ
    then show ?thesis 
      using c1_pos inv_subtrees rank_pos rule_bal by auto
  next
    case GT
    have *:"height r \<le> height ?t"
      by simp
    have "W_splitr ?t x \<le> 1 + c\<^sub>1 * height r + rank (splitr ?t x)"
      using GT Node inv_subtrees by auto
    also have "... \<le> 1 + c\<^sub>1 * height ?t + rank (splitr ?t x)"
      by (simp add: c1_pos)
    finally show ?thesis .
  qed
qed

text \<open>Combining both yields the work bound of @{term "split"}.\<close>
definition K_split where 
"K_split = (4 * c\<^sub>u - 2 * c\<^sub>l + 2) / c\<^sub>l"

lemma K_split_pos: "K_split > 0"
  unfolding K_split_def using c_vals by fastforce

lemma K_split_ge_1: "K_split \<ge> 1"
  unfolding K_split_def using c_vals by fastforce

theorem W_split_bounded: 
assumes "inv t"
shows "W_split t x \<le> 2 + K_split * rank t"
proof -
  have "c\<^sub>1 * height t \<le> c\<^sub>1 * (rank t / c\<^sub>l)"
    using rank_lower_height_inverse'[OF assms] c1_pos
    by (intro mult_left_mono) auto
  then have "W_split t x \<le> 2 + 2 * (c\<^sub>1 * (rank t / c\<^sub>l)) + 2 * rank t"
    using W_split_lr[of t x] W_splitl_bounded[OF assms, of x] W_splitr_bounded[OF assms, of x]
      splitl_rank[OF assms, of x] splitr_rank[OF assms, of x] by linarith
  also have "\<dots> = 2 + K_split * rank t"
    unfolding K_split_def c\<^sub>1_def c\<^sub>\<delta>_def using c_vals by (simp add: field_simps)
  finally show ?thesis .
qed

text \<open>Finally the generated @{term T_split} is bounded by its work-function equivalent.\<close>

time_fun cmp

time_fun split equations split.simps

lemma W_split_ge_1: "1 \<le> W_split t x"
  by (induction t rule: tree2_induct)
     (auto simp: W_join_def split: cmp_val.splits prod.splits)

lemma rule_cost_step:
  assumes "inv l" "inv r" and "real t \<le> (1 + k\<^sub>0 + k\<^sub>1) * w"
  shows "1 + (real t + real (T_join l a r)) \<le> (1 + k\<^sub>0 + k\<^sub>1) * (1 + W_join l a r + w)"
proof -
  have "1 + (real t + real (T_join l a r))
        \<le> (1 + k\<^sub>0) + k\<^sub>1 * W_join l a r + (1 + k\<^sub>0 + k\<^sub>1) * w"
    using rule_cost_W[OF assms(1,2), where a=a] assms(3) by linarith
  also have "\<dots> \<le> (1 + k\<^sub>0 + k\<^sub>1) + (1 + k\<^sub>0 + k\<^sub>1) * W_join l a r + (1 + k\<^sub>0 + k\<^sub>1) * w"
    using k\<^sub>0_nonneg k\<^sub>1_nonneg by (simp add: add_increasing mult_right_mono)
  also have "\<dots> = (1 + k\<^sub>0 + k\<^sub>1) * (1 + W_join l a r + w)"
    by algebra
  finally show ?thesis .
qed

lemma T_split_bridge_strong:
  "inv t \<Longrightarrow> real (T_split x t) \<le> (1 + k\<^sub>0 + k\<^sub>1) * W_split t x"
  using k\<^sub>0_nonneg k\<^sub>1_nonneg 
  by(induction x t rule: T_split.induct)
    (auto simp: split_inv intro!: rule_cost_step split: cmp_val.splits prod.splits)

corollary T_split_bridge:
  assumes "inv t"
  shows "real (T_split x t) \<le> K_T * W_split t x"
proof -
  have "(1 + k\<^sub>0 + k\<^sub>1) * W_split t x \<le> K_T * W_split t x"
    using W_split_ge_1[of t x] k\<^sub>0_nonneg unfolding K_T_def by auto
  then show ?thesis
    using T_split_bridge_strong[OF assms] by (metis max.absorb2 max.bounded_iff)
qed

subsubsection \<open>@{term split_min}\<close>

text \<open>@{term split_min} removes the minimum element from a tree.
  The rank of the resulting tree stays close to the original i.e. it can decrease
  but not drop by more than @{term c\<^sub>u}.\<close>

lemma split_min_rank:
  assumes "inv t" "split_min t = (m, t')" "t \<noteq> Leaf"
  shows "rank t \<ge> rank t'"
using assms proof(induction t arbitrary: t' rule: tree2_induct)
  case Leaf then show ?case 
    by auto
next
  case (Node l a b r)
  let ?t = "Node l (a,b) r"
  have inv_sub: "inv l" "inv r" 
    using Node inv_Node by blast+
  show ?case
  proof (cases "l = Leaf")
    case True
    then show ?thesis 
      using Node.prems(1,2) split_min.simps c_vals inv_children_explD(2) by force
  next
    case False
    then obtain m' l' where SmL: "split_min l = (m', l')"
                      and inv_l': "inv l'" 
      by (metis split_min_inv False inv_sub(1) old.prod.exhaust)
    then have "rank l \<ge> rank l'" 
      using Node False inv_sub by auto 
    moreover have "t' = join l' a r" 
      using Node False SmL by auto
    ultimately show ?thesis 
      by (simp add: Node.prems(1) inv_l' inv_sub(2) rule_sub_dec)
  qed
qed

lemma split_min_rank_min:
  assumes "inv t" "split_min t = (m, t')" "t \<noteq> Leaf"
  shows "rank t \<le> rank t' + c\<^sub>u"
using assms proof(induction t arbitrary: t' rule: tree2_induct)
  case Leaf then show ?case by auto
next
  case (Node l a b r)
  let ?t = "Node l (a,b) r"
  have inv_sub: "inv l" "inv r"
    using Node inv_Node by blast+
  show ?case
  proof (cases "l = Leaf")
    case True
    then show ?thesis
      using Node.prems(1,2) inv_children_explD(4) by force
  next
    case False
    then obtain m' l' where SmL: "split_min l = (m', l')"
                      and inv_l': "inv l'"
      by (metis split_min_inv inv_sub(1) old.prod.exhaust)
    have "rank ?t \<le> rank r + c\<^sub>u"
      using Node.prems(1) inv_children_explD(4) by force
    also have "... \<le> rank (join l' a r) + c\<^sub>u"
      using rule_mono[OF inv_l' inv_sub(2)] by auto
    moreover have "t' = join l' a r"
      using Node False SmL by auto
    ultimately show ?thesis by simp
  qed
qed

text \<open>As per functional correctness, @{term split_min} always removes exactly one element.\<close>
lemma split_min_sum:
  "\<lbrakk>split_min t = (m, t'); inv t; t \<noteq> Leaf\<rbrakk> \<Longrightarrow> inv t' \<and> size t = size t' + 1"
  by (induction t arbitrary: m t' rule: tree2_induct)
     (auto simp: join_size inv_join inv_Leaf dest!: inv_Node split: prod.splits if_splits)

corollary split_min_size:
  assumes "inv t" "split_min t = (m, t')" "t \<noteq> Leaf"
  shows "size t' = size t - 1"
  using split_min_sum assms by simp

text \<open>The work of @{term split_min} follows the same inductive pattern as @{term W_splitl}.\<close>

fun W_split_min :: "('a*'b) tree \<Rightarrow> real" where
"W_split_min (Node l (a, _) r) =
  (if l = Leaf then 1 else let (m,l') = split_min l in 1 + W_split_min l + W_join l' a r)"

lemma W_split_min_bounded:
  assumes "inv t" "split_min t = (m, t')" "t \<noteq> Leaf"
  shows "W_split_min t \<le> 1 + c\<^sub>1 * height t + rank t'"
using assms proof (induction t arbitrary: t' rule: tree2_induct)
  case Leaf then show ?case by simp
next
  case (Node l a x r)
  let ?t = "Node l (a,x) r"
  have inv_sub: "inv l \<and> inv r" using inv_Node Node by blast
  have bal: "balanced ?t" using Node by blast
  show ?case
  proof (cases "l = Leaf")
    case True
    then have "t' = r" and "W_split_min ?t = 1"
      using Node by auto
    then show ?thesis using c\<^sub>1_def rank_pos c1_pos inv_sub by force
  next
    case False
    obtain m' l' where SmL: "split_min l = (m', l')"
      using False by fastforce
    have IH: "W_split_min l \<le> 1 + c\<^sub>1 * height l + rank l'"
      using Node False inv_sub SmL by simp
    have t'_def: "t' = join l' a r"
      using Node False SmL by auto
    have unfold: "W_split_min ?t = 1 + W_split_min l + W_join l' a r"
      using False SmL by force
    have rm: "rank l \<ge> rank l'"
      using split_min_rank False inv_sub SmL by simp
    then have "rank r + c\<^sub>\<delta> \<ge> rank l'"
      using Node bal c\<^sub>\<delta>_def by force
    then obtain \<delta> where hdiff: "rank r + c\<^sub>\<delta> = rank l' + \<delta>"
      by (metis add.commute diff_add_cancel)
    then have "W_join l' a r \<le> c\<^sub>\<delta> + \<delta>"
      using W_join_def c\<^sub>\<delta>_def c_vals \<open>rank l' \<le> rank r + c\<^sub>\<delta>\<close> by force
    then have "W_split_min ?t \<le> 2 + c\<^sub>1 * height l + rank l' + c\<^sub>\<delta> + \<delta>"
      using IH unfold by linarith
    also have "... = 2 + 2 * c\<^sub>\<delta> + c\<^sub>1 * height l + rank r"
      using hdiff by simp
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height l + rank t'"
      using inv_sub rule_mono False SmL split_min_inv t'_def by force
    also have "... \<le> 2 + 2*c\<^sub>\<delta> + c\<^sub>1 * height ?t - c\<^sub>1 + rank t'"
      using c1_pos by (simp add: distrib_left)
    also have "... \<le> 1 + c\<^sub>1 * height ?t + rank t'"
      by (simp add: c\<^sub>1_def)
    finally show ?thesis 
      by fastforce
  qed
qed

definition K_min :: real where "K_min = 1 + c\<^sub>1 / c\<^sub>l"

lemma K_min_nonneg: "0 \<le> K_min"
  using K_min_def c1_pos c_vals by auto

corollary W_split_min_rank:
  assumes "inv t" "split_min t = (m, t')" "t \<noteq> Leaf"
  shows "W_split_min t \<le> 1 + K_min * rank t"
proof -
  have "W_split_min t \<le> 1 + c\<^sub>1 * height t + rank t'"
    using assms W_split_min_bounded by force
  also have "... \<le> 1 + c\<^sub>1 * (rank t / c\<^sub>l) + rank t'"
    using c1_pos assms(1) mult_left_mono rank_lower_height_inverse by fastforce
  also have "... \<le> 1 + c\<^sub>1 * (rank t / c\<^sub>l) + rank t"
    by (simp add: assms split_min_rank)
  also have "... \<le> 1 + (1 + c\<^sub>1 / c\<^sub>l) * rank t"
    by argo
  finally show ?thesis 
    using K_min_def by presburger
qed

lemma W_split_min_ge_1: "t \<noteq> Leaf \<Longrightarrow> 1 \<le> W_split_min t"
  by (induction t rule: tree2_induct)
     (auto simp: W_join_def split: prod.splits)

text \<open>@{term T_split_min} is then bounded by @{term W_split_min}.\<close>

time_fun split_min equations split_min.simps

lemma rule_cost_step_min:
  assumes "inv l" "inv r" and "real t \<le> (1 + k\<^sub>0 + k\<^sub>1) * w"
  shows "1 + (real t + real (T_join l a r)) \<le> (1 + k\<^sub>0 + k\<^sub>1) * (1 + w + W_join l a r)"
  using rule_cost_step[OF assms] by (simp add: ac_simps)

lemma T_split_min_bridge_strong:
  "\<lbrakk>inv t; t \<noteq> Leaf\<rbrakk> \<Longrightarrow> real (T_split_min t) \<le> (1 + k\<^sub>0 + k\<^sub>1) * W_split_min t"
  using k\<^sub>0_nonneg k\<^sub>1_nonneg 
  by (induction t rule: tree2_induct)
     (auto intro!: rule_cost_step_min dest: split_min_inv inv_Node split: prod.splits)

subsubsection \<open>@{term join2}\<close>

text \<open>
  @{term join2} joins two trees without a pivot element by extracting
  the minimum of the right tree. Its rank is close to the maximum of its inputs, analogous
  to the monotonicity rule.\<close>

lemma join2_split_min: "\<lbrakk>split_min r = (m, r'); r \<noteq> Leaf\<rbrakk> \<Longrightarrow> join2 l r = join l m r'"
  by (simp add: join2_def)

lemma rule_mono_join2:
  assumes "inv l" "inv r"
  shows "max (rank l) (rank r) \<le> rank (join2 l r) + c\<^sub>u"
proof (cases r)
  case Leaf
  then show ?thesis
    using c_vals join2_def assms(1) rank_pos rule_bal rule_empty by simp
next
  case (Node l2 x r2)
  obtain m r' where SmR: "split_min r = (m, r')"
    by (cases "split_min r") auto
  have inv_r': "inv r'"
    using split_min_inv[OF SmR assms(2)] Node by simp
  have "join2 l r = join l m r'"
    using SmR Node by (simp add: join2_split_min)
  moreover have "max (rank l) (rank r') \<le> rank (join l m r')"
    using rule_mono[OF assms(1) inv_r'] .
  moreover have "rank r \<le> rank r' + c\<^sub>u"
    using split_min_rank_min[OF assms(2) SmR] Node by auto
  ultimately have "rank l \<le> rank (join2 l r) + c\<^sub>u"
              and "rank r \<le> rank (join2 l r) + c\<^sub>u"
    using c_vals by auto
  then show ?thesis 
    by (simp add: max_def)
qed

text \<open>Size is again defined by functional correctness.\<close>

lemma join2_size:
  assumes "inv l" "inv r"
  shows "size (join2 l r) = size l + size r"
proof (cases r)
  case Leaf
  then show ?thesis by (simp add: join2_def)
next
  case (Node l2 x r2)
  obtain m r' where SM: "split_min r = (m, r')"
    by (cases "split_min r") auto
  have inv_r': "inv r'"
    using split_min_inv[OF SM assms(2)] Node by simp
  have "size r' = size r - 1"
    using split_min_size[OF assms(2) SM] Node by simp
  moreover have "join2 l r = join l m r'"
    using SM Node by (simp add: join2_split_min)
  moreover have "0 < size r"
    using Node by simp
  ultimately show ?thesis
    by (simp add: join_size[OF assms(1) inv_r'])
qed


text \<open>
  The work of @{term join2} is bounded by a join plus a linear term in the rank
  of the right tree, accounting for the cost of extracting the minimum.\<close>

definition W_join2 :: "('a*'b) tree \<Rightarrow> ('a*'b) tree \<Rightarrow> real" where
  "W_join2 l r = (if r = Leaf then 1
                  else let (m, r') = split_min r in W_join l m r' + W_split_min r)"

lemma W_join2_split_min:
  "\<lbrakk>split_min r = (m, r'); r \<noteq> Leaf\<rbrakk> \<Longrightarrow>
     W_join2 l r = W_join l m r' + W_split_min r"
  by (simp add: W_join2_def)

lemma W_join2_bounded:
  assumes "inv l" "inv r"
  shows "W_join2 l r \<le> W_join l a r + 1 + c\<^sub>u + K_min * rank r"
proof (cases r)
  case Leaf
  then show ?thesis
    using W_join2_def W_join_def c_vals rule_empty by auto
next
  case (Node l2 x r2)
  obtain m r' where SM: "split_min r = (m, r')"
    by (cases "split_min r") auto
  have inv_r': "inv r'" and rank_r': "rank r' \<le> rank r" and rank_min: "rank r \<le> rank r' + c\<^sub>u"
    using split_min_inv[OF SM assms(2)] split_min_rank[OF assms(2) SM]
      split_min_rank_min[OF assms(2) SM] Node by auto
  have "W_join2 l r = W_join l m r' + W_split_min r"
    using SM Node by (simp add: W_join2_split_min)
  also have "... \<le> W_join l m r' + 1 + K_min * rank r"
    using W_split_min_rank Node assms(2) SM by force
  also have "... \<le> abs(rank l - rank r') + 1 + K_min * rank r"
    using W_join_def by force
  also have "... \<le> abs(rank l - rank r) + c\<^sub>u + 1 + K_min * rank r"
    using rank_min rank_r' by argo
  finally show ?thesis
    using Node W_join_def by auto
qed

text \<open>@{term T_join2} is again bounded by @{term W_join2}.\<close>
time_fun join2 equations join2_def

lemma rule_cost_step_join2:
  assumes "inv l" "inv r" and "real t \<le> (1 + k\<^sub>0 + k\<^sub>1) * w" and "1 \<le> w"
  shows "real t + real (T_join l a r) \<le> K_T * (W_join l a r + w)"
proof -
  have "k\<^sub>0 * 1 \<le> k\<^sub>0 * w"
      using assms(4) k\<^sub>0_nonneg by (intro mult_left_mono) auto
  then have absorb: "k\<^sub>0 + (1 + k\<^sub>0 + k\<^sub>1) * w \<le> K_T * w"
    unfolding K_T_def by argo

  have "real t + real (T_join l a r)
        \<le> (k\<^sub>0 + (1 + k\<^sub>0 + k\<^sub>1) * w) + k\<^sub>1 * W_join l a r"
    using rule_cost_W[OF assms(1,2), where a=a] assms(3) by linarith
  also have "\<dots> \<le> K_T * w + K_T * W_join l a r"
    using absorb K_T_ge_k1 by (auto intro!: add_mono mult_right_mono)
  also have "\<dots> = K_T * (W_join l a r + w)"
    by algebra
  finally show ?thesis .
qed

lemma T_join2_bridge:
  assumes "inv l" "inv r"
  shows "real (T_join2 l r) \<le> K_T * W_join2 l r"
proof (cases "r = Leaf")
  case True
  then show ?thesis using K_T_ge_1 by (simp add: W_join2_def)
next
  case False
  obtain m r' where SM: "split_min r = (m,r')" by fastforce
  have inv_r': "inv r'" using split_min_inv[OF SM assms(2) False] .
  show ?thesis
    using rule_cost_step_join2[OF assms(1) inv_r'
            T_split_min_bridge_strong[OF assms(2) False]
            W_split_min_ge_1[OF False]]
    by (simp add: W_join2_def False SM)
qed

section \<open>Layered analysis of split-work\<close>

text \<open>
  The set operations \<open>union\<close>, \<open>inter\<close> and \<open>diff\<close> share one recursion
  pattern. At each step the root key of one tree acts as a pivot at which the other tree
  is split. Following \<^cite>\<open>blelloch2022joinable\<close>, the tree supplying the pivots is
  called the pivot tree and the tree being split the decomposed tree. In
  @{locale Set2_Join}, union and intersection split @{term t2} by the keys of @{term t1},
  so the pivot tree is @{term t1} and the decomposed tree is @{term t2}; for difference the roles are swapped.
  A subtree resulting from a split is referred to as a part of the decomposed tree.
  @{term split_work} records exactly the split cost incurred along this shared
  recursion.
  The goal of this section is obtaining a closed-form bound on @{term split_work}, 
  and this bound is in essence already the work bound of the set operations. By
  @{thm [source] W_split_bounded} each individual split costs linearly
  in the rank of the part \<open>t\<close> it splits, i.e. logarithmically in
  its size. What the analysis will show is that paying this logarithmic
  charge once per part already sums to the optimal $O(m \log(n/m + 1))$.
  This will be done by grouping the parts into unit-rank layers according
  to the pivot tree that produced them and using the fact that the
  number of rank roots per layer decays geometrically
  (c.f. @{thm [source] rank_roots_count_powr_le}),
  making the total collapse into a geometric series. 
  This corresponds to the exact analytical chain in 
  \<^cite>\<open>\<open>Theorem 11\<close> in blelloch2022joinable\<close>.
  For the final work bounds of each set function it will be shown that the work performed by
  @{term join} along the way follows the same cost model.
\<close>

fun split_work :: "('a * 'b) tree \<Rightarrow> ('a * 'b) tree \<Rightarrow> real" where
"split_work t1 t2 =
  (if t1 = Leaf then 0
   else if t2 = Leaf then 0
   else case t1 of Node l1 (a,_) r1 \<Rightarrow>
     (let (l2, _, r2) = split a t2
      in W_split t2 a
         + split_work l1 l2
         + split_work r1 r2))"

declare split_work.simps[simp del]

subsection \<open>Layered decomposition of @{term "split_work"}\<close>

text \<open>To enable layered analysis, this section shows that @{term split_work} can be
 re-written as a double sum over all layers, summing work of individual layers.
 First @{text split_parts} is defined, which collects all parts of the decomposed tree
 along the recursive path.\<close>

fun split_parts :: "(('a::linorder) * 'b) tree \<Rightarrow> ('a * 'b) tree \<Rightarrow> ('a * 'b) tree list" where
"split_parts t1 t2 =
  (if t1 = Leaf then []
   else if t2 = Leaf then []
   else case t1 of
     Node l1 (a,_) r1 \<Rightarrow>
       let (l2, _, r2) = split a t2
       in t2 # (split_parts l1 l2 @ split_parts r1 r2))"

declare split_parts.simps [simp del]

text \<open>Which enables bounding @{term split_work} by a direct sum, which already 
  plugs in bounds for \<open>W_split\<close>.\<close>
 
lemma split_work_le_part_sum:
  assumes "inv t2"
  shows "split_work t1 t2 \<le> (\<Sum>t \<leftarrow>(split_parts t1 t2). 2 + K_split * rank t)"
using assms
proof (induction t1 t2 rule: split_work.induct)
  case (1 t1 t2)
  then show ?case
    by (fastforce simp: split_work.simps[of t1 t2] split_parts.simps[of t1 t2]
                        split_inv add.assoc[symmetric]
                  intro!: add_mono W_split_bounded
                  split: tree.splits prod.splits)
qed

text \<open>All parts conform to @{term inv}, since split preserves it.\<close>
lemma split_parts_inv:
  assumes "inv t2"
  shows "t \<in> set (split_parts t1 t2) \<Longrightarrow> inv t"
using assms
proof (induction t1 t2 rule: split_parts.induct)
  case (1 t1 t2)
  then show ?case 
    by (fastforce simp: split_parts.simps[of t1 t2] split: tree.splits prod.splits if_splits)
qed

text \<open>Next, @{text parts_in_layer} collects the parts belonging
  to specific layers of the pivot tree @{text t1}.\<close>
fun parts_in_layer :: "(('a::linorder) * 'b) tree \<Rightarrow> ('a * 'b) tree \<Rightarrow> nat \<Rightarrow> ('a * 'b) tree list" where
"parts_in_layer t1 t2 i =
  (if t1 = Leaf then []
   else if t2 = Leaf then []
   else case t1 of
     Node l1 (a,_) r1 \<Rightarrow>
       let (l2, _, r2) = split a t2
       in ((if in_band i (rank t1) then [t2] else [])
           @ parts_in_layer l1 l2 i
           @ parts_in_layer r1 r2 i))"

declare parts_in_layer.simps[simp del]

text \<open>
  When the rank of the pivot tree @{term t1} is below layer @{term i}, no parts can be
  collected in that layer. This is because the layer condition @{term "real i \<le> rank t1"} fails
  at the root, and by balance, all children have even smaller rank.
\<close>
lemma parts_in_layer_empty_if_rank_lt:
  assumes "balanced t1" "rank t1 < i"
  shows "parts_in_layer t1 t2 i = []"
  using assms
proof (induction t1 arbitrary: t2 i)
  case Leaf then show ?case 
    by (simp add: parts_in_layer.simps)
next
  case (Node l1 x r1)
  then have "rank l1 < i" "rank r1 < i"
    using balanced_children_explD[of l1 x r1] c_vals by linarith+
  then show ?case using Node
    by (auto simp: parts_in_layer.simps[of "Node l1 x r1" t2 i]
             split: prod.splits tree.splits)
qed

text \<open>Layers above the rank of @{term t1} contribute nothing, so extending the
  summation range is harmless.\<close>
lemma sum_parts_in_layer_pad:
  assumes "balanced t1" "nat \<lceil>rank t1\<rceil> \<le> N"
  shows "(\<Sum>i \<le> N. \<Sum>t\<leftarrow>parts_in_layer t1 t2 i. f t)
       = (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>. \<Sum>t\<leftarrow>parts_in_layer t1 t2 i. f t)"
proof -
  have "(\<Sum>t\<leftarrow>parts_in_layer t1 t2 i. f t) = 0"
    if "i \<in> {..N} - {..nat \<lceil>rank t1\<rceil>}" for i
  proof -
    have "nat \<lceil>rank t1\<rceil> < i"  
      using that by simp
    then have "rank t1 < real i"
      by linarith
    then show ?thesis
      by (auto simp add: parts_in_layer_empty_if_rank_lt[OF assms(1)])
  qed
  then show ?thesis
    using assms(2) by (auto intro!: sum.mono_neutral_right)
qed

text \<open>A band condition @{term "in_band j x"} holds for exactly one
  index @{term j} (i.e. the floor of @{term x}). Summing an indicator over any 
  range covering it therefore collects its value exactly once.\<close>
lemma sum_band_single:
  fixes x :: real
  assumes "0 \<le> x" and "nat \<lfloor>x\<rfloor> \<le> R"
  shows "(\<Sum>j \<le> R. (if in_band j x then c else 0)) = c"
proof -
  have "(real j \<le> x \<and> x < real j + 1) \<longleftrightarrow> \<lfloor>x\<rfloor> = int j" for j
    by linarith
  then have "(real j \<le> x \<and> x < real j + 1) \<longleftrightarrow> j = nat \<lfloor>x\<rfloor>" for j
    using assms(1) by fastforce
  then show ?thesis
    using assms(2) by force
qed

text \<open>
  This now begets the central layering identity. Summing any weight over parts layer by layer
  yields the same value as summing over @{term split_parts} directly.
\<close>
lemma sum_parts_as_layers:
  fixes f :: "('a * 'b) tree \<Rightarrow> real"
  assumes "balanced t1"
  shows "(\<Sum>t\<leftarrow>split_parts t1 t2. f t) = (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>. \<Sum>t\<leftarrow>parts_in_layer t1 t2 i. f t)"
using assms
proof (induction t1 arbitrary: t2 rule: tree2_induct)
  case Leaf
  then show ?case 
    by (simp add: split_parts.simps parts_in_layer.simps)
next
  case (Node l1 a bx r1)
  obtain l2 b r2 where SPL: "split a t2 = (l2, b, r2)"
    by (cases "split a t2") auto

  let ?t1 = "Node l1 (a, bx) r1"
  let ?r = "nat \<lceil>rank ?t1\<rceil>"

  have Bl: "balanced l1" and Br: "balanced r1"
    using Node.prems by auto

  have "rank l1 \<le> rank ?t1" "rank r1 \<le> rank ?t1"
    using balanced_children_explD[OF Node.prems] c_vals by linarith+
  then have Rl: "nat \<lceil>rank l1\<rceil> \<le> ?r" and Rr: "nat \<lceil>rank r1\<rceil> \<le> ?r"
    by linarith+

  show ?case
  proof (cases "t2 = Leaf")
    case True
    then show ?thesis 
      by (simp add: split_parts.simps parts_in_layer.simps)
  next
    case False

    \<comment> \<open>The root contribution is collected exactly once, at layer \<open>\<lfloor>rank ?t1\<rfloor>\<close>\<close>
    have root_sum:
      "(\<Sum>j \<le> ?r. (if real j \<le> rank ?t1 \<and> rank ?t1 < real j + 1 then f t2 else 0)) = f t2"
      using rank_pos[OF Node.prems] by (auto intro!: sum_band_single; linarith)

    have "(\<Sum>t\<leftarrow>parts_in_layer ?t1 t2 j. f t)
        = (if real j \<le> rank ?t1 \<and> rank ?t1 < real j + 1 then f t2 else 0)
          + ((\<Sum>t\<leftarrow>parts_in_layer l1 l2 j. f t) + (\<Sum>t\<leftarrow>parts_in_layer r1 r2 j. f t))" for j
      using False SPL
      by (auto simp: parts_in_layer.simps[of ?t1 t2 j] split: prod.splits tree.splits)
    then have "(\<Sum>i \<le> ?r. \<Sum>t\<leftarrow>parts_in_layer ?t1 t2 i. f t)
        = (\<Sum>j \<le> ?r. (if real j \<le> rank ?t1 \<and> rank ?t1 < real j + 1 then f t2 else 0)) +
          ((\<Sum>i \<le> ?r. \<Sum>t\<leftarrow>parts_in_layer l1 l2 i. f t) +
          (\<Sum>i \<le> ?r. \<Sum>t\<leftarrow>parts_in_layer r1 r2 i. f t))"
      by (simp add: sum.distrib)
    also have "\<dots> = f t2 + ((\<Sum>t\<leftarrow>split_parts l1 l2. f t) + (\<Sum>t\<leftarrow>split_parts r1 r2. f t))"
      by (simp add: root_sum sum_parts_in_layer_pad[OF Bl Rl] sum_parts_in_layer_pad[OF Br Rr]
                    Node.IH(1)[OF Bl] Node.IH(2)[OF Br])
    also have "\<dots> = (\<Sum>t\<leftarrow>split_parts ?t1 t2. f t)"
      using False SPL by (simp add: split_parts.simps)
    finally show ?thesis 
      by fastforce
  qed
qed

subsubsection \<open>Bounding @{term parts_in_layer} via rank roots\<close>

text \<open>
  With the layering identity in place, one piece is still missing. Per layer,
  @{term parts_in_layer} accounts for the cost accurately but has no usable
  structure. Its entries are nested fragments of each other, so neither their
  number nor their total size can be nicely argued about. 
  The coarsening @{term rank_root_parts_in_layer} walks down @{term t1} only until a node whose rank
  falls in the band \<open>[i, i+1)\<close> (i.e. it is a rank root) records the current part and
  stops.
\<close>

fun rank_root_parts_in_layer :: "(('a::linorder) * 'b) tree \<Rightarrow> ('a * 'b) tree \<Rightarrow> nat \<Rightarrow> ('a * 'b) tree list" where
"rank_root_parts_in_layer t1 t2 i =
  (if t1 = Leaf then []
   else if t2 = Leaf then []
   else case t1 of
     Node l1 (a,_) r1 \<Rightarrow>
       let (l2, _, r2) = split a t2
       in (if in_band i (rank t1) then [t2] else
           rank_root_parts_in_layer l1 l2 i
           @ rank_root_parts_in_layer r1 r2 i))"

declare rank_root_parts_in_layer.simps[simp del]

text \<open>All such rank root parts in a layer preserve the invariant.\<close>

lemma root_parts_inv:
  assumes "inv t2"
  shows "t \<in> set (rank_root_parts_in_layer t1 t2 i) \<Longrightarrow> inv t"
  using assms
proof (induction t1 t2 i rule: rank_root_parts_in_layer.induct)
  case (1 t1 t2 i)
  then show ?case
     by (fastforce simp: rank_root_parts_in_layer.simps[of t1 t2 i] split_inv
           split: tree.splits prod.splits if_splits)
qed

text \<open>Moreover, none of them is empty as the recursion stops as soon as the 
  decomposed tree runs out.\<close>

lemma root_parts_nonempty:
  "t \<in> set (rank_root_parts_in_layer t1 t2 i) \<Longrightarrow> t \<noteq> Leaf"
proof (induction t1 t2 i rule: rank_root_parts_in_layer.induct)
  case (1 t1 t2 i)
  then show ?case
    by (fastforce simp: rank_root_parts_in_layer.simps[of t1 t2 i]
          split: tree.splits prod.splits if_splits)
qed

text \<open>
  The combined size of all rank root parts in a single layer cannot exceed the size of the
  decomposed tree @{term t2} \<^cite>\<open>\<open>Lemma 10\<close> in blelloch2022joinable\<close>.
\<close>
lemma sizes_root_layer:
  assumes "inv t2"
  shows "(\<Sum>t \<leftarrow> rank_root_parts_in_layer t1 t2 i. size t) \<le> size t2"
using assms
proof (induction t1 arbitrary: t2 i)
  case Leaf then show ?case
    by (simp add: rank_root_parts_in_layer.simps)
next
  case (Node l1 x r1)
  obtain l2 b r2 where SPL: "split (fst x) t2 = (l2, b, r2)"
    by (cases "split (fst x) t2") auto

  have "inv l2" "inv r2"
    using SPL Node.prems split_inv by blast+
  then have "(\<Sum>t\<leftarrow>rank_root_parts_in_layer l1 l2 i. size t) +
        (\<Sum>t\<leftarrow>rank_root_parts_in_layer r1 r2 i. size t) \<le> size t2"
    using Node.IH(1) Node.IH(2) split_size[OF SPL[symmetric] Node.prems] 
      by (meson add_mono_thms_linordered_semiring(1) dual_order.trans)
  then show ?case
    using SPL by (auto simp: rank_root_parts_in_layer.simps[of "Node l1 x r1" t2 i]
                  split: tree.splits prod.splits if_splits)
qed

text \<open>The number of rank root parts per layer is bounded directly
  by the number of rank roots of the pivot tree.\<close>

lemma length_root_parts_le_rank_roots:
  "length (rank_root_parts_in_layer t1 t2 i) \<le> length (rank_roots t1 i)"
  by (induction t1 arbitrary: t2)
     (auto simp: rank_root_parts_in_layer.simps add_mono split: prod.splits tree.splits if_splits)

text \<open>Each part collected by @{term parts_in_layer} is bounded by the rank of the
  decomposed tree.\<close>
lemma part_rank_le_snd:
  "t \<in> set (parts_in_layer t1 t2 i) \<Longrightarrow> inv t2 \<Longrightarrow> rank t \<le> rank t2"
proof (induction t1 arbitrary: t2)
  case Leaf
  then show ?case 
    by (simp add: parts_in_layer.simps)
next
  case (Node l x r)
  show ?case
  proof (cases "t2 = Leaf")
    case True
    then show ?thesis 
      using Node.prems by (simp add: parts_in_layer.simps)
  next
    case False
    obtain l2 b r2 where SPL: "split (fst x) t2 = (l2, b, r2)"
      by (cases "split (fst x) t2") auto
    have "inv l2" and inv_r2: "inv r2"
      using SPL Node.prems(2) split_inv by metis+
    moreover have "rank l2 \<le> rank t2" "rank r2 \<le> rank t2"
      using SPL Node.prems(2) split_rank by blast+
    ultimately show ?thesis
      using Node SPL False 
      by (fastforce simp: parts_in_layer.simps[of "Node l x r" t2]
                    intro: order.trans
                    split: prod.splits tree.splits if_splits)
  qed
qed

text \<open>
  Therefore, at a rank root @{term t1} of layer @{term i}, the number of parts in
  @{term "parts_in_layer t1 t2 i"} is bounded by the constant @{term C} i.e. the layer of
  @{term t1} has at most @{term C} nodes (c.f. @{thm [source] layer_bound_const}).
\<close>
lemma length_parts_in_layer_le_C:
  assumes "balanced t1" "in_band i (rank t1)"
  shows "length (parts_in_layer t1 t2 i) \<le> C"
proof -
  have "length (parts_in_layer t1 t2 i) \<le> length (layer t1 i)"
  proof (induction t1 arbitrary: t2)
    case Leaf then show ?case 
      by (simp add: parts_in_layer.simps)
  next
    case (Node l ab r)
    then show ?case
      by (auto simp: parts_in_layer.simps[of "Node l ab r" t2]
                     add_mono_thms_linordered_semiring(1)
               split: prod.splits tree.split if_split)
  qed
  also have "... \<le> C"
    using layer_bound_const assms by (simp add: C_def)
  finally show ?thesis .
qed

text \<open>
  Consequently, at a rank root the whole weighted part sum is charged against a single
  part. There are at most @{term C} parts, each of rank at most @{term "rank t2"}.
\<close>
lemma sum_parts_band_le_C:
  assumes "balanced t1" "inv t2" "in_band i (rank t1)"
      and "k > 0" "c > 0"
  shows "(\<Sum>t \<leftarrow> parts_in_layer t1 t2 i. k + c * rank t) \<le> real C * (k + c * rank t2)"
proof -
  have each: "\<And>t. t \<in> set (parts_in_layer t1 t2 i) \<Longrightarrow> k + c * rank t \<le> k + c * rank t2"
    using part_rank_le_snd assms(2,5) mult_left_mono by fastforce
  have "(\<Sum>t \<leftarrow> parts_in_layer t1 t2 i. k + c * rank t)
       \<le> (\<Sum>_ \<leftarrow> parts_in_layer t1 t2 i. k + c * rank t2)"
    using each by (simp add: sum_list_mono)
  also have "\<dots> = real (length (parts_in_layer t1 t2 i)) * (k + c * rank t2)"
    by (simp add: sum_list_triv)
  also have "\<dots> \<le> real C * (k + c * rank t2)"
    using length_parts_in_layer_le_C rank_pos assms
    by (auto intro: add_nonneg_nonneg mult_right_mono)
  finally show ?thesis .
qed

text \<open>
  Thus the coarsening loses only a constant factor. Below a rank root, @{term t1} has at
  most @{term C} further nodes in the layer (@{thm [source] layer_bound_const}), and
  every part collected there is a further split of the recorded part, hence of no
  larger rank. Per layer, the weighted part sum is therefore at most \<open>C\<close> times the
  root-part sum.
\<close>
lemma parts_rank_le_C_root_parts_rank:
  assumes "inv t1" "inv t2" "k > 0" "c > 0"
  shows "(\<Sum>t \<leftarrow> parts_in_layer t1 t2 i. k + c * rank t)
       \<le> real C * (\<Sum>t \<leftarrow> rank_root_parts_in_layer t1 t2 i. k + c * rank t)"
using assms(1,2)
proof (induction t1 arbitrary: t2 rule: tree2_induct)
  case Leaf
  then show ?case
    by (simp add: parts_in_layer.simps rank_root_parts_in_layer.simps)
next
  case (Node l1 a bx r1)
  let ?t1 = "Node l1 (a, bx) r1"
  obtain l2 b r2 where SPL: "split a t2 = (l2, b, r2)"
    by (cases "split a t2") auto
  consider (leaf) "t2 = Leaf"
    | (band) "t2 \<noteq> Leaf" "in_band i (rank ?t1)"
    | (rec) "t2 \<noteq> Leaf" "\<not> in_band i (rank ?t1)"
    by auto
  then show ?case
  proof cases
    case leaf
    then show ?thesis
      by (simp add: parts_in_layer.simps rank_root_parts_in_layer.simps)
  next
    case band
    then show ?thesis
      using sum_parts_band_le_C[OF rule_bal[OF Node.prems(1)] Node.prems(2) band(2) assms(3,4)]
      by (simp add: rank_root_parts_in_layer.simps[of ?t1 t2] SPL)
  next
    case rec
    have "(\<Sum>t \<leftarrow> parts_in_layer l1 l2 i. k + c * rank t)
             \<le> real C * (\<Sum>t \<leftarrow> rank_root_parts_in_layer l1 l2 i. k + c * rank t)"
      and "(\<Sum>t \<leftarrow> parts_in_layer r1 r2 i. k + c * rank t)
             \<le> real C * (\<Sum>t \<leftarrow> rank_root_parts_in_layer r1 r2 i. k + c * rank t)"
      using Node.IH Node.prems SPL by(auto simp: split_inv dest!: inv_Node)
    then show ?thesis
      using rec
      by (auto simp: parts_in_layer.simps[of ?t1 t2] rank_root_parts_in_layer.simps[of ?t1 t2]
                    SPL distrib_left) 
  qed
qed

text \<open>
  Combining the layering identity with the per-layer approximation yields the layered root-part sum.
\<close>
corollary sum_parts_le_C_root:
  assumes "inv t1" "inv t2" "k > 0" "c > 0"
  shows "(\<Sum>t\<leftarrow>split_parts t1 t2. k + c * rank t)
       \<le> real C * (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>.
            \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)"
proof -
  have "(\<Sum>t\<leftarrow>split_parts t1 t2. k + c * rank t)
      = (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>. \<Sum>t\<leftarrow>parts_in_layer t1 t2 i. k + c * rank t)"
    using sum_parts_as_layers[OF rule_bal[OF assms(1)]] by simp
  also have "\<dots> \<le> (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>.
                     real C * (\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t))"
    using parts_rank_le_C_root_parts_rank[OF assms] by (auto intro: sum_mono)
  also have "\<dots> = real C * (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>.
                     \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

subsection \<open>Split-work as a layered double sum\<close>

text \<open>With the above in place @{term split_work} can be rewritten into the target double-sum.\<close>

corollary split_work_le_C_root_parts:
  assumes "inv t1" "inv t2"
  shows "split_work t1 t2
       \<le> real C * K_split * (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>.
            \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. 2 + rank t)"
proof -
  have "split_work t1 t2
      \<le> (\<Sum>t \<leftarrow> split_parts t1 t2. 2 + K_split * rank t)"
    using split_work_le_part_sum[OF assms(2)] .
  also have "... \<le> (\<Sum>t \<leftarrow> split_parts t1 t2. K_split * 2 + K_split * rank t)"
    using K_split_ge_1 by (auto intro: sum_list_mono)
  also have "... \<le> real C * (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>.
            \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. K_split * 2 + K_split * rank t)"
    using sum_parts_le_C_root[OF assms, of "K_split * 2" K_split] K_split_pos by simp
  also have "... = real C * K_split * (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>.
            \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. 2 + rank t)"
  proof -
    have "(\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. K_split * 2 + K_split * rank t)
        = K_split * (\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. 2 + rank t)" for i
      unfolding distrib_left[symmetric] using sum_list_const_mult by fast
    then show ?thesis
      by (simp add: sum_distrib_left algebra_simps)
  qed
  finally show ?thesis .
qed

text \<open>Only non-empty layers contribute.\<close>
definition L where "L t1 t2 = {i. i \<le> nat \<lceil>rank t1\<rceil> \<and> rank_root_parts_in_layer t1 t2 i \<noteq> []}"

corollary L_finite: "finite (L t1 t2)"
  using finite_subset by (auto simp: L_def)

lemma sum_layers_nonempty:
  "(\<Sum>i \<le> nat \<lceil>rank t1\<rceil>. \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. f t) =
   (\<Sum>i \<in> L t1 t2. \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. f t)"
  by (auto simp: L_def atMost_def intro!: sum.mono_neutral_right)

corollary split_work_le_C_root_parts_L:
  assumes "inv t1" "inv t2"
  shows "split_work t1 t2
       \<le> real C * K_split * (\<Sum>i \<in> L t1 t2.
            \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. 2 + rank t)"
proof -
  have "split_work t1 t2
       \<le> real C * K_split * (\<Sum>i \<le> nat \<lceil>rank t1\<rceil>.
            \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. 2 + rank t)"
    using split_work_le_C_root_parts[OF assms] .
  also have "... = real C * K_split * (\<Sum>i \<in> L t1 t2.
            \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. 2 + rank t)"
    using sum_layers_nonempty by auto
  finally show ?thesis .
qed


subsection \<open>Inner sum analysis\<close>

text \<open>
  In this subsection a closed form of the inner sum is obtained. 
   \<open>s\<close> denotes the number of rank root parts in a specific layer which inherits
  the geometric decay of the rank roots. 
  \<close>
definition s where "s t1 t2 i = length (rank_root_parts_in_layer t1 t2 i)"

lemma s_le_geometric:
  assumes "inv t1"
  shows "real (s t1 t2 i) \<le> size1 t1 / 2 powr (i / c\<^sub>u)"
proof -
  have "real (s t1 t2 i) \<le> real (length (rank_roots t1 i))"
    using length_root_parts_le_rank_roots by (simp add: s_def)
  also have "\<dots> \<le> size1 t1 / 2 powr (i / c\<^sub>u)"
    using rank_roots_count_powr_le assms by blast
  finally show ?thesis .
qed

text \<open>
  Independently of the layer, the number of root parts is also bounded by the size of the
  decomposed tree itself. Since every recorded part is non-empty, @{thm [source] sizes_root_layer}
  leaves room for at most @{term "size t2"} of them.
\<close>
lemma s_le_size:
  assumes "inv t2"
  shows "s t1 t2 i \<le> size t2"
proof -
  let ?xs = "rank_root_parts_in_layer t1 t2 i"
  have "\<And>t. t \<in> set ?xs \<Longrightarrow> 1 \<le> size t"
    using root_parts_nonempty by (metis eq_size_0 less_one not_le)
  then have "(\<Sum>t\<leftarrow>?xs. 1) \<le> (\<Sum>t\<leftarrow>?xs. size t)"
    by (intro sum_list_mono)
  then show ?thesis
    using sizes_root_layer[OF assms] dual_order.trans
    by (simp add: s_def sum_list_triv) blast
qed

text \<open>Replace rank with @{term "c\<^sub>u * log 2 (size1 t)"} using 
  @{thm [source] rank_le_cu_log_size1}.\<close>
lemma inner_sum_log_bound:
  assumes "inv t2"
  shows "(\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. rank t)
       \<le> c\<^sub>u * (\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. log 2 (size1 t))"
proof -
  have "\<forall>t \<in> set (rank_root_parts_in_layer t1 t2 i). rank t \<le> c\<^sub>u * log 2 (size1 t)"
    using root_parts_inv[OF assms] rank_le_cu_log_size1' by blast
  then have "sum_list (map rank (rank_root_parts_in_layer t1 t2 i))
           \<le> sum_list (map (\<lambda>t. c\<^sub>u * log 2 (size1 t)) (rank_root_parts_in_layer t1 t2 i))"
    by (auto intro: sum_list_mono)
  then show ?thesis
    by (metis sum_list_const_mult)
qed

corollary inner_sum_log_bound_size:
  assumes "inv t2"
  shows "(\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. rank t)
       \<le> c\<^sub>u * (\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. log 2 (size t + 1))"
  by (metis (lifting) ext assms inner_sum_log_bound size1_size)

text \<open>
  Since the inner sum can now be written as a sum of logs, Jensen's inequality
  for concave functions on finite sets (c.f. @{thm [source] jensen_finite}) pulls the log out
  of the sum, replacing the sum of logs with a single log of the average.
  This is key because the size of an individual part in a layer cannot be known,
  but their combined size is bounded - the concavity of @{term log} makes 
  the average the right quantity to work with.
\<close>
lemma bound_sum_logs:
  assumes "rank_root_parts_in_layer t1 t2 i \<noteq> []"
  shows "(\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. log 2 (real (size t + 1)))
       \<le> (s t1 t2 i) * log 2 ((\<Sum>t \<leftarrow> rank_root_parts_in_layer t1 t2 i. size t + 1) / (s t1 t2 i))"
proof -
  let ?xs = "rank_root_parts_in_layer t1 t2 i"
  let ?vals = "map (\<lambda>t. real (size t + 1)) ?xs"
  let ?n = "length ?xs"
  let ?f = "log 2"
  let ?D = "{0<..}"

  have n_pos: "?n > 0" using assms by simp
  have pos: "\<And>x. x \<in> set ?vals \<Longrightarrow> x \<in> ?D" by auto
  have conc: "concave_on ?D ?f" using log_concave by simp

  have jensen: "(1 / real ?n) * sum_list (map ?f ?vals)
    \<le> ?f ((1 / real ?n) * sum_list ?vals)"
    using jensen_list[OF _ conc pos, of ?vals] n_pos by simp
  have "(\<Sum>t\<leftarrow>?xs. log 2 (real (size t + 1))) = sum_list (map ?f ?vals)"
    by (metis (mono_tags, lifting) list.map_comp map_eq_conv o_apply)
  also have "(1 / real ?n) * sum_list (map ?f ?vals) \<le> ?f ((1 / real ?n) * sum_list ?vals)"
    using jensen by simp
  also have "sum_list ?vals = real (\<Sum>t\<leftarrow>?xs. size t + 1)"
     by (metis (mono_tags, lifting) list.map_comp map_eq_conv o_apply sum_list_of_nat)
  finally have "(1 / real ?n) * (\<Sum>t\<leftarrow>?xs. log 2 (real (size t + 1)))
     \<le> log 2 (real (\<Sum>t\<leftarrow>?xs. size t + 1) / real ?n)"
    by simp
  then have "(\<Sum>t\<leftarrow>?xs. log 2 (real (size t + 1)))
      \<le> real ?n * log 2 (real (\<Sum>t\<leftarrow>?xs. size t + 1) / real ?n)"
    using n_pos by (simp add: divide_simps) argo 
  moreover have "real ?n = real (s t1 t2 i)"
    by (simp add: s_def)
  moreover have "(\<Sum>t\<leftarrow>?xs. size t + 1) = (\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. size t + 1)"
    by blast
  ultimately show ?thesis
    by simp
qed

text \<open>Combining the above with the size bound @{thm [source] sizes_root_layer} 
  enables simplification of the log.\<close>
lemma layer_step_1:
  assumes "inv t2" "s t1 t2 i > 0"
  shows "(s t1 t2 i) * log 2 ((\<Sum>t \<leftarrow> rank_root_parts_in_layer t1 t2 i. size t + 1) / (s t1 t2 i))
       \<le> (s t1 t2 i) * log 2 (size t2 / (s t1 t2 i) + 1)"
proof -
  let ?xs = "rank_root_parts_in_layer t1 t2 i"
  let ?n = "s t1 t2 i"
  let ?sum = "(\<Sum>t \<leftarrow> ?xs. size t + 1)"

  have npos: "?n > 0"
    using assms by simp
  have split_sum: "?sum = (\<Sum>t \<leftarrow> ?xs. size t) + ?n"
    by (simp add: sum_list_Suc s_def)

  have "?sum / ?n \<le> size t2 / ?n + 1"
  proof -
    have "(\<Sum>t \<leftarrow> ?xs. size t) \<le> size t2"
      using sizes_root_layer[OF assms(1)] by blast
    then have "?sum \<le> size t2 + ?n"
      using split_sum by linarith
    then have "?sum / ?n \<le> (size t2 + ?n) / ?n"
      using npos by (auto intro: divide_right_mono)
    also have "... = size t2 / ?n + 1"
      using npos by (simp add: add_divide_distrib)
    finally show ?thesis .
  qed

  then have "log 2 (?sum / ?n) \<le> log 2 (size t2 / ?n + 1)"
    using less_eq_real_def log_mono npos split_sum by auto
  then show ?thesis
    by (simp add: mult_left_mono npos)
qed

text \<open>Combining the three steps above, the whole contribution of a layer is bounded by a
  term in the part count \<open>s\<close> alone.\<close>
lemma layer_term_le_s:
  assumes "inv t2" "i \<in> L t1 t2" "0 \<le> c"
  shows "(\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)
       \<le> (s t1 t2 i) * (k + c * c\<^sub>u * log 2 (size t2 / (s t1 t2 i) + 1))"
proof -
  let ?xs = "rank_root_parts_in_layer t1 t2 i"
  have spos: "s t1 t2 i > 0" using assms(2) by (simp add: L_def s_def)

  have "(\<Sum>t\<leftarrow>?xs. rank t) \<le> c\<^sub>u * (\<Sum>t\<leftarrow>?xs. log 2 (size t + 1))"
    using inner_sum_log_bound_size[OF assms(1)] .
  also have "\<dots> \<le> c\<^sub>u * ((s t1 t2 i) * log 2 ((\<Sum>t \<leftarrow> ?xs. size t + 1) / (s t1 t2 i)))"
  proof -
    have "?xs \<noteq> []" using spos s_def by auto
    then show ?thesis using bound_sum_logs c_vals by (simp add: mult_left_mono)
  qed
  also have "\<dots> \<le> c\<^sub>u * ((s t1 t2 i) * log 2 (size t2 / (s t1 t2 i) + 1))"
    using layer_step_1[OF assms(1) spos] c_vals by (simp add: mult_left_mono)
  finally have rank_chain: "(\<Sum>t\<leftarrow>?xs. rank t)
       \<le> c\<^sub>u * ((s t1 t2 i) * log 2 (size t2 / (s t1 t2 i) + 1))" .

  have "(\<Sum>t\<leftarrow>?xs. k + c * rank t) = k * (s t1 t2 i) + c * (\<Sum>t\<leftarrow>?xs. rank t)"
    by (simp add: sum_list_addf s_def sum_list_triv sum_list_const_mult algebra_simps)
  also have "\<dots> \<le> k * (s t1 t2 i) + c * (c\<^sub>u * ((s t1 t2 i) * log 2 (size t2 / (s t1 t2 i) + 1)))"
    using mult_left_mono[OF rank_chain assms(3)] by linarith
  also have "\<dots> = (s t1 t2 i) * (k + c * c\<^sub>u * log 2 (size t2 / (s t1 t2 i) + 1))"
    by argo
  finally show ?thesis .
qed

text \<open>
  From strict monotonicity of
  $x \log_2\left(1 + \frac{n}{x}\right)$ (c.f. @{thm [source] xlog_term_mono}) \<open>s\<close> can
  be substituted with its geometric upper bound.
\<close>
  (* This corresponds to step 5 of the paper. *)
lemma layer_term_le_geometric:
  assumes "inv t1" "inv t2" "size t2 > 0" "i \<in> L t1 t2" and k0: "0 \<le> k" and c0: "0 \<le> c"
  shows "(\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)
       \<le> (size1 t1 / 2 powr (i / c\<^sub>u)) *
           (k + c * c\<^sub>u * log 2 (size t2 / (size1 t1 / 2 powr (i / c\<^sub>u)) + 1))"
proof -
  have spos: "0 < real (s t1 t2 i)" using assms(4) by (simp add: L_def s_def)
  have npos: "0 < real (size t2)" using assms(3) by simp
  have ccu: "0 \<le> c * c\<^sub>u" using c0 c_u_nonneg by (rule mult_nonneg_nonneg)

  have "(\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)
      \<le> (s t1 t2 i) * (k + c * c\<^sub>u * log 2 (size t2 / (s t1 t2 i) + 1))"
    using layer_term_le_s[OF assms(2,4) c0] .
  also have "\<dots> \<le> (size1 t1 / 2 powr (i / c\<^sub>u)) *
           (k + c * c\<^sub>u * log 2 (size t2 / (size1 t1 / 2 powr (i / c\<^sub>u)) + 1))"
    using xlog_term_mono[OF spos s_le_geometric[OF assms(1)] npos k0 ccu] .
  finally show ?thesis .
qed


subsection \<open>Closed-form work bound\<close>

text \<open>
  Having obtained a closed form for the inner sum, the rest of the proof proceeds purely
  analytically. All previous steps are combined to show that each layer's contribution
  is bounded by a term involving $\mathit{size1~t_1} / 2^{i/c_u}$ (the geometric
  decay) and a logarithmic factor. The sum index $i$ only appears as an exponent
  in the denominator, which is key for obtaining the final closed form via geometric series.
\<close>
corollary dsum_le_sum_logs:
  assumes "inv t1" "inv t2" "size t2 > 0" and k0: "0 \<le> k" and c0: "0 \<le> c"
  shows "(\<Sum>i \<in> L t1 t2. \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)
       \<le> (\<Sum>i \<in> L t1 t2.
            (size1 t1 / 2 powr (i / c\<^sub>u)) *
            (k + c * c\<^sub>u * log 2 (size t2 / (size1 t1 / 2 powr (i / c\<^sub>u)) + 1)))"
  using assms layer_term_le_geometric sum_mono by meson


text \<open>
  The sum from @{thm [source] dsum_le_sum_logs} has summands of the form
  $z_i \cdot (k + c \cdot c_u \log_2(n/z_i + 1))$ with $z_i = m / 2^{i/c_u}$. After rewriting
  $z_i$ in terms of the geometric ratio $1/2^{1/c_u}$, the log is split and linearized
  pointwise, and the sum falls apart into geometric and arithmetic-geometric series,
  bounded by $S_1$ and $S_2$ respectively.
\<close>
lemma final_sum_decomposed_ge_pivot:
  assumes sz2: "size t2 > 0" and k0: "0 \<le> k" and c0: "0 \<le> c"
  shows "(\<Sum>i \<in> L t1 t2.
           (size1 t1 / 2 powr (i / c\<^sub>u)) *
           (k + c * c\<^sub>u * log 2 (size t2 / (size1 t1 / 2 powr (i / c\<^sub>u)) + 1)))
       \<le> size1 t1 * (k * S1 c\<^sub>u + c * c\<^sub>u * S1 c\<^sub>u + c * S2 c\<^sub>u)
        + c * c\<^sub>u * S1 c\<^sub>u * size1 t1 * log 2 (size t2 / size1 t1 + 1)"
proof -
  let ?A = "L t1 t2"
  let ?m = "real (size1 t1)"
  let ?n = "real (size t2)"
  let ?q = "geom_ratio c\<^sub>u"

  have cu_pos: "c\<^sub>u > 0" using c_vals by force
  have finA: "finite ?A" using L_finite .
  have m_pos: "?m > 0" by simp
  have nm_pos: "?n / ?m > 0" using sz2 m_pos by simp
  have q_ge0: "?q ^ i \<ge> 0" for i using geom_ratio_range[OF cu_pos] by simp

  have inv_powr_as_q: "1 / (2 powr (real i / c\<^sub>u)) = ?q ^ i" for i
    using inv_powr_geom_ratio[OF cu_pos] .

  have summand_rw:
    "((?m / (2 powr (real i / c\<^sub>u))) *
      (k + c * c\<^sub>u * log 2 (?n / (?m / (2 powr (real i / c\<^sub>u))) + 1)))
     = ?m * (?q ^ i) * (k + c * c\<^sub>u * log 2 ((?n / ?m) * (2 powr (real i / c\<^sub>u)) + 1))" for i
  proof -
    have "?m / (2 powr (real i / c\<^sub>u)) = ?m * (?q ^ i)"
      by (metis inv_powr_as_q mult.right_neutral times_divide_eq_right)
    moreover have "?n / (?m / (2 powr (real i / c\<^sub>u))) = (?n / ?m) * (2 powr (real i / c\<^sub>u))"
      using m_pos by force
    ultimately show ?thesis by presburger
  qed

  \<comment> \<open>Pointwise: split the log and linearize the power part\<close>
  have pw: "log 2 ((?n / ?m) * (2 powr (real i / c\<^sub>u)) + 1)
          \<le> log 2 (?n / ?m + 1) + (1 + real i / c\<^sub>u)" for i
  proof -
    have "log 2 ((?n / ?m) * (2 powr (real i / c\<^sub>u)) + 1)
        \<le> log 2 (?n / ?m + 1) + log 2 (2 powr (real i / c\<^sub>u) + 1)"
      using log_split[of "?n / ?m" "2 powr (real i / c\<^sub>u)"] nm_pos by auto
    then show ?thesis
      using log_2powr_plus_1_le[of "real i / c\<^sub>u"] cu_pos by simp
  qed

  \<comment> \<open>Pointwise: distribute into the three series summands\<close>
  have expand: "?m * (?q ^ i) * (k + c * c\<^sub>u * (log 2 (?n / ?m + 1) + (1 + real i / c\<^sub>u)))
              = ?m * ((k + c * c\<^sub>u) * ?q ^ i + c * c\<^sub>u * ?q ^ i * log 2 (?n / ?m + 1)
                      + c * real i * ?q ^ i)" for i
    using cu_pos by (simp add: field_simps)

  have "(\<Sum>i \<in> ?A.
         (?m / (2 powr (i / c\<^sub>u))) *
         (k + c * c\<^sub>u * log 2 (?n / (?m / (2 powr (i / c\<^sub>u))) + 1)))
      = (\<Sum>i \<in> ?A. ?m * (?q ^ i) * (k + c * c\<^sub>u * log 2 ((?n / ?m) * (2 powr (real i / c\<^sub>u)) + 1)))"
    using summand_rw by simp

  \<comment> \<open>Split the log and linearize inside the sum\<close>
  also have "... \<le> (\<Sum>i \<in> ?A. ?m * (?q ^ i) *
      (k + c * c\<^sub>u * (log 2 (?n / ?m + 1) + (1 + real i / c\<^sub>u))))"
    using pw m_pos q_ge0 c_vals c0
    by (auto intro!: mult_nonneg_nonneg sum_mono mult_left_mono add_left_mono)

  \<comment> \<open>Distribute and split into three geometric series\<close>
  also have "... = (\<Sum>i \<in> ?A. ?m * ((k + c * c\<^sub>u) * ?q ^ i
    + c * c\<^sub>u * ?q ^ i * log 2 (?n / ?m + 1) + c * real i * ?q ^ i))"
    by (simp add: expand)

  also have "... = ?m * (
      (k + c * c\<^sub>u) * (\<Sum>i\<in>?A. ?q ^ i)
    + c * c\<^sub>u * (\<Sum>i\<in>?A. ?q ^ i) * log 2 (?n / ?m + 1)
    + c * (\<Sum>i\<in>?A. real i * (?q ^ i)))"
    by (simp add: sum.distrib sum_distrib_left sum_distrib_right algebra_simps)

  also have "... \<le> ?m * (
      (k + c * c\<^sub>u) * S1 c\<^sub>u
    + c * c\<^sub>u * S1 c\<^sub>u * log 2 (?n / ?m + 1)
    + c * S2 c\<^sub>u)"
    using geom_ratio_sum_le[OF cu_pos finA] geom_ratio_arith_sum_le[OF cu_pos finA] m_pos nm_pos c_vals k0 c0
    by (auto simp: add_pos_pos
             intro!: mult_left_mono add_mono mult_right_mono add_nonneg_nonneg mult_nonneg_nonneg)

  \<comment> \<open>Gather terms\<close>
  also have "... = ?m * (k * S1 c\<^sub>u + c * c\<^sub>u * S1 c\<^sub>u + c * S2 c\<^sub>u)
                 + c * c\<^sub>u * S1 c\<^sub>u * ?m * log 2 (?n / ?m + 1)"
    by argo
  finally show ?thesis by simp
qed


text \<open>
  The bound of @{thm [source] final_sum_decomposed_ge_pivot} is tight only while the decomposed
  tree @{term t2} is at least as large as the pivot tree @{term t1}. Otherwise the geometric bound
  $m / 2^{i/c_u}$ on the layer counts exceeds $n = \mathit{size}\ t_2$ in the upper layers
  and the linear term degenerates to $O(m)$. This is the second case in the proof of
  \<^cite>\<open>\<open>Theorem 11\<close> in blelloch2022joinable\<close> - the layers are cut at the threshold
  $\theta = c_u \log_2(m / n)$, where the two bounds on \<open>s\<close> coincide.
  \<^item> Layers $i \le \theta$ are bounded via @{thm [source] s_le_size}. Each contributes
    at most $n (k + c\, c_u)$ and there are at most $\theta + 1$ of them.
  \<^item> Layers $i > \theta$ are bounded geometrically as before, but re-indexed relative to the
    first such layer $i_0 = \lfloor\theta\rfloor + 1$. There the geometric bound has already
    decayed to $n$, so the sum becomes a geometric series in $n$.
\<close>

lemma final_sum_decomposed_le_pivot:
  assumes "inv t1" "inv t2" "size t2 > 0" "size t2 \<le> size1 t1"
      and k0: "0 \<le> k" and c0: "0 \<le> c"
  shows "(\<Sum>i \<in> L t1 t2. \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)
       \<le> size t2 * ((k + c * c\<^sub>u) * (1 + S1 c\<^sub>u) + c * S1 c\<^sub>u + c * S2 c\<^sub>u)
        + (k + c * c\<^sub>u) * c\<^sub>u * size t2 * log 2 (size1 t1 / size t2 + 1)"
proof -
  let ?m = "real (size1 t1)"
  let ?n = "real (size t2)"
  let ?\<theta> = "c\<^sub>u * log 2 (?m / ?n)"
  let ?i\<^sub>0 = "nat \<lfloor>?\<theta>\<rfloor> + 1"
  let ?L\<^sub>1 = "{i \<in> L t1 t2. i < ?i\<^sub>0}"
  let ?L\<^sub>2 = "{i \<in> L t1 t2. ?i\<^sub>0 \<le> i}"
  let ?q = "geom_ratio c\<^sub>u"
  let ?term = "\<lambda>i. (\<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)"

  have cu_pos: "c\<^sub>u > 0" using c_vals by force
  have cu_ne: "c\<^sub>u \<noteq> 0" using cu_pos by linarith
  have ccu: "0 \<le> c * c\<^sub>u" using c0 c_u_nonneg by fastforce
  have m_pos: "?m > 0" by simp
  have n_pos: "?n > 0" using assms(3) by simp
  have mn_pos: "?m / ?n > 0" using m_pos n_pos by simp
  have mn_ge1: "1 \<le> ?m / ?n" using assms(4) n_pos by force
  have \<theta>_nonneg: "0 \<le> ?\<theta>" using cu_pos mn_ge1 mn_pos by simp
  have i0_bounds: "?\<theta> < real ?i\<^sub>0" "real ?i\<^sub>0 \<le> ?\<theta> + 1"
    using \<theta>_nonneg by linarith+

  \<comment> \<open>Split the layers at the threshold\<close>
  have "(\<Sum>i \<in> L t1 t2. ?term i) = (\<Sum>i \<in> ?L\<^sub>1 \<union> ?L\<^sub>2. ?term i)"
    by (rule sum.cong) auto
  also have "\<dots> = (\<Sum>i \<in> ?L\<^sub>1. ?term i) + (\<Sum>i \<in> ?L\<^sub>2. ?term i)"
    by (rule sum.union_disjoint) (auto intro: rev_finite_subset[OF L_finite])
  finally have sum_split: "(\<Sum>i \<in> L t1 t2. ?term i)
      = (\<Sum>i \<in> ?L\<^sub>1. ?term i) + (\<Sum>i \<in> ?L\<^sub>2. ?term i)" .

  \<comment> \<open>Lower layers: at most \<open>size t2\<close> parts each, and at most \<open>\<theta> + 1\<close> such layers\<close>
  have L1_term: "?term i \<le> ?n * (k + c * c\<^sub>u)" if "i \<in> L t1 t2" for i
  proof -
    have spos: "0 < real (s t1 t2 i)" using that by (simp add: L_def s_def)
    have sle: "real (s t1 t2 i) \<le> ?n" using s_le_size[OF assms(2)] by simp
    have "?term i \<le> (s t1 t2 i) * (k + c * c\<^sub>u * log 2 (?n / (s t1 t2 i) + 1))"
      using layer_term_le_s[OF assms(2) that c0] .
    also have "\<dots> \<le> ?n * (k + c * c\<^sub>u * log 2 (?n / ?n + 1))"
      using xlog_term_mono[OF spos sle n_pos k0 ccu] .
    also have "\<dots> = ?n * (k + c * c\<^sub>u)"
      using n_pos by simp
    finally show ?thesis .
  qed

  have card_L1: "real (card ?L\<^sub>1) \<le> ?\<theta> + 1"
  proof -
    have "card ?L\<^sub>1 \<le> card {..<?i\<^sub>0}"
      by (intro card_mono) auto
    then have "real (card ?L\<^sub>1) \<le> real ?i\<^sub>0"
      by simp
    with i0_bounds(2) show ?thesis
      by linarith
  qed

  have sum_L1: "(\<Sum>i \<in> ?L\<^sub>1. ?term i) \<le> (?\<theta> + 1) * (?n * (k + c * c\<^sub>u))"
  proof -
    have "(\<Sum>i \<in> ?L\<^sub>1. ?term i) \<le> (\<Sum>i \<in> ?L\<^sub>1. ?n * (k + c * c\<^sub>u))"
      using L1_term by (intro sum_mono) auto
    also have "\<dots> = real (card ?L\<^sub>1) * (?n * (k + c * c\<^sub>u))"
      by simp
    also have "\<dots> \<le> (?\<theta> + 1) * (?n * (k + c * c\<^sub>u))"
      using card_L1 n_pos k0 ccu
      by (intro mult_right_mono) (auto intro!: mult_nonneg_nonneg add_nonneg_nonneg)
    finally show ?thesis .
  qed

  \<comment> \<open>Upper layers: the geometric bound decays from \<open>size t2\<close> onwards\<close>
  have L2_term: "?term i \<le> ?n * (k + c * c\<^sub>u + c) * ?q ^ (i - ?i\<^sub>0)
                          + c * ?n * (real (i - ?i\<^sub>0) * ?q ^ (i - ?i\<^sub>0))"
    if "i \<in> ?L\<^sub>2" for i
  proof -
    let ?j = "i - ?i\<^sub>0"
    let ?z = "?m / 2 powr (real i / c\<^sub>u)"
    have iL: "i \<in> L t1 t2" and i_ge: "?i\<^sub>0 \<le> i" using that by auto

    have i_split: "real i / c\<^sub>u = real ?i\<^sub>0 / c\<^sub>u + real ?j / c\<^sub>u"
      using i_ge cu_pos by (simp add: field_simps)
    have pow_split: "2 powr (real i / c\<^sub>u) = 2 powr (real ?i\<^sub>0 / c\<^sub>u) * 2 powr (real ?j / c\<^sub>u)"
      by (simp add: i_split powr_add)

    \<comment> \<open>\<open>i\<^sub>0\<close> lies within one layer above the threshold, i.e. \<open>m/n \<le> 2 powr (i\<^sub>0/c\<^sub>u) \<le> (m/n) 2 powr (1/c\<^sub>u)\<close>\<close>
    have pow_i0_lb: "?m / ?n \<le> 2 powr (real ?i\<^sub>0 / c\<^sub>u)"
    proof -
      have "log 2 (?m / ?n) < real ?i\<^sub>0 / c\<^sub>u"
        using i0_bounds(1) cu_pos by (simp add: field_simps)
      then have "2 powr (log 2 (?m / ?n)) < 2 powr (real ?i\<^sub>0 / c\<^sub>u)"
        by auto
      then show ?thesis
        using mn_pos by simp
    qed
    have pow_i0_ub: "2 powr (real ?i\<^sub>0 / c\<^sub>u) \<le> (?m / ?n) * 2 powr (1 / c\<^sub>u)"
    proof -
      have "real ?i\<^sub>0 / c\<^sub>u \<le> (?\<theta> + 1) / c\<^sub>u"
        using i0_bounds(2) cu_pos by (intro divide_right_mono) auto
      also have "\<dots> = log 2 (?m / ?n) + 1 / c\<^sub>u"
        using cu_ne by (simp add: add_divide_distrib)
      finally have "2 powr (real ?i\<^sub>0 / c\<^sub>u) \<le> 2 powr (log 2 (?m / ?n) + 1 / c\<^sub>u)"
        by simp
      then show ?thesis
        using mn_pos by (simp add: powr_add)
    qed

    \<comment> \<open>The geometric bound, re-indexed: \<open>z \<le> n q\<^sup>j\<close>\<close>
    have z_le: "?z \<le> ?n * ?q ^ ?j"
    proof -
      have "(?m / ?n) * 2 powr (real ?j / c\<^sub>u) \<le> 2 powr (real i / c\<^sub>u)"
        using pow_i0_lb unfolding pow_split by (intro mult_right_mono) auto
      then have "?z \<le> ?m / ((?m / ?n) * 2 powr (real ?j / c\<^sub>u))"
        using mn_pos by (intro divide_left_mono mult_pos_pos) auto
      also have "\<dots> = ?n / 2 powr (real ?j / c\<^sub>u)"
        using m_pos n_pos by (simp add: field_simps)
      also have "\<dots> = ?n * ?q ^ ?j"
        by (metis inv_powr_geom_ratio[OF cu_pos] mult.right_neutral times_divide_eq_right)
      finally show ?thesis .
    qed

    \<comment> \<open>The logarithmic factor: \<open>n / z \<le> 2 powr ((j + 1) / c\<^sub>u)\<close>\<close>
    have log_le: "log 2 (?n / ?z + 1) \<le> 1 + (real ?j + 1) / c\<^sub>u"
    proof -
      have "?n / ?z = (?n / ?m) * 2 powr (real ?i\<^sub>0 / c\<^sub>u) * 2 powr (real ?j / c\<^sub>u)"
        using m_pos unfolding pow_split by fastforce
      also have "\<dots> \<le> (?n / ?m) * ((?m / ?n) * 2 powr (1 / c\<^sub>u)) * 2 powr (real ?j / c\<^sub>u)"
        using pow_i0_ub n_pos m_pos by (intro mult_right_mono mult_left_mono) auto
      also have "\<dots> = 2 powr (1 / c\<^sub>u) * 2 powr (real ?j / c\<^sub>u)"
        using n_pos m_pos by auto
      also have "\<dots> = 2 powr ((real ?j + 1) / c\<^sub>u)"
        by (simp add: add_divide_distrib powr_add)
      finally have "?n / ?z \<le> 2 powr ((real ?j + 1) / c\<^sub>u)" .
      then have "log 2 (?n / ?z + 1) \<le> log 2 (2 powr ((real ?j + 1) / c\<^sub>u) + 1)"
        by (auto intro!: log_mono add_nonneg_pos)
      also have "\<dots> \<le> 1 + (real ?j + 1) / c\<^sub>u"
        using cu_pos by (simp add: log_2powr_plus_1_le)
      finally show ?thesis .
    qed

    have lognn: "0 \<le> log 2 (?n / ?z + 1)"
      by (simp add: log_def)

    have "?term i \<le> ?z * (k + c * c\<^sub>u * log 2 (?n / ?z + 1))"
      using layer_term_le_geometric[OF assms(1,2,3) iL k0 c0] .
    also have "\<dots> \<le> (?n * ?q ^ ?j) * (k + c * c\<^sub>u * (1 + (real ?j + 1) / c\<^sub>u))"
      using mult_left_mono[OF log_le ccu] k0 mult_nonneg_nonneg[OF ccu lognn]
         k0 mult_nonneg_nonneg[OF ccu lognn] z_le n_pos geom_ratio_range[OF cu_pos]
      by(intro mult_mono) auto 
    also have "\<dots> = ?n * (k + c * c\<^sub>u + c) * ?q ^ ?j + c * ?n * (real ?j * ?q ^ ?j)"
    proof -
      have eq: "c * c\<^sub>u * (1 + (real ?j + 1) / c\<^sub>u) = c * c\<^sub>u + c * (real ?j + 1)"
        using cu_ne by (simp add: field_simps)
      show ?thesis
        by (subst eq) (simp add: algebra_simps)
    qed
    finally show ?thesis .
  qed

  have sum_L2: "(\<Sum>i \<in> ?L\<^sub>2. ?term i) \<le> ?n * (k + c * c\<^sub>u + c) * S1 c\<^sub>u + c * ?n * S2 c\<^sub>u"
  proof -
    let ?J = "(\<lambda>i. i - ?i\<^sub>0) ` ?L\<^sub>2"
    have inj: "inj_on (\<lambda>i. i - ?i\<^sub>0) ?L\<^sub>2"
      by (auto simp: inj_on_def eq_diff_iff)
    have finJ: "finite ?J"
      by (auto intro: rev_finite_subset[OF L_finite])
    have "(\<Sum>i \<in> ?L\<^sub>2. ?term i)
        \<le> (\<Sum>i \<in> ?L\<^sub>2. ?n * (k + c * c\<^sub>u + c) * ?q ^ (i - ?i\<^sub>0)
                          + c * ?n * (real (i - ?i\<^sub>0) * ?q ^ (i - ?i\<^sub>0)))"
      using L2_term by (auto intro!: sum_mono) 
    also have "\<dots> = (\<Sum>j \<in> ?J. ?n * (k + c * c\<^sub>u + c) * ?q ^ j + c * ?n * (real j * ?q ^ j))"
      by (subst sum.reindex[OF inj]) (simp add: o_def)
    also have "\<dots> = ?n * (k + c * c\<^sub>u + c) * (\<Sum>j \<in> ?J. ?q ^ j)
                   + c * ?n * (\<Sum>j \<in> ?J. real j * ?q ^ j)"
      by (simp add: sum.distrib sum_distrib_left)
    also have "\<dots> \<le> ?n * (k + c * c\<^sub>u + c) * S1 c\<^sub>u + c * ?n * S2 c\<^sub>u"
      using geom_ratio_sum_le[OF cu_pos finJ] geom_ratio_arith_sum_le[OF cu_pos finJ] n_pos k0 c0 ccu
      by (auto intro!: add_mono mult_left_mono)
    finally show ?thesis .
  qed

  \<comment> \<open>Assemble; \<open>\<theta>\<close> is absorbed into the logarithmic term\<close>
  have "(\<Sum>i \<in> L t1 t2. ?term i)
      \<le> (?\<theta> + 1) * (?n * (k + c * c\<^sub>u)) + (?n * (k + c * c\<^sub>u + c) * S1 c\<^sub>u + c * ?n * S2 c\<^sub>u)"
    using sum_split sum_L1 sum_L2 by linarith
  also have "\<dots> = ?n * ((k + c * c\<^sub>u) * (1 + S1 c\<^sub>u) + c * S1 c\<^sub>u + c * S2 c\<^sub>u)
                 + (k + c * c\<^sub>u) * c\<^sub>u * ?n * log 2 (?m / ?n)"
    by argo
  also have "\<dots> \<le> ?n * ((k + c * c\<^sub>u) * (1 + S1 c\<^sub>u) + c * S1 c\<^sub>u + c * S2 c\<^sub>u)
                 + (k + c * c\<^sub>u) * c\<^sub>u * ?n * log 2 (?m / ?n + 1)"
    using mn_pos k0 ccu cu_pos by (auto intro!: log_mono add_left_mono mult_left_mono)
  finally show ?thesis .
qed

subsection \<open>Unified closed form\<close>

text \<open>
  The two closed forms combine into a single bound of the shape
  $A \cdot m + B \cdot m \log_2(n/m + 1)$ in the smaller size $m$ and the larger size $n$.
  For $m = \mathit{size1}\ t_1$ the first form applies, and its logarithm only grows when
  @{term "size t2"} is replaced by @{term "size1 t2"}. For $m = \mathit{size1}\ t_2$ the
  second form applies, and @{thm [source] xlog_mono} lets @{term "size t2"} grow to
  @{term "size1 t2"} in both factors at once. The constants are the pointwise maxima of
  the two cases.
\<close>

lemma S1_nonneg: "0 \<le> S1 c\<^sub>u" and S2_nonneg: "0 \<le> S2 c\<^sub>u"
  using geom_ratio_sum_le[of c\<^sub>u]  geom_ratio_arith_sum_le[of c\<^sub>u] c_vals by force+

abbreviation bound_mn :: "real \<Rightarrow> real \<Rightarrow> ('a*'b) tree \<Rightarrow> ('a*'b) tree \<Rightarrow> real" where
"bound_mn k c ta tb \<equiv>
    size_min ta tb * ((k + c * c\<^sub>u) * (1 + S1 c\<^sub>u) + c * S1 c\<^sub>u + c * S2 c\<^sub>u)
  + c\<^sub>u * (k + c * c\<^sub>u + c * S1 c\<^sub>u) * size_min ta tb
      * log 2 (size_max ta tb / size_min ta tb + 1)"

lemma final_sum_bound_mn:
  assumes "inv t1" "inv t2" "size t2 > 0" and k0: "0 \<le> k" and c0: "0 \<le> c"
  shows "(\<Sum>i \<in> L t1 t2. \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)
       \<le> bound_mn k c t1 t2"
proof -
  let ?A = "(k + c * c\<^sub>u) * (1 + S1 c\<^sub>u) + c * S1 c\<^sub>u + c * S2 c\<^sub>u"
  let ?B = "c\<^sub>u * (k + c * c\<^sub>u + c * S1 c\<^sub>u)"
  have ccu: "0 \<le> c * c\<^sub>u" using c0 c_u_nonneg by fastforce
  have cS1: "0 \<le> c * S1 c\<^sub>u" using c0 S1_nonneg by force
  have A_nonneg: "0 \<le> ?A"
    using k0 c0 ccu S1_nonneg S2_nonneg by auto
  have B_nonneg: "0 \<le> ?B"
    using k0 ccu cS1 c_u_nonneg by auto

  \<comment> \<open>The unified constants dominate those of both cases\<close>
  have A_ge: "k * S1 c\<^sub>u + c * c\<^sub>u * S1 c\<^sub>u + c * S2 c\<^sub>u \<le> ?A"
  using k0 ccu cS1 by argo
  have B_ge1: "c * c\<^sub>u * S1 c\<^sub>u \<le> ?B"
    by (metis add_increasing c_u_nonneg ccu k0 le_add_same_cancel2 
      mult.commute mult.left_commute mult_left_mono)
  have B_ge2: "(k + c * c\<^sub>u) * c\<^sub>u \<le> ?B"
    by (metis mult_left_mono le_add_same_cancel2 add.commute c_u_nonneg cS1 mult.commute)

  show ?thesis
  proof (cases "size t1 \<le> size t2")
    case True
    then have le: "size1 t1 \<le> size1 t2" by (simp add: size1_size)
    have mn: "size_min t1 t2 = size1 t1" "size_max t1 t2 = size1 t2"
      using le by (simp_all add: min_absorb1 max_absorb2)

    have lin: "size1 t1 * (k * S1 c\<^sub>u + c * c\<^sub>u * S1 c\<^sub>u + c * S2 c\<^sub>u) \<le> size1 t1 * ?A"
      using A_ge by (auto intro: mult_left_mono) 
    have "size t2 / size1 t1 \<le> size1 t2 / size1 t1"
      by (simp add: divide_right_mono size1_size)
    then have lg: "log 2 (size t2 / size1 t1 + 1) \<le> log 2 (size1 t2 / size1 t1 + 1)"
      by (intro log_mono) (auto intro: add_nonneg_pos)
    have "c * c\<^sub>u * S1 c\<^sub>u * size1 t1 * log 2 (size t2 / size1 t1 + 1)
        \<le> ?B * size1 t1 * log 2 (size t2 / size1 t1 + 1)"
      using B_ge1 by (intro mult_right_mono) (auto simp: log_def)
    also have "\<dots> \<le> ?B * size1 t1 * log 2 (size1 t2 / size1 t1 + 1)"
      using lg B_nonneg by (auto intro!: mult_left_mono mult_nonneg_nonneg)
    finally have lg': "c * c\<^sub>u * S1 c\<^sub>u * size1 t1 * log 2 (size t2 / size1 t1 + 1)
        \<le> ?B * size1 t1 * log 2 (size1 t2 / size1 t1 + 1)" .

    have "(\<Sum>i \<in> L t1 t2. \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)
        \<le> (\<Sum>i \<in> L t1 t2. (size1 t1 / 2 powr (i / c\<^sub>u)) *
             (k + c * c\<^sub>u * log 2 (size t2 / (size1 t1 / 2 powr (i / c\<^sub>u)) + 1)))"
      using dsum_le_sum_logs[OF assms(1,2,3) k0 c0] .
    also have "\<dots> \<le> size1 t1 * (k * S1 c\<^sub>u + c * c\<^sub>u * S1 c\<^sub>u + c * S2 c\<^sub>u)
                 + c * c\<^sub>u * S1 c\<^sub>u * size1 t1 * log 2 (size t2 / size1 t1 + 1)"
      using final_sum_decomposed_ge_pivot[OF assms(3) k0 c0] .
    also have "\<dots> \<le> size1 t1 * ?A + ?B * size1 t1 * log 2 (size1 t2 / size1 t1 + 1)"
      using lin lg' by linarith
    finally show ?thesis using mn by simp
  next
    case False
    then have le: "size1 t2 \<le> size1 t1" and sz: "size t2 \<le> size1 t1"
      by (auto simp: size1_size)
    have mn: "size_min t1 t2 = size1 t2" "size_max t1 t2 = size1 t1"
      using le by (auto simp: min_absorb2 max_absorb1)

    have lin: "size t2 * ?A \<le> size1 t2 * ?A"
      using A_nonneg by (simp add: mult_right_mono size1_size)
    have "size t2 * log 2 (size1 t1 / size t2 + 1) \<le> size1 t2 * log 2 (size1 t1 / size1 t2 + 1)"
      using assms(3) by (intro xlog_mono) (auto simp: size1_size)
    then have "(k + c * c\<^sub>u) * c\<^sub>u * (size t2 * log 2 (size1 t1 / size t2 + 1))
        \<le> (k + c * c\<^sub>u) * c\<^sub>u * (size1 t2 * log 2 (size1 t1 / size1 t2 + 1))"
      using k0 ccu c_u_nonneg by  (auto intro!: mult_left_mono)
    also have "\<dots> \<le> ?B * (size1 t2 * log 2 (size1 t1 / size1 t2 + 1))"
      using B_ge2 log_def by (intro mult_right_mono) auto
    finally have lg: "(k + c * c\<^sub>u) * c\<^sub>u * (size t2 * log 2 (size1 t1 / size t2 + 1))
        \<le> ?B * (size1 t2 * log 2 (size1 t1 / size1 t2 + 1))" .

    have "(\<Sum>i \<in> L t1 t2. \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. k + c * rank t)
        \<le> size t2 * ?A + (k + c * c\<^sub>u) * c\<^sub>u * size t2 * log 2 (size1 t1 / size t2 + 1)"
      using final_sum_decomposed_le_pivot[OF assms(1,2,3) sz k0 c0] .
    also have "\<dots> = size t2 * ?A + (k + c * c\<^sub>u) * c\<^sub>u * (size t2 * log 2 (size1 t1 / size t2 + 1))"
      by auto
    also have "\<dots> \<le> size1 t2 * ?A + ?B * (size1 t2 * log 2 (size1 t1 / size1 t2 + 1))"
      using lin lg by linarith
    also have "\<dots> = size1 t2 * ?A + ?B * size1 t2 * log 2 (size1 t1 / size1 t2 + 1)"
      by auto
    finally show ?thesis using mn by simp
  qed
qed

text\<open>Putting all of the above together yields the final theorem \<^cite>\<open>\<open>Theorem 11\<close> in blelloch2022joinable\<close>.\<close>

theorem split_work_bound_exact:
  assumes "inv t1" "inv t2" "size t2 > 0"
  shows "split_work t1 t2 \<le> real C * K_split * bound_mn 2 1 t1 t2"
proof -
  have "split_work t1 t2
       \<le> real C * K_split * (\<Sum>i \<in> L t1 t2.
            \<Sum>t\<leftarrow>rank_root_parts_in_layer t1 t2 i. 2 + rank t)"
    using split_work_le_C_root_parts_L[OF assms(1,2)] .
  also have "... \<le> real C * K_split * bound_mn 2 1 t1 t2"
    using final_sum_bound_mn[where k=2 and c=1, OF assms] K_split_pos C_pos
    by (auto intro: mult_left_mono)
  finally show ?thesis .
qed

section \<open>Generic work-bound theorem\<close>

text \<open>
  The three operations union, intersection and difference share one analytical chain.
  Writing @{term "(ta, tb)"} for the role pair - @{term "(t1, t2)"} for union and
  intersection, @{term "(t2, t1)"} for difference - each operation only has to provide
  two facts:
  \<^item> the join-work bound
      @{term "jw \<le> (\<Sum>t \<leftarrow> split_parts ta tb. k + c * rank t)"}
  \<^item> a decomposition @{term "W \<le> jw + split_work ta tb"}\<close>

text\<open>
  The former implies that the join-work is asymptotically no more than the split-work
  \<^cite>\<open>\<open>Theorem 10\<close> in blelloch2022joinable\<close>. The operation-specific theorems 
  are mere instantiations of this proof chain. First, observe that the argument for
  \<open>split_work\<close> is really an argument about summing \<open>split_parts\<close>.
\<close>

corollary part_sum_le_mn:
  assumes "inv ta" "inv tb" "size tb > 0"
  assumes kc: "0 < k" "0 < c"
  shows "(\<Sum>t \<leftarrow> split_parts ta tb. k + c * rank t) \<le> real C * bound_mn k c ta tb"
proof -
  have "(\<Sum>t \<leftarrow> split_parts ta tb. k + c * rank t)
      \<le> real C * (\<Sum>i \<in> L ta tb. \<Sum>t\<leftarrow>rank_root_parts_in_layer ta tb i. k + c * rank t)"
    using sum_parts_le_C_root sum_layers_nonempty assms by metis
  also have "... \<le> real C * bound_mn k c ta tb"
    using final_sum_bound_mn[OF assms(1,2,3)] kc C_pos by (auto intro: mult_left_mono)
  finally show ?thesis .
qed


text \<open>
  The arguments \<open>k, c\<close> of the packaged constants mirror the shape of the join-work
  bound. The shifts by \<open>1 + 2 * K_split\<close> resp. \<open>K_split\<close> account for the split-work and
  for the one unit of work charged per call.\<close>

definition K_lin :: "real \<Rightarrow> real \<Rightarrow> real" where
  "K_lin k c = real C * ((k + 1 + 2 * K_split + (c + K_split) * c\<^sub>u) * (1 + S1 c\<^sub>u)
                       + (c + K_split) * S1 c\<^sub>u + (c + K_split) * S2 c\<^sub>u)"
definition K_log :: "real \<Rightarrow> real \<Rightarrow> real" where
  "K_log k c = real C * c\<^sub>u * (k + 1 + 2 * K_split + (c + K_split) * c\<^sub>u + (c + K_split) * S1 c\<^sub>u)"

lemma K_lin_nonneg: "0 \<le> k \<Longrightarrow> 0 \<le> c \<Longrightarrow> 0 \<le> K_lin k c"
  unfolding K_lin_def using S1_nonneg S2_nonneg c_u_nonneg C_pos K_split_pos
  by (fastforce intro!: add_nonneg_nonneg mult_nonneg_nonneg)

lemma K_log_nonneg: "0 \<le> k \<Longrightarrow> 0 \<le> c \<Longrightarrow> 0 \<le> K_log k c"
  unfolding K_log_def using S1_nonneg c_u_nonneg C_pos K_split_pos
  by (fastforce intro!: add_nonneg_nonneg mult_nonneg_nonneg)

theorem W_bound_generic:
  fixes W jw k c :: real
  assumes invs: "inv ta" "inv tb" "size tb > 0"
  assumes decomp: "W \<le> jw + split_work ta tb"
  assumes jw_piv: "jw \<le> (\<Sum>t \<leftarrow> split_parts ta tb. k + c * rank t)"
  assumes k_pos: "0 < k" and c_pos: "0 < c"
  shows "W \<le> real C * bound_mn (k + 2 * K_split) (c + K_split) ta tb"
proof -
  have jw_bound: "jw \<le> real C * bound_mn k c ta tb"
    using jw_piv part_sum_le_mn[OF invs k_pos c_pos] by linarith
  have sw: "split_work ta tb \<le> real C * K_split * bound_mn 2 1 ta tb"
    using split_work_bound_exact[OF invs] .
  have "W \<le> real C * bound_mn k c ta tb + real C * K_split * bound_mn 2 1 ta tb"
    using decomp jw_bound sw by linarith
  also have "... = real C * bound_mn (k + 2 * K_split) (c + K_split) ta tb"
    by algebra
  finally show ?thesis .
qed

text \<open>
  The concrete work functions charge one unit per call, base cases included. Since every
  inner call records exactly one part, this overhead amounts to
  \<open>1 + length (split_parts ta tb)\<close> and is folded into the part sum by shifting \<open>k\<close>
  by one.\<close>

lemma sum_list_parts_shift:
  "(\<Sum>t \<leftarrow> xs. (k + 1) + c * rank t) = length xs + (\<Sum>t \<leftarrow> xs. k + c * rank t)"
  by (induction xs) (simp_all add: algebra_simps)

corollary W_bound_generic':
  fixes W jw k c :: real
  assumes invs: "inv ta" "inv tb"
  assumes decomp: "W \<le> 1 + length (split_parts ta tb) + jw + split_work ta tb"
  assumes jw_piv: "jw \<le> (\<Sum>t \<leftarrow> split_parts ta tb. k + c * rank t)"
  assumes k_pos: "0 < k" and c_pos: "0 < c"
  shows "W \<le> 1 + K_lin k c * size_min ta tb
             + K_log k c * (size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1))"
proof (cases "tb = Leaf")
  case True
  \<comment> \<open>An empty decomposed tree produces no parts, so only the unit of work
     of the call itself remains and the bound holds trivially\<close>
  have kc: "0 \<le> k" "0 \<le> c"
    using k_pos c_pos by linarith+
  have parts: "split_parts ta tb = []" and work: "split_work ta tb = 0"
    by (simp_all add: True split_parts.simps[of ta Leaf] split_work.simps[of ta Leaf])
  have "W \<le> 1 + jw" and "jw \<le> 0"
    using decomp jw_piv by (simp_all add: parts work)
  then have "W \<le> 1"
    by linarith
  moreover have "0 \<le> K_lin k c * size_min ta tb"
    by (intro mult_nonneg_nonneg K_lin_nonneg kc) simp
  moreover have "0 \<le> K_log k c * (size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1))"
    by (rule mult_nonneg_nonneg[OF K_log_nonneg[OF kc]]) (simp add: log_def)
  ultimately show ?thesis
    by linarith
next
  case False
  then have sz: "size tb > 0"
    by (cases tb) auto
  have "length (split_parts ta tb) + jw \<le> (\<Sum>t \<leftarrow> split_parts ta tb. (k + 1) + c * rank t)"
    using jw_piv by (simp add: sum_list_parts_shift)
  moreover have "0 < k + 1"
    using k_pos by linarith
  ultimately have "length (split_parts ta tb) + jw + split_work ta tb
      \<le> real C * bound_mn (k + 1 + 2 * K_split) (c + K_split) ta tb"
    using W_bound_generic[OF invs sz order.refl _ _ c_pos] by blast
  also have "\<dots> = K_lin k c * size_min ta tb
             + K_log k c * (size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1))"
    unfolding K_lin_def K_log_def by algebra
  finally show ?thesis
    using decomp by linarith
qed

subsection \<open>Asymptotic form\<close>

text \<open>
  The closed-form bound above has the shape $1 + O(m) + O(m \log_2(n/m + 1))$.
  Since $1 \le m \le n$, the logarithm is at least $\log_2 2 = 1$, so both the constant and
  the linear part are absorbed and each operation runs in $O(m \log_2(n/m + 1))$.\<close>

lemma K_lin_log_pos:
  assumes "0 \<le> k" "0 \<le> c"
  shows "0 < 1 + K_lin k c + K_log k c"
  using K_lin_nonneg[OF assms] K_log_nonneg[OF assms] by linarith

lemma mlog_ge:
  fixes ta tb :: "('a * 'b) tree"
  shows "1 \<le> size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1)"
    and "size_min ta tb \<le> size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1)"
proof -
  have m1: "1 \<le> size_min ta tb" and mM: "size_min ta tb \<le> size_max ta tb"
    by (simp_all add: size1_size min_le_iff_disj)
  then have "1 \<le> size_max ta tb / size_min ta tb"
    by (simp add: pos_le_divide_eq)
  then have lg: "1 \<le> log 2 (size_max ta tb / size_min ta tb + 1)"
    by (subst one_le_log_cancel_iff) linarith+
  have "size_min ta tb * 1 \<le> size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1)"
    by (intro mult_left_mono) (use m1 lg in auto)
  then show "size_min ta tb \<le> size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1)"
    by simp
  then show "1 \<le> size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1)"
    using m1 by linarith
qed

corollary W_bound_absorb:
  fixes W jw k c :: real
  assumes invs: "inv ta" "inv tb"
  assumes decomp: "W \<le> 1 + length (split_parts ta tb) + jw + split_work ta tb"
  assumes jw_piv: "jw \<le> (\<Sum>t \<leftarrow> split_parts ta tb. k + c * rank t)"
  assumes k_pos: "0 < k" and c_pos: "0 < c"
  shows "W \<le> (1 + K_lin k c + K_log k c)
             * (size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1))"
proof -
  let ?g = "size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1)"
  have lin: "K_lin k c * size_min ta tb \<le> K_lin k c * ?g"
    using mlog_ge(2) K_lin_nonneg k_pos c_pos by (intro mult_left_mono) auto
  have "W \<le> 1 + K_lin k c * size_min ta tb + K_log k c * ?g"
    using W_bound_generic'[OF assms] .
  also have "\<dots> \<le> ?g + K_lin k c * ?g + K_log k c * ?g"
    using mlog_ge(1)[of ta tb] lin by linarith
  also have "\<dots> = (1 + K_lin k c + K_log k c) * ?g"
    by algebra
  finally show ?thesis .
qed

  
text \<open>
  The formal argument uses the machinery defined in
  @{theory "HOL-Library.Going_To_Filter"}. Intuitively, the filter defined 
  below is generated by a collection of regions of trees i.e. for every 
  threshold $N$ the region $A_N$ contains all invariant trees of size at least $N$. 
  The regions are obviously nested i.e. $A_0 \supseteq A_1 \supseteq A_2 \supseteq \dots$.
  \<close>

definition tree_filter :: "('a \<times> 'b) tree filter" where
  "tree_filter = size going_to at_top within {t. inv t}"

text \<open>
  The connection to Big-O notation is the notion of \<open>eventually\<close>. 
  A predicate $P$ holds eventually in the filter iff $P$ holds on some region 
  $A_N$, i.e. iff there is a threshold $N$ such that $P$ holds for \<open>every\<close> 
  invariant tree of size at least $N$. In other words, for all sufficiently 
  large valid inputs.
  \<close>

lemma eventually_tree_filter: "eventually (\<lambda>t. inv t \<and> 1 \<le> size t) tree_filter"
proof -
  have "\<forall>t. inv t \<longrightarrow> 1 \<le> size t \<longrightarrow> inv t \<and> 1 \<le> size t"
    by fast
  then have "eventually (\<lambda>t. inv t \<and> 1 \<le> size t) (size going_to at_top within {t. inv t})"
    using eventually_going_to_at_top_linorder by force
  then show ?thesis 
    unfolding tree_filter_def .
qed


text \<open>
  The argument could already proceed here, but there is one pitfall. Nothing so far
  guarantees that the regions $A_N$ are non-empty. Suppose some $A_N$ were empty.
  Then \<^emph>\<open>every\<close> predicate, including $\lambda t.\ \mathit{False}$,  
  would hold on all elements of $A_N$, as there are none. 
  Since @{text eventually} only requires
  one witness region, every statement whatsoever would then hold eventually and the
  filter collapses to the degenerate filter @{term bot}. Every asymptotic
  statement over it becomes vacuously true. Note that such statements would still
  be provable, they would merely carry no information. The following lemma constructs, 
  for every $N$, an invariant tree of size exactly $N$, hence a member of $A_N$.
\<close>

lemma exists_inv_tree_of_size: "\<exists>t. inv t \<and> size t = N"
proof (induction N)
  case 0
  show ?case 
    using inv_Leaf by force
next
  case (Suc N)
  then obtain t where t: "inv t" "size t = N" 
    by blast
  from t have "inv (join t a Leaf)" "size (join t a Leaf) = Suc N"
    by (auto simp: join_size inv_Leaf intro: inv_join)
  then show ?case 
    by blast
qed

text \<open>Properness is now immediate.\<close>

lemma tree_filter_proper: "tree_filter \<noteq> bot"
proof
  assume "tree_filter = bot"
  then have "eventually (\<lambda>t. False) tree_filter"
    by (simp add: eventually_False)
  then obtain C where C: "\<forall>t \<in> {t. inv t}. C \<le> size t \<longrightarrow> False"
    unfolding tree_filter_def eventually_going_to_at_top_linorder by blast
  obtain t :: "('a \<times> 'b) tree" where "inv t" "size t = C"
    using exists_inv_tree_of_size by blast
  with C show False 
    by auto
qed


text \<open>
  Because the work functions operate on pairs of trees, the product filter is used
  to extend @{term tree_filter} to a filter on pairs. As the bound is symmetric in the
  two sizes, no restriction on their order is needed.\<close>

definition tree_pair_filter :: "((('a \<times> 'b) tree) \<times> ('a \<times> 'b) tree) filter" where
  "tree_pair_filter = tree_filter \<times>\<^sub>F tree_filter"

corollary tree_pair_filter_proper: "tree_pair_filter \<noteq> bot"
  by (simp add: tree_pair_filter_def prod_filter_eq_bot tree_filter_proper)

corollary eventually_tree_pair_filter:
"eventually (\<lambda>x. (\<lambda>t. inv t \<and> 1 \<le> size t) (fst x) \<and> (\<lambda>t. inv t \<and> 1 \<le> size t) (snd x)) 
  (tree_filter \<times>\<^sub>F tree_filter)"
  using eventually_prodI[OF eventually_tree_filter eventually_tree_filter] by simp

text \<open>Finally, the Big-O bound can be stated.\<close>
theorem W_bound_bigo_generic:
  fixes W jw :: "('a \<times> 'b) tree \<Rightarrow> ('a \<times> 'b) tree \<Rightarrow> real"
    and k c :: real
  assumes W_nonneg: "\<And>ta tb. 0 \<le> W ta tb"
  assumes decomp: "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk>
      \<Longrightarrow> W ta tb \<le> 1 + length (split_parts ta tb) + jw ta tb + split_work ta tb"
  assumes jw_piv: "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk>
      \<Longrightarrow> jw ta tb \<le> (\<Sum>t \<leftarrow> split_parts ta tb. k + c * rank t)"
  assumes k_pos: "0 < k" and c_pos: "0 < c"
  shows "(\<lambda>(ta, tb). W ta tb) \<in> O[tree_pair_filter](\<lambda>(ta, tb).
           size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1))"
proof -
  let ?K = "1 + K_lin k c + K_log k c"
  let ?W = "(\<lambda>(ta, tb). W ta tb)"
  let ?g = "(\<lambda>(ta, tb). size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1))"

  \<comment>\<open>First, plug in the bound computed above\<close>
  have "W ta tb \<le> ?K * (size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1))"
    if "inv ta" "inv tb" for ta tb
    using W_bound_absorb[OF that decomp[OF that] jw_piv[OF that] k_pos c_pos] .

  \<comment>\<open>The right-hand side is non-negative; together with \<open>W_nonneg\<close> this allows
     the norms in the Big-O form to be introduced later on\<close>
  moreover have nonneg: "0 \<le> size_min t u * log 2 (size_max t u / size_min t u + 1)"
    for t u :: "('a \<times> 'b) tree"
    by (simp add: log_def)

  (* Note: The transformations below can be collapsed into a single automation step,
     but are written out on purpose as to make it clear how the proof proceeds internally. *)
  \<comment>\<open>On the product filter both components are eventually invariant and of size at
     least one (the witness region is $A_1 \times A_1$), which supplies every
     assumption of the pointwise bound.\<close>
  ultimately have "eventually (\<lambda>(ta, tb).
          W ta tb \<le> ?K * (size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1)))
        tree_pair_filter"
    unfolding tree_pair_filter_def
    using eventually_tree_pair_filter by (auto elim: eventually_mono)

  \<comment>\<open>Since both sides of the inequality are non-negative, the norms demanded by the
     Big-O definition can be introduced\<close>
  then have "eventually (\<lambda>x. norm (?W x) \<le> ?K * norm (?g x)) tree_pair_filter"
    by (auto simp: W_nonneg nonneg elim: eventually_mono)

  \<comment>\<open>Which can be directly restated in the form required for Big-O.\<close>
  then have "\<exists>b > 0. eventually (\<lambda>x. norm (?W x) \<le> b * norm (?g x)) tree_pair_filter"
    using K_lin_log_pos k_pos c_pos less_imp_le by meson

  then show ?thesis
    by blast
qed

text \<open>Which also begets the canonical form phrased in terms of the natural logarithm.\<close>
corollary W_bound_bigo_generic_ln:
  fixes W jw :: "('a \<times> 'b) tree \<Rightarrow> ('a \<times> 'b) tree \<Rightarrow> real"
    and k c :: real
  assumes W_nonneg: "\<And>ta tb. 0 \<le> W ta tb"
  assumes decomp: "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk>
      \<Longrightarrow> W ta tb \<le> 1 + length (split_parts ta tb) + jw ta tb + split_work ta tb"
  assumes jw_piv: "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk>
      \<Longrightarrow> jw ta tb \<le> (\<Sum>t \<leftarrow> split_parts ta tb. k + c * rank t)"
  assumes k_pos: "0 < k" and c_pos: "0 < c"
  shows "(\<lambda>(ta, tb). W ta tb) \<in> O[tree_pair_filter](\<lambda>(ta, tb).
           size_min ta tb * ln (size_max ta tb / size_min ta tb + 1))"
proof -
  let ?f = "\<lambda>(ta, tb). size_min ta tb * log 2 (size_max ta tb / size_min ta tb + 1)"
  let ?g = "\<lambda>(ta, tb). size_min ta tb * ln (size_max ta tb / size_min ta tb + 1)"

  have *:"?f = (\<lambda>x. (1 / (ln 2)) * ?g x)"
    using log_def by auto 
  have "O[tree_pair_filter](\<lambda>x. (1 / (ln 2)) * ?g x) = O[tree_pair_filter](?g)"
    by simp
  then show ?thesis
    using W_bound_bigo_generic[OF W_nonneg decomp jw_piv k_pos c_pos] by(simp add: *)
qed

section \<open>Union\<close>

text\<open>Start by defining the work function and show it decomposes as split- and join-work.\<close>

fun W_union :: "('a * 'b) tree \<Rightarrow> ('a * 'b) tree \<Rightarrow> real" where
"W_union t1 t2 =
  (if t1 = Leaf then 1
   else if t2 = Leaf then 1
   else case t1 of Node l1 (a,_) r1 \<Rightarrow>
     (let (l2, _, r2) = split a t2;
          l' = union l1 l2;
          r' = union r1 r2
      in 1
         + W_split t2 a
         + W_union l1 l2
         + W_union r1 r2
         + W_join l' a r'))"

fun join_work_union :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> real" where
"join_work_union t1 t2 =
  (if t1 = Leaf then 0 else
   if t2 = Leaf then 0 else
   case t1 of Node l1 (a, _) r1 \<Rightarrow>
   let (l2,_ ,r2) = split a t2;
       l' = union l1 l2; r' = union r1 r2
   in 1 + W_join l' a r' + join_work_union l1 l2 + join_work_union r1 r2)"

declare W_union.simps[simp del]
declare join_work_union.simps[simp del]

lemma W_union_work_bound:
  assumes "inv t1" "inv t2"
  shows "W_union t1 t2
       \<le> 1 + length (split_parts t1 t2) + join_work_union t1 t2 + split_work t1 t2"
  using assms
proof (induction t1 t2 rule: W_union.induct)
  case (1 t1 t2)
  then show ?case
    by (fastforce simp: W_union.simps[of t1 t2] split_work.simps[of t1 t2]
                        join_work_union.simps[of t1 t2] split_parts.simps[of t1 t2]
                        inv_union split_inv
                  split: prod.splits tree.splits
                  dest: split_inv)
qed

subsection \<open>Bounding join-work\<close>

text \<open>
  To instantiate the generic work bound, the join-work needs to fit the cost model.
  First, show that \<open>union\<close> produces results whose rank is bounded by the ranks of
  the input trees. The upper bound is a consequence of \<open>rule_sub\<close>. The lower
  bound combines balance, monotonicity and @{thm [source] split_rank_min}. 
  \<close>

lemma union_rank_upper: "\<lbrakk>inv t1; inv t2\<rbrakk> \<Longrightarrow> rank (union t1 t2) \<le> rank t1 + rank t2"
proof (induction t1 t2 rule: union.induct)
  case (1 t1 t2)
  consider (leaves) "t1 = Leaf \<or> t2 = Leaf" | (nodes) "t1 \<noteq> Leaf \<and> t2 \<noteq> Leaf" by auto
  then show ?case
  proof cases
    case leaves
    then show ?thesis
      using "1.prems" by (auto simp: union.simps[of t1 t2] rule_empty)
  next
    case nodes
    then obtain l1 a b r1 where t1_def: "t1 = Node l1 (a, b) r1"
      by (cases t1) auto
    obtain l2 f r2 where SPL: "split a t2 = (l2, f, r2)"
      by (cases "split a t2") auto
    have inv_sub: "inv l1" "inv r1" "inv l2" "inv r2"
      using "1.prems" t1_def SPL by auto
    let ?tl = "union l1 l2" and ?tr = "union r1 r2"

    have res: "union t1 t2 = join ?tl a ?tr"
      using nodes by (simp add: t1_def SPL union.simps[of "Node l1 (a, b) r1" t2])
    have IHl: "rank ?tl \<le> rank l1 + rank l2" and IHr: "rank ?tr \<le> rank r1 + rank r2"
      using 1 nodes t1_def SPL inv_sub by simp_all
    have "rank ?tl \<le> rank l1 + rank t2" "rank ?tr \<le> rank r1 + rank t2"
      using IHl IHr split_rank[OF SPL "1.prems"(2)] by linarith+
    then have "rank (join ?tl a ?tr) \<le> rank t1 + rank t2"
      using rule_sub[of ?tl l1 "rank t2" ?tr r1 a b] inv_union inv_sub "1.prems"(1)
      by (simp add: t1_def)
    then show ?thesis
      using res by simp
  qed
qed

lemma union_rank_lower: "\<lbrakk>inv t1; inv t2\<rbrakk> \<Longrightarrow> rank t1 \<le> rank (union t1 t2) + (c\<^sub>u / c\<^sub>l) * rank t2"
proof (induction t1 t2 rule: union.induct)
  case (1 t1 t2)
  have kappa: "0 \<le> c\<^sub>u / c\<^sub>l"
    using c_vals by simp
  consider (leaves) "t1 = Leaf \<or> t2 = Leaf" | (nodes) "t1 \<noteq> Leaf \<and> t2 \<noteq> Leaf" by auto
  then show ?case
  proof cases
    case leaves
    have nn: "0 \<le> (c\<^sub>u / c\<^sub>l) * rank t2"
      using kappa rank_pos'[OF "1.prems"(2)] mult_nonneg_nonneg by force
    show ?thesis
    using nn rank_pos'[OF "1.prems"(2)] rule_empty leaves 
    by (cases "t1 = Leaf") (auto simp: union.simps)
  next
    case nodes
    then obtain l1 a b r1 where t1_def: "t1 = Node l1 (a, b) r1"
      by (cases t1) auto
    obtain l2 f r2 where SPL: "split a t2 = (l2, f, r2)"
      by (cases "split a t2") auto
    have inv_sub: "inv l1" "inv r1" "inv l2" "inv r2"
      using "1.prems" t1_def SPL by auto
    let ?k = "c\<^sub>u / c\<^sub>l"
    let ?tl = "union l1 l2" and ?tr = "union r1 r2"

    have IHl: "rank l1 \<le> rank ?tl + ?k * rank l2" and IHr: "rank r1 \<le> rank ?tr + ?k * rank r2"
      using 1 nodes t1_def SPL inv_sub by auto
    have mono: "max (rank ?tl) (rank ?tr) \<le> rank (join ?tl a ?tr)"
      using rule_mono inv_union inv_sub by blast
    have bal: "rank t1 \<le> min (rank l1) (rank r1) + c\<^sub>u"
      using inv_children_explD(3,4)[of l1 "(a,b)" r1] "1.prems"(1) t1_def by auto
    have pieces: "min (rank l2) (rank r2) \<le> rank t2 - c\<^sub>l"
      using split_rank_min[OF "1.prems"(2) _ SPL] nodes by simp

    have "rank t1 \<le> min (rank ?tl + ?k * rank l2) (rank ?tr + ?k * rank r2) + c\<^sub>u"
      using bal IHl IHr min.mono by fastforce
    also have "\<dots> \<le> max (rank ?tl) (rank ?tr) + ?k * min (rank l2) (rank r2) + c\<^sub>u"
    by (cases "rank l2 \<le> rank r2") fastforce+
    also have "\<dots> \<le> rank (join ?tl a ?tr) + ?k * (rank t2 - c\<^sub>l) + c\<^sub>u"
      using mono mult_left_mono[OF pieces kappa] by linarith
    also have "\<dots> = rank (join ?tl a ?tr) + ?k * rank t2"
      using c_vals by (simp add: field_simps)
    finally show ?thesis
      using nodes by (simp add: t1_def SPL union.simps[of "Node l1 (a, b) r1" t2])
  qed
qed

text \<open>With the two results above, the join-work of every step is bounded by a
  constant plus a constant multiple of the rank of the tree being split. The
  constants are named after the generic bound they feed into.\<close>

abbreviation "KJ_union \<equiv> (1 + c\<^sub>\<delta>)"
abbreviation "KJc_union \<equiv> (1 + c\<^sub>u / c\<^sub>l)"

lemma KJ_union_pos: "0 < 1 + c\<^sub>\<delta>"
  using c\<^sub>\<delta>_def c_vals by linarith

lemma KJc_union_pos: "0 < 1 + c\<^sub>u / c\<^sub>l"
  using c_vals by (simp add: add_pos_nonneg)

fun join_work_union' :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> real" where
"join_work_union' t1 t2 =
  (if t1 = Leaf then 0 else
   if t2 = Leaf then 0 else
   case t1 of Node l1 (a, _) r1 \<Rightarrow>
   let (l2,_ ,r2) = split a t2
   in 1 + c\<^sub>\<delta> + KJc_union * rank t2 + join_work_union' l1 l2 + join_work_union' r1 r2)"

lemma join_work_bounded:
  assumes "inv t1" "inv t2"
  shows "join_work_union t1 t2 \<le> join_work_union' t1 t2"
using assms
proof (induction t1 t2 rule: join_work_union.induct)
  case (1 t1 t2)
  show ?case
  proof (cases "t1 = Leaf \<or> t2 = Leaf")
    case True
    then show ?thesis by (auto simp: join_work_union.simps)
  next
    case nodes: False
    then obtain l1 x b r1 where t1_def: "t1 = Node l1 (x, b) r1"
      by (cases t1) auto
    obtain l2 b' r2 where split_def: "split x t2 = (l2, b', r2)"
      by (cases "split x t2") auto
    have inv_sub: "inv l1" "inv r1" "inv l2" "inv r2"
      using "1.prems" t1_def split_def by auto

    let ?l = "union l1 l2"
    let ?r = "union r1 r2"

    have IH: "join_work_union l1 l2 \<le> join_work_union' l1 l2"
             "join_work_union r1 r2 \<le> join_work_union' r1 r2"
      using 1 split_inv by (metis inv_Node local.split_def nodes t1_def)+

    have Wj: "W_join ?l x ?r \<le> c\<^sub>\<delta> + KJc_union * rank t2"
    proof -
      have up: "rank ?l \<le> rank l1 + rank l2" "rank ?r \<le> rank r1 + rank r2"
        using union_rank_upper inv_sub by blast+
      have lo: "rank l1 \<le> rank ?l + (c\<^sub>u / c\<^sub>l) * rank l2"
              "rank r1 \<le> rank ?r + (c\<^sub>u / c\<^sub>l) * rank r2"
        using union_rank_lower inv_sub by blast+
      have pieces: "rank l2 \<le> rank t2" "rank r2 \<le> rank t2"
        using split_rank[OF split_def "1.prems"(2)] by simp_all
      then have "(c\<^sub>u / c\<^sub>l) * rank l2 \<le> (c\<^sub>u / c\<^sub>l) * rank t2"
                "(c\<^sub>u / c\<^sub>l) * rank r2 \<le> (c\<^sub>u / c\<^sub>l) * rank t2"
        using c_vals by (intro mult_left_mono; simp)+
      moreover have "\<bar>rank l1 - rank r1\<bar> \<le> c\<^sub>\<delta>"
        using dmax' t1_def "1.prems"(1) by blast
      ultimately show ?thesis
        using up lo pieces unfolding W_join_def by (simp add: abs_le_iff algebra_simps)
    qed

    have "join_work_union t1 t2 = 1 + W_join ?l x ?r + join_work_union l1 l2 + join_work_union r1 r2"
      using t1_def split_def nodes by (auto simp: join_work_union.simps split.simps split: prod.splits if_split)
    also have "... \<le> 1 + c\<^sub>\<delta> + KJc_union * rank t2 + join_work_union' l1 l2 + join_work_union' r1 r2"
      using Wj IH by linarith
    also have "... = join_work_union' t1 t2"
      using t1_def split_def nodes by (auto simp: split.simps split: prod.splits if_split)
    finally show ?thesis .
  qed
qed

lemma join_work_union'_as_sum:
  "join_work_union' t1 t2 = (\<Sum>t \<leftarrow> split_parts t1 t2. KJ_union + KJc_union * rank t)"
proof (induction t1 t2 rule: split_parts.induct)
  case (1 t1 t2)
  then show ?case
    by (force simp: join_work_union'.simps[of t1 t2] split_parts.simps[of t1 t2]
                 split: tree.splits prod.split)
qed

corollary join_work_union_le_sum_rank:
  assumes "inv t1" "inv t2"
  shows "join_work_union t1 t2 \<le> (\<Sum>t \<leftarrow> split_parts t1 t2. KJ_union + KJc_union * rank t)"
  using join_work_bounded[OF assms] join_work_union'_as_sum by auto

subsection \<open>Final bound\<close>

text \<open>The step of the set operations charges its unit of work against the final join,
  absorbing the constants of @{thm [source] rule_cost_W} into @{term K_T}. This form is
  shared by the union and intersection bridges.\<close>
lemma rule_cost_K_T:
  assumes "inv l" "inv r"
  shows "1 + real (T_join l a r) \<le> K_T + K_T * W_join l a r"
proof -
  have "1 + real (T_join l a r) \<le> (1 + k\<^sub>0) + k\<^sub>1 * W_join l a r"
    using rule_cost_W[OF assms] by fastforce
  also have "\<dots> \<le> K_T + K_T * W_join l a r"
    using K_T_ge_1_plus_k0 K_T_ge_k1 by (intro add_mono mult_right_mono) auto
  finally show ?thesis .
qed

text \<open>Writing out the \<open>union\<close> specific induction step enables complete automation.\<close>

lemma rule_cost_step_union:
  assumes "inv l" "inv r"
      and "real t\<^sub>s \<le> K_T * w\<^sub>s" "real t\<^sub>l \<le> K_T * w\<^sub>l" "real t\<^sub>r \<le> K_T * w\<^sub>r"
  shows "1 + (real t\<^sub>s + (real t\<^sub>l + (real t\<^sub>r + real (T_join l a r))))
         \<le> K_T * (1 + w\<^sub>s + w\<^sub>l + w\<^sub>r + W_join l a r)"
proof -
  have "K_T * (1 + w\<^sub>s + w\<^sub>l + w\<^sub>r + W_join l a r)
        = K_T * w\<^sub>s + K_T * w\<^sub>l + K_T * w\<^sub>r + (K_T + K_T * W_join l a r)"
    by (simp add: algebra_simps)
  then show ?thesis
    using assms(3-5) rule_cost_K_T[OF assms(1,2), where a=a] by linarith
qed

time_fun union equations union.simps
declare T_union.simps[simp del]

lemma T_union_bridge:
  "\<lbrakk>inv t1; inv t2\<rbrakk> \<Longrightarrow> real (T_union t1 t2) \<le> K_T * W_union t1 t2"
proof (induction t1 t2 rule: union.induct)
  case (1 t1 t2)
  then show ?case
    using K_T_ge_1
    by (fastforce simp: T_union.simps[of t1 t2] W_union.simps[of t1 t2] inv_union split_inv
                  intro!: rule_cost_step_union T_split_bridge
                  split: tree.splits prod.splits)
qed

text\<open>The generic work bounds can be instantiated directly.\<close>

theorem W_union_bound:
  assumes "inv t1" "inv t2"
  shows "W_union t1 t2
       \<le> 1 + K_lin KJ_union KJc_union * size_min t1 t2
         + K_log KJ_union KJc_union * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have jw: "join_work_union t1 t2 \<le> (\<Sum>t \<leftarrow> split_parts t1 t2. KJ_union + KJc_union * rank t)"
    using join_work_union_le_sum_rank[OF assms] by simp
  show ?thesis
    using W_bound_generic'[OF assms W_union_work_bound[OF assms] jw KJ_union_pos KJc_union_pos]
    by simp
qed

corollary T_union_bound:
  assumes "inv t1" "inv t2"
  shows "real (T_union t1 t2)
       \<le> K_T + (K_T * K_lin KJ_union KJc_union) * size_min t1 t2
         + (K_T * K_log KJ_union KJc_union) * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (T_union t1 t2) \<le> K_T * W_union t1 t2"
    using T_union_bridge assms(1,2) by simp
  also have "\<dots> \<le> K_T * (1 + K_lin KJ_union KJc_union * size_min t1 t2 +
     K_log KJ_union KJc_union * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1)))"
    using W_union_bound[OF assms] K_T_ge_1 by auto
  also have "\<dots> = K_T + (K_T * K_lin KJ_union KJc_union) * size_min t1 t2 +
    (K_T * K_log KJ_union KJc_union) * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    by argo
  finally show ?thesis .
qed

text \<open>The generic asymptotic bound requires the work functions to be nonnegative.\<close>

lemma W_split_nonneg: "0 \<le> W_split t x"
  by (induction t x rule: W_split.induct)
     (auto split: cmp_val.split prod.split)

lemma W_union_nonneg: "0 \<le> W_union t1 t2"
proof (induction t1 t2 rule: W_union.induct)
  case (1 t1 t2)
  then show ?case
    by (auto simp: W_union.simps[of t1 t2] 
             intro!: add_nonneg_nonneg W_split_nonneg
             split: tree.splits prod.splits)
qed

theorem W_union_bigo:
 "(\<lambda>(t1, t2). W_union t1 t2) \<in> O[tree_pair_filter](\<lambda>(t1,t2).
   size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "\<And>ta tb. 0 \<le> W_union ta tb"
    by (rule W_union_nonneg)
  moreover have "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk> \<Longrightarrow> W_union ta tb
      \<le> 1 + length (split_parts ta tb) + join_work_union ta tb + split_work ta tb"
    using W_union_work_bound by blast
  moreover have "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk>
      \<Longrightarrow> join_work_union ta tb \<le> (\<Sum>t \<leftarrow> split_parts ta tb. KJ_union + KJc_union * rank t)"
    using join_work_union_le_sum_rank by fastforce
  ultimately show ?thesis
    using KJ_union_pos KJc_union_pos W_bound_bigo_generic_ln[where k=KJ_union and c=KJc_union] by force
qed

text \<open>The time bound follows from transitivity of Big-O.\<close>

corollary T_union_bigo:
 "(\<lambda>(t1, t2). real (T_union t1 t2)) \<in> O[tree_pair_filter](\<lambda>(t1,t2).
   size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "eventually (\<lambda>x. norm ((\<lambda>(t1, t2). real (T_union t1 t2)) x)
          \<le> K_T * norm ((\<lambda>(t1, t2). W_union t1 t2) x)) tree_pair_filter"
    unfolding tree_pair_filter_def using eventually_tree_pair_filter
    by (auto simp: W_union_nonneg elim!: eventually_mono intro!: T_union_bridge)
  then have "(\<lambda>(t1, t2). real (T_union t1 t2))
      \<in> O[tree_pair_filter](\<lambda>(t1, t2). W_union t1 t2)"
    using bigoI by fast
  then show ?thesis
    using W_union_bigo landau_o.big_trans by blast
qed

section \<open>Intersection\<close>

text\<open>Start by defining the work function and show it decomposes into the split- and join-work.\<close>

fun W_inter :: "('a * 'b) tree \<Rightarrow> ('a * 'b) tree \<Rightarrow> real" where
"W_inter t1 t2 =
  (if t1 = Leaf then 1
   else if t2 = Leaf then 1
   else case t1 of Node l1 (a,_) r1 \<Rightarrow>
     (let (l2, b, r2) = split a t2;
          l' = inter l1 l2;
          r' = inter r1 r2
      in 1  
         + W_split t2 a
         + (if b then W_join l' a r' else W_join2 l' r')
         + W_inter l1 l2
         + W_inter r1 r2
         ))"

fun join_work_inter :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> real" where
"join_work_inter t1 t2 =
  (if t1 = Leaf then 0 else
   if t2 = Leaf then 0 else
   case t1 of Node l1 (a, _) r1 \<Rightarrow>
   let (l2,b ,r2) = split a t2;
       l' = inter l1 l2; r' = inter r1 r2
   in 1 + (if b then W_join l' a r' else W_join2 l' r') + join_work_inter l1 l2 + join_work_inter r1 r2)"

declare W_inter.simps[simp del]
declare join_work_inter.simps[simp del]

lemma W_inter_work_bound:
  assumes "inv t1" "inv t2"
  shows "W_inter t1 t2
       \<le> 1 + length (split_parts t1 t2) + join_work_inter t1 t2 + split_work t1 t2"
  using assms
proof (induction t1 t2 rule: W_inter.induct)
  case (1 t1 t2)
  then show ?case
    by (fastforce simp: W_inter.simps[of t1 t2] split_work.simps[of t1 t2]
                        join_work_inter.simps[of t1 t2] split_parts.simps[of t1 t2]
                        inv_inter split_inv
                  split: prod.splits tree.splits
                  dest: split_inv)
qed


subsection \<open>Bounding join-work\<close>

text\<open>The rank-based argument for @{term union} does not carry over, as there is no
 submodularity rule for @{term join2}. By nature of the operation, however, the size
 of the resulting tree can be bounded directly.\<close>
lemma inter_size_bound:
  assumes "inv t1" "inv t2"
  shows "size (inter t1 t2) \<le> size t2"
using assms
proof (induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  show ?case
  proof (cases "t1 = Leaf \<or> t2 = Leaf")
    case True
    then show ?thesis using inter.simps by auto
  next
    case False
    then obtain l1 a b r1 where t1_def: "t1 = Node l1 (a, b) r1"
      by (cases t1) auto
    obtain l2 f r2 where SPL: "split a t2 = (l2, f, r2)"
      by (cases "split a t2") auto
    have invs: "inv l1" "inv r1" "inv l2" "inv r2"
      using "1.prems" t1_def SPL inv_Node split_inv by metis+
    have IHl: "size (inter l1 l2) \<le> size l2" and IHr: "size (inter r1 r2) \<le> size r2"
      using "1.IH" False t1_def SPL invs by auto
    have result: "inter t1 t2 = (if f then join (inter l1 l2) a (inter r1 r2)
                                      else join2 (inter l1 l2) (inter r1 r2))"
      using False t1_def SPL by (auto simp: inter.simps split: prod.splits tree.splits)
    show ?thesis
    proof (cases f)
      case True
      then have "size (inter t1 t2) = size (inter l1 l2) + size (inter r1 r2) + 1"
        using result join_size inv_inter invs by auto
      moreover have "size l2 + size r2 = size t2 - 1"
        using split_size_true SPL True "1.prems"(2) by (metis (full_types))
      moreover have "0 < size t2"
        using False by (cases t2) auto
      ultimately show ?thesis
        using IHl IHr by linarith
    next
      case FalseF: False
      then have "size (inter t1 t2) = size (inter l1 l2) + size (inter r1 r2)"
        using result join2_size inv_inter invs by auto
      then show ?thesis
        using IHl IHr split_size[OF SPL[symmetric] "1.prems"(2)] by linarith
    qed
  qed
qed

text \<open>By balance, \<open>size\<close> can be exchanged for \<open>rank\<close> to arrive at a shape required 
  for the generic work bound. This pattern is re-used by difference.\<close>
lemma log_size1_le_rank_ratio:
  assumes "inv t"
  shows "c\<^sub>u * log 2 (size1 t) \<le> (c\<^sub>u / c\<^sub>l) * rank t + c\<^sub>u"
proof -
  have "real (size1 t) \<le> 2 ^ height t"
    using size1_height by auto
  then have "log 2 (real (size1 t)) \<le> log 2 (2 ^ height t)"
    by (intro log_mono) auto
  then have "log 2 (size1 t) \<le> height t"
     by fastforce
  also have "... \<le> rank t / c\<^sub>l + 1"
    using rank_lower_height_inverse' assms by fastforce
  finally have "c\<^sub>u * log 2 (size1 t) \<le> c\<^sub>u * (rank t / c\<^sub>l + 1)"
    using c_vals assms rank_lower_height_inverse' by auto
  then show ?thesis by argo
qed

corollary inter_rank_le_log_size:
  assumes "inv t1" "inv t2"
  shows "rank (inter t1 t2) \<le> c\<^sub>u * log 2 (size1 t2)"
proof -
  have "inv (inter t1 t2)" 
    using assms inv_inter by auto
  then have "rank (inter t1 t2) \<le> c\<^sub>u * log 2 (size1 (inter t1 t2))"
    using rank_le_cu_log_size1 by blast
  also have "... \<le> c\<^sub>u * log 2 (size1 t2)"
    using inter_size_bound[OF assms] c_vals by (simp add: size1_size)
  finally show ?thesis .
qed

text\<open>The join work can thus be bounded.\<close>

fun join_work_inter' :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> real" where
"join_work_inter' t1 t2 =
  (if t1 = Leaf then 0 else
   if t2 = Leaf then 0 else
   case t1 of Node l1 (a, _) r1 \<Rightarrow>
   let (l2, _, r2) = split a t2;
       l' = inter l1 l2; r' = inter r1 r2
   in 1 + W_join l' a r' + 1 + c\<^sub>u + K_min * rank r'
      + join_work_inter' l1 l2 + join_work_inter' r1 r2)"

declare join_work_inter'.simps[simp del]

lemma join_work_inter_le_inter':
  assumes "inv t1" "inv t2"
  shows "join_work_inter t1 t2 \<le> join_work_inter' t1 t2"
using assms
proof (induction t1 t2 rule: join_work_inter.induct)
  case (1 t1 t2)
  show ?case
  proof (cases "t1 = Leaf \<or> t2 = Leaf")
    case True
    then show ?thesis
      by (auto simp: join_work_inter.simps join_work_inter'.simps)
  next
    case False
    then obtain l1 a b r1 where t1_def: "t1 = Node l1 (a, b) r1"
      by (cases t1) auto
    obtain l2 f r2 where SPL: "split a t2 = (l2, f, r2)"
      by (cases "split a t2") auto
    have inv_l1: "inv l1" and inv_r1: "inv r1"
      using "1.prems"(1) t1_def inv_Node by blast+
    have inv_l2: "inv l2" and inv_r2: "inv r2"
      using SPL "1.prems"(2) split_inv by metis+

    have "W_join2 (inter l1 l2) (inter r1 r2)
        \<le> W_join (inter l1 l2) a (inter r1 r2) + 1 + c\<^sub>u + K_min * rank (inter r1 r2)"
      using W_join2_bounded[OF inv_inter[OF inv_l1 inv_l2] inv_inter[OF inv_r1 inv_r2]] .
    moreover have "join_work_inter l1 l2 \<le> join_work_inter' l1 l2"
      using "1.IH" False t1_def SPL inv_l1 inv_l2 by auto
    moreover have "join_work_inter r1 r2 \<le> join_work_inter' r1 r2"
      using "1.IH" False t1_def SPL inv_r1 inv_r2 by auto
    moreover have "K_min * rank (inter r1 r2) \<ge> 0"
      using K_min_def c1_pos c_vals rank_pos'[OF inv_inter[OF inv_r1 inv_r2]]
      by (auto intro: mult_nonneg_nonneg divide_nonneg_pos)
    ultimately  show ?thesis using False t1_def SPL c_vals
      by (auto simp: join_work_inter.simps[of "Node l1 (a,b) r1" t2]
                     join_work_inter'.simps[of "Node l1 (a,b) r1" t2])
  qed
qed

lemma cu_log_size1_mono:
  fixes s t :: "('a * 'b) tree"
  assumes "size s \<le> size t"
  shows "c\<^sub>u * log 2 (size1 s) \<le> c\<^sub>u * log 2 (size1 t)"
  using assms c_vals by (auto simp: size1_size intro: mult_left_mono log_mono)

lemma join_work_inter'_as_sum:
  assumes "inv t1" "inv t2"
  shows "join_work_inter' t1 t2
       \<le> (\<Sum>t \<leftarrow> split_parts t1 t2.
            2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t))"
using assms
proof (induction t1 t2 rule: split_parts.induct)
  case (1 t1 t2)
  show ?case
  proof (cases "t1 = Leaf \<or> t2 = Leaf")
    case True
    then show ?thesis
      by (auto simp: join_work_inter'.simps split_parts.simps)
  next
    case False
    then obtain l1 a b r1 where t1_def: "t1 = Node l1 (a, b) r1"
      by (cases t1) auto
    obtain l2 f r2 where SPL: "split a t2 = (l2, f, r2)"
      by (cases "split a t2") auto
    have inv_l1: "inv l1" and inv_r1: "inv r1" and inv_l2: "inv l2" and inv_r2: "inv r2"
      using "1.prems" t1_def SPL inv_Node split_inv by metis+
    have inv_il: "inv (inter l1 l2)" and inv_ir: "inv (inter r1 r2)"
      using inv_inter inv_l1 inv_r1 inv_l2 inv_r2 by auto
    have sz: "size l2 \<le> size t2" "size r2 \<le> size t2"
      using split_size[OF SPL[symmetric] "1.prems"(2)] by linarith+
    have rank_il: "rank (inter l1 l2) \<le> c\<^sub>u * log 2 (size1 t2)"
      using inter_rank_le_log_size[OF inv_l1 inv_l2] cu_log_size1_mono sz by force
    have rank_ir: "rank (inter r1 r2) \<le> c\<^sub>u * log 2 (size1 t2)"
      using inter_rank_le_log_size[OF inv_r1 inv_r2] cu_log_size1_mono sz by force

    have "W_join (inter l1 l2) a (inter r1 r2) \<le> 2 * c\<^sub>u * log 2 (size1 t2)"
      using rank_il rank_ir W_join_def rank_pos'[OF inv_il] rank_pos'[OF inv_ir]
      by (simp add: abs_le_iff)
    then have "1 + W_join (inter l1 l2) a (inter r1 r2) + 1 + c\<^sub>u + K_min * rank (inter r1 r2)
                  \<le> 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t2)"
      using mult_left_mono[OF rank_ir K_min_nonneg] by (simp add: algebra_simps)
    moreover have "split_parts t1 t2 = t2 # (split_parts l1 l2 @ split_parts r1 r2)"
      using False t1_def SPL by (simp add: split_parts.simps)
    moreover have "join_work_inter' t1 t2
        = 1 + W_join (inter l1 l2) a (inter r1 r2) + 1 + c\<^sub>u + K_min * rank (inter r1 r2)
          + join_work_inter' l1 l2 + join_work_inter' r1 r2"
      using False t1_def SPL
      by (auto simp: join_work_inter'.simps split: prod.splits)
    moreover have "join_work_inter' l1 l2
             \<le> (\<Sum>t \<leftarrow> split_parts l1 l2. 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t))"
     and "join_work_inter' r1 r2
             \<le> (\<Sum>t \<leftarrow> split_parts r1 r2. 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t))"
      using "1.IH" False t1_def SPL inv_l1 inv_r1 inv_l2 inv_r2 by auto
    ultimately show ?thesis
      by simp
  qed
qed

text \<open>Exchanging the log for the rank via @{thm [source] log_size1_le_rank_ratio} puts the
  sum directly into the shape @{term "k + c * rank t"} accepted by the generic bound.\<close>

abbreviation "KJk_inter \<equiv> 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u"
abbreviation "KJc_inter \<equiv> (2 + K_min) * c\<^sub>u / c\<^sub>l"

lemma join_work_inter_le_sum_rank:
  assumes "inv t1" "inv t2"
  shows "join_work_inter t1 t2
       \<le> (\<Sum>t \<leftarrow> split_parts t1 t2. KJk_inter + KJc_inter * rank t)"
proof -
  have pw: "2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t)
          \<le> KJk_inter + KJc_inter * rank t"
    if "t \<in> set (split_parts t1 t2)" for t
  proof -
    have inv_t: "inv t" using split_parts_inv[OF assms(2)] that by simp
    have "(2 + K_min) * (c\<^sub>u * log 2 (size1 t)) \<le> (2 + K_min) * ((c\<^sub>u / c\<^sub>l) * rank t + c\<^sub>u)"
      using log_size1_le_rank_ratio[OF inv_t] K_min_nonneg by (auto intro: mult_left_mono)
    then show ?thesis by argo
  qed

  have "join_work_inter t1 t2 \<le> join_work_inter' t1 t2"
    using join_work_inter_le_inter'[OF assms(1,2)] .
  also have "... \<le> (\<Sum>t \<leftarrow> split_parts t1 t2. 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t))"
    using join_work_inter'_as_sum[OF assms(1,2)] .
  also have "... \<le> (\<Sum>t \<leftarrow> split_parts t1 t2. KJk_inter + KJc_inter * rank t)"
    using pw by (intro sum_list_mono) auto
  finally show ?thesis .
qed

subsection \<open>Final bound\<close>

text\<open>The remaining is analogous to the instantiation for \<open>union\<close>.\<close>

lemma rule_cost_step_inter:
  assumes "inv l" "inv r"
      and "real t\<^sub>s \<le> K_T * w\<^sub>s" "real t\<^sub>l \<le> K_T * w\<^sub>l" "real t\<^sub>r \<le> K_T * w\<^sub>r"
  shows "1 + (real t\<^sub>s + (real t\<^sub>l + (real t\<^sub>r + real (T_join l a r))))
         \<le> K_T * (1 + w\<^sub>s + W_join l a r + w\<^sub>l + w\<^sub>r)"
proof -
  have "K_T * (1 + w\<^sub>s + W_join l a r + w\<^sub>l + w\<^sub>r)
        = K_T * w\<^sub>s + K_T * w\<^sub>l + K_T * w\<^sub>r + (K_T + K_T * W_join l a r)"
    by (simp add: algebra_simps)
  then show ?thesis
    using assms(3-5) rule_cost_K_T[OF assms(1,2), where a=a] by linarith
qed

lemma rule_cost_step_inter2:
  assumes "inv l" "inv r"
      and "real t\<^sub>s \<le> K_T * w\<^sub>s" "real t\<^sub>l \<le> K_T * w\<^sub>l" "real t\<^sub>r \<le> K_T * w\<^sub>r"
  shows "1 + (real t\<^sub>s + (real t\<^sub>l + (real t\<^sub>r + real (T_join2 l r))))
         \<le> K_T * (1 + w\<^sub>s + W_join2 l r + w\<^sub>l + w\<^sub>r)"
proof -
  have "K_T * (1 + w\<^sub>s + W_join2 l r + w\<^sub>l + w\<^sub>r)
        = K_T * w\<^sub>s + K_T * w\<^sub>l + K_T * w\<^sub>r + (K_T + K_T * W_join2 l r)"
    by argo
  then show ?thesis
    using assms(3-5) T_join2_bridge[OF assms(1,2)] K_T_ge_1 by linarith
qed

time_fun inter equations inter.simps
declare T_inter.simps[simp del]

lemma T_inter_bridge:
  "\<lbrakk>inv t1; inv t2\<rbrakk> \<Longrightarrow> real (T_inter t1 t2) \<le> K_T * W_inter t1 t2"
proof (induction t1 t2 rule: inter.induct)
  case (1 t1 t2)
  then show ?case
    using K_T_ge_1
    by (fastforce simp: T_inter.simps[of t1 t2] W_inter.simps[of t1 t2] inv_inter split_inv
                  simp del: T_join2.simps
                  intro!: rule_cost_step_inter rule_cost_step_inter2 T_split_bridge
                  split: tree.splits prod.splits)
                  
qed

lemma KJk_inter_pos: "0 < KJk_inter"
proof -
  have "0 \<le> (2 + K_min) * c\<^sub>u"
    using K_min_nonneg c_u_nonneg by (auto intro: mult_nonneg_nonneg)
  then show ?thesis using c_u_ge_one by linarith
qed

lemma KJc_inter_pos: "0 < KJc_inter"
  using K_min_nonneg c_vals by auto

theorem W_inter_bound:
  assumes "inv t1" "inv t2"
  shows "W_inter t1 t2
       \<le> 1 + K_lin KJk_inter KJc_inter * size_min t1 t2
         + K_log KJk_inter KJc_inter
           * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
  using W_bound_generic'[OF assms W_inter_work_bound[OF assms]
          join_work_inter_le_sum_rank[OF assms]
          KJk_inter_pos KJc_inter_pos] by simp

corollary T_inter_bound:
  assumes "inv t1" "inv t2"
  shows "real (T_inter t1 t2)
       \<le> K_T + (K_T * K_lin KJk_inter KJc_inter) * size_min t1 t2
         + (K_T * K_log KJk_inter KJc_inter)
           * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (T_inter t1 t2) \<le> K_T * W_inter t1 t2"
    using T_inter_bridge assms(1,2) by simp
  also have "\<dots> \<le> K_T * (1 + K_lin KJk_inter KJc_inter * size_min t1 t2 +
     K_log KJk_inter KJc_inter * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1)))"
    using W_inter_bound[OF assms] K_T_ge_1 by auto
  also have "\<dots> = K_T + (K_T * K_lin KJk_inter KJc_inter) * size_min t1 t2 +
    (K_T * K_log KJk_inter KJc_inter)
      * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    by argo
  finally show ?thesis .
qed

lemma W_split_min_nonneg: "t \<noteq> Leaf \<Longrightarrow> 0 \<le> W_split_min t"
  by (induction t rule: W_split_min.induct)
     (auto intro!: add_nonneg_nonneg split: prod.split)

lemma W_join2_nonneg: "0 \<le> W_join2 l r"
  unfolding W_join2_def
  by (auto intro!: add_nonneg_nonneg W_split_min_nonneg split: prod.split)

lemma W_inter_nonneg: "0 \<le> W_inter t1 t2"
proof (induction t1 t2 rule: W_inter.induct)
  case (1 t1 t2)
  then show ?case
    by (auto simp: W_inter.simps[of t1 t2]
             intro!: add_nonneg_nonneg W_split_nonneg W_join2_nonneg
             split: tree.splits prod.splits)
qed


theorem W_inter_bigo:
 "(\<lambda>(t1, t2). W_inter t1 t2) \<in> O[tree_pair_filter](\<lambda>(t1,t2).
   size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "\<And>ta tb. 0 \<le> W_inter ta tb"
    by (rule W_inter_nonneg)
  moreover have "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk> \<Longrightarrow> W_inter ta tb
      \<le> 1 + length (split_parts ta tb) + join_work_inter ta tb + split_work ta tb"
    using W_inter_work_bound by blast
  moreover have "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk>
      \<Longrightarrow> join_work_inter ta tb \<le> (\<Sum>t \<leftarrow> split_parts ta tb. KJk_inter + KJc_inter * rank t)"
    using join_work_inter_le_sum_rank by blast
  ultimately show ?thesis
    using KJk_inter_pos KJc_inter_pos
          W_bound_bigo_generic_ln[where k=KJk_inter and c=KJc_inter] by force
qed

corollary T_inter_bigo:
 "(\<lambda>(t1, t2). real (T_inter t1 t2)) \<in> O[tree_pair_filter](\<lambda>(t1,t2).
   size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "eventually (\<lambda>x. norm ((\<lambda>(t1, t2). real (T_inter t1 t2)) x)
          \<le> K_T * norm ((\<lambda>(t1, t2). W_inter t1 t2) x)) tree_pair_filter"
    unfolding tree_pair_filter_def using eventually_tree_pair_filter
    by (auto simp: W_inter_nonneg elim!: eventually_mono intro!: T_inter_bridge)
  then have "(\<lambda>(t1, t2). real (T_inter t1 t2))
      \<in> O[tree_pair_filter](\<lambda>(t1, t2). W_inter t1 t2)"
    using bigoI by fast
  then show ?thesis
    using W_inter_bigo landau_o.big_trans by blast
qed

section \<open>Difference\<close>

text \<open>
  Difference decomposes @{term t1} instead of @{term t2}. Otherwise the proof proceeds in an identical manner.
\<close>

fun W_diff :: "('a * 'b) tree \<Rightarrow> ('a * 'b) tree \<Rightarrow> real" where
"W_diff t1 t2 =
  (if t1 = Leaf then 1
   else if t2 = Leaf then 1
   else case t2 of Node l2 (a,_) r2 \<Rightarrow>
     (let (l1, _, r1) = split a t1;
          l' = diff l1 l2; r' = diff r1 r2
      in 1
         + W_split t1 a
         + W_join2 l' r'
         + W_diff l1 l2
         + W_diff r1 r2))"

fun join_work_diff :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> real" where
"join_work_diff t1 t2 =
  (if t1 = Leaf then 0 else
   if t2 = Leaf then 0 else
   case t2 of Node l2 (a, _) r2 \<Rightarrow>
   let (l1, _, r1) = split a t1;
       l' = diff l1 l2; r' = diff r1 r2
   in 1 + W_join2 l' r' + join_work_diff l1 l2 + join_work_diff r1 r2)"

declare W_diff.simps[simp del]
declare join_work_diff.simps[simp del]

lemma W_diff_work_bound:
  assumes "inv t1" "inv t2"
  shows "W_diff t1 t2
       \<le> 1 + length (split_parts t2 t1) + join_work_diff t1 t2 + split_work t2 t1"
  using assms
proof (induction t1 t2 rule: W_diff.induct)
  case (1 t1 t2)
  then show ?case
    by (fastforce simp: W_diff.simps[of t1 t2] split_work.simps[of t2 t1]
                        join_work_diff.simps[of t1 t2] split_parts.simps[of t2 t1]
                        inv_diff split_inv
                  split: prod.splits tree.splits
                  dest: split_inv)
qed

subsection \<open>Bounding join-work\<close>

lemma diff_size_bound:
  assumes "inv t1" "inv t2"
  shows "size (diff t1 t2) \<le> size t1"
using assms
proof (induction t1 t2 rule: diff.induct)
  case (1 t1 t2)
  show ?case
  proof (cases "t1 = Leaf \<or> t2 = Leaf")
    case True
    then show ?thesis by (auto simp: diff.simps[of t1 t2])
  next
    case False
    then obtain l2 a b r2 where t2_def: "t2 = Node l2 (a, b) r2"
      by (cases t2) auto
    obtain l1 f r1 where SPL: "split a t1 = (l1, f, r1)"
      by (cases "split a t1") auto
    have inv_l1: "inv l1" and inv_r1: "inv r1"
      using SPL "1.prems"(1) split_inv by metis+
    have inv_l2: "inv l2" and inv_r2: "inv r2"
      using "1.prems"(2) t2_def inv_Node by blast+
    have IHl: "size (diff l1 l2) \<le> size l1"
      using "1.IH"(1) False t2_def SPL inv_l1 inv_l2 by auto
    have IHr: "size (diff r1 r2) \<le> size r1"
      using "1.IH"(2) False t2_def SPL inv_r1 inv_r2 by auto

    have "diff t1 t2 = join2 (diff l1 l2) (diff r1 r2)"
      using False t2_def SPL by (auto simp: diff.simps split: prod.splits tree.splits)
    then have "size (diff t1 t2) = size (diff l1 l2) + size (diff r1 r2)"
      by (simp add: join2_size[OF inv_diff[OF inv_l1 inv_l2] inv_diff[OF inv_r1 inv_r2]])
    also have "\<dots> \<le> size l1 + size r1"
      using IHl IHr by linarith
    also have "\<dots> \<le> size t1"
      using split_size[OF SPL[symmetric] "1.prems"(1)] .
    finally show ?thesis .
  qed
qed

lemma diff_rank_le_log_size:
  assumes "inv t1" "inv t2"
  shows "rank (diff t1 t2) \<le> c\<^sub>u * log 2 (size1 t1)"
proof -
  have "inv (diff t1 t2)" using assms inv_diff by auto
  then have "rank (diff t1 t2) \<le> c\<^sub>u * log 2 (size1 (diff t1 t2))"
    using rank_le_cu_log_size1 by blast
  also have "... \<le> c\<^sub>u * log 2 (size1 t1)"
    using diff_size_bound[OF assms] c_vals by (simp add: size1_size)
  finally show ?thesis .
qed

fun join_work_diff' :: "('a*'b)tree \<Rightarrow> ('a*'b)tree \<Rightarrow> real" where
"join_work_diff' t1 t2 =
  (if t1 = Leaf then 0 else
   if t2 = Leaf then 0 else
   case t2 of Node l2 (a, _) r2 \<Rightarrow>
   let (l1, _, r1) = split a t1;
       l' = diff l1 l2; r' = diff r1 r2
   in 1 + W_join l' a r' + 1 + c\<^sub>u + K_min * rank r'
      + join_work_diff' l1 l2 + join_work_diff' r1 r2)"

declare join_work_diff'.simps[simp del]

lemma join_work_diff_le_diff':
  assumes "inv t1" "inv t2"
  shows "join_work_diff t1 t2 \<le> join_work_diff' t1 t2"
using assms
proof (induction t1 t2 rule: join_work_diff.induct)
  case (1 t1 t2)
  show ?case
  proof (cases "t1 = Leaf \<or> t2 = Leaf")
    case True then show ?thesis
      by (auto simp: join_work_diff.simps join_work_diff'.simps)
  next
    case False
    then obtain l2 a b r2 where t2_def: "t2 = Node l2 (a, b) r2"
      by (cases t2) auto
    obtain l1 f r1 where SPL: "split a t1 = (l1, f, r1)"
      by (cases "split a t1") auto
    have inv_l1: "inv l1" and inv_r1: "inv r1"
      using SPL "1.prems"(1) split_inv by metis+
    have inv_l2: "inv l2" and inv_r2: "inv r2"
      using "1.prems"(2) t2_def inv_Node by blast+
    have inv_dl: "inv (diff l1 l2)" and inv_dr: "inv (diff r1 r2)"
      using inv_diff inv_l1 inv_r1 inv_l2 inv_r2 by auto

    have "join_work_diff l1 l2 \<le> join_work_diff' l1 l2"
      using "1.IH"(1) False t2_def SPL inv_l1 inv_l2 by auto
    moreover have "join_work_diff r1 r2 \<le> join_work_diff' r1 r2"
      using "1.IH"(2) False t2_def SPL inv_r1 inv_r2 by auto
    moreover have "W_join2 (diff l1 l2) (diff r1 r2)
        \<le> W_join (diff l1 l2) a (diff r1 r2) + 1 + c\<^sub>u + K_min * rank (diff r1 r2)"
      using W_join2_bounded[OF inv_dl inv_dr] .
    ultimately show ?thesis
      using False t2_def SPL K_min_def c1_pos c_vals
      by (auto simp: join_work_diff.simps join_work_diff'.simps W_join_def
               split: prod.splits)
  qed
qed

lemma join_work_diff'_as_sum:
  assumes "inv t1" "inv t2"
  shows "join_work_diff' t1 t2
       \<le> (\<Sum>t \<leftarrow> split_parts t2 t1.
            2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t))"
using assms
proof (induction t1 t2 rule: diff.induct)
  case (1 t1 t2)
  show ?case
  proof (cases "t1 = Leaf \<or> t2 = Leaf")
    case True then show ?thesis
      by (auto simp: join_work_diff'.simps split_parts.simps)
  next
    case False
    then obtain l2 a b r2 where t2_def: "t2 = Node l2 (a, b) r2"
      by (cases t2) auto
    obtain l1 f r1 where SPL: "split a t1 = (l1, f, r1)"
      by (cases "split a t1") auto
    have inv_l1: "inv l1" and inv_r1: "inv r1" and inv_l2: "inv l2" and inv_r2: "inv r2"
      using "1.prems" t2_def SPL inv_Node split_inv by metis+
    have inv_dl: "inv (diff l1 l2)" and inv_dr: "inv (diff r1 r2)"
      using inv_diff inv_l1 inv_r1 inv_l2 inv_r2 by auto
    have sz: "size l1 \<le> size t1" "size r1 \<le> size t1"
      using split_size[OF SPL[symmetric] "1.prems"(1)] by linarith+
    have rank_dl: "rank (diff l1 l2) \<le> c\<^sub>u * log 2 (size1 t1)"
      using diff_rank_le_log_size[OF inv_l1 inv_l2] cu_log_size1_mono sz by force
    have rank_dr: "rank (diff r1 r2) \<le> c\<^sub>u * log 2 (size1 t1)"
      using diff_rank_le_log_size[OF inv_r1 inv_r2] cu_log_size1_mono sz by force

    have "W_join (diff l1 l2) a (diff r1 r2) \<le> 2 * c\<^sub>u * log 2 (size1 t1)"
      using rank_dl rank_dr W_join_def rank_pos'[OF inv_dl] rank_pos'[OF inv_dr]
      by (simp add: abs_le_iff)
    then have "1 + W_join (diff l1 l2) a (diff r1 r2) + 1 + c\<^sub>u + K_min * rank (diff r1 r2)
                  \<le> 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t1)"
      using mult_left_mono[OF rank_dr K_min_nonneg] by (simp add: algebra_simps)
    moreover have "split_parts t2 t1 = t1 # (split_parts l2 l1 @ split_parts r2 r1)"
      using False t2_def SPL by (simp add: split_parts.simps)
    moreover have "join_work_diff' t1 t2
        = 1 + W_join (diff l1 l2) a (diff r1 r2) + 1 + c\<^sub>u + K_min * rank (diff r1 r2)
          + join_work_diff' l1 l2 + join_work_diff' r1 r2"
      using False t2_def SPL
      by (auto simp: join_work_diff'.simps split: prod.splits)
    moreover have "join_work_diff' l1 l2
             \<le> (\<Sum>t \<leftarrow> split_parts l2 l1. 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t))"
     and "join_work_diff' r1 r2
             \<le> (\<Sum>t \<leftarrow> split_parts r2 r1. 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t))"
      using "1.IH" False t2_def SPL inv_l1 inv_r1 inv_l2 inv_r2 by auto
    ultimately show ?thesis
      by simp
  qed
qed

abbreviation "KJk_diff \<equiv> 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u"
abbreviation "KJc_diff \<equiv> (2 + K_min) * c\<^sub>u / c\<^sub>l"

lemma join_work_diff_le_sum_rank:
  assumes "inv t1" "inv t2"
  shows "join_work_diff t1 t2
       \<le> (\<Sum>t \<leftarrow> split_parts t2 t1. KJk_diff + KJc_diff * rank t)"
proof -
  have pw: "2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t)
          \<le> KJk_diff + KJc_diff * rank t"
    if "t \<in> set (split_parts t2 t1)" for t
  proof -
    have inv_t: "inv t" using split_parts_inv[OF assms(1)] that by simp
    have "(2 + K_min) * (c\<^sub>u * log 2 (size1 t)) \<le> (2 + K_min) * ((c\<^sub>u / c\<^sub>l) * rank t + c\<^sub>u)"
      using log_size1_le_rank_ratio[OF inv_t] K_min_nonneg by (auto intro: mult_left_mono)
    then show ?thesis by argo
  qed
  have "join_work_diff t1 t2 \<le> join_work_diff' t1 t2"
    using join_work_diff_le_diff'[OF assms(1,2)] .
  also have "... \<le> (\<Sum>t \<leftarrow> split_parts t2 t1. 2 + c\<^sub>u + (2 + K_min) * c\<^sub>u * log 2 (size1 t))"
    using join_work_diff'_as_sum[OF assms(1,2)] .
  also have "... \<le> (\<Sum>t \<leftarrow> split_parts t2 t1. KJk_diff + KJc_diff * rank t)"
    using pw by (intro sum_list_mono) auto
  finally show ?thesis .
qed

subsection \<open>Final bound\<close>

time_fun diff equations diff.simps
declare T_diff.simps[simp del]

lemma T_diff_bridge:
  "\<lbrakk>inv t1; inv t2\<rbrakk> \<Longrightarrow> real (T_diff t1 t2) \<le> K_T * W_diff t1 t2"
proof (induction t1 t2 rule: diff.induct)
  case (1 t1 t2)
  then show ?case
    using K_T_ge_1
    by (fastforce simp: T_diff.simps[of t1 t2] W_diff.simps[of t1 t2] inv_diff split_inv
                  simp del: T_join2.simps
                  intro!: rule_cost_step_inter2 T_split_bridge
                  split: tree.splits prod.splits)
                  
qed

lemma KJk_diff_pos: "0 < KJk_diff"
  using KJk_inter_pos by fastforce

lemma KJc_diff_pos: "0 < KJc_diff"
  using KJc_inter_pos by fastforce

theorem W_diff_bound:
  assumes "inv t1" "inv t2"
  shows "W_diff t1 t2
       \<le> 1 + K_lin KJk_diff KJc_diff * size_min t1 t2
         + K_log KJk_diff KJc_diff
           * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
  using W_bound_generic'[OF assms(2,1)
          W_diff_work_bound[OF assms]
          join_work_diff_le_sum_rank[OF assms]
          KJk_diff_pos KJc_diff_pos]
  by (simp add: min.commute max.commute)

corollary T_diff_bound:
  assumes "inv t1" "inv t2"
  shows "real (T_diff t1 t2)
       \<le> K_T + (K_T * K_lin KJk_diff KJc_diff) * size_min t1 t2
         + (K_T * K_log KJk_diff KJc_diff)
           * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "real (T_diff t1 t2) \<le> K_T * W_diff t1 t2"
    using T_diff_bridge assms(1,2) by simp
  also have "\<dots> \<le> K_T * (1 + K_lin KJk_diff KJc_diff * size_min t1 t2 +
     K_log KJk_diff KJc_diff * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1)))"
    using W_diff_bound[OF assms] K_T_ge_1 by auto
  also have "\<dots> = K_T + (K_T * K_lin KJk_diff KJc_diff) * size_min t1 t2 +
    (K_T * K_log KJk_diff KJc_diff)
      * (size_min t1 t2 * log 2 (size_max t1 t2 / size_min t1 t2 + 1))"
    by argo
  finally show ?thesis .
qed

lemma W_diff_nonneg: "0 \<le> W_diff t1 t2"
proof (induction t1 t2 rule: W_diff.induct)
  case (1 t1 t2)
  then show ?case
    by (auto simp: W_diff.simps[of t1 t2]
             intro!: add_nonneg_nonneg W_split_nonneg W_join2_nonneg
             split: tree.splits prod.splits)
qed

text \<open>
  As both the product filter and the bounding
  function are symmetric, the result is transported along when swapping the terms.\<close>

lemma filterlim_swap_tree_pair:
  "filterlim prod.swap tree_pair_filter tree_pair_filter"
proof -
  have "eventually (\<lambda>x. P (prod.swap x)) tree_pair_filter"
    if "eventually P tree_pair_filter"
    for P :: "(('a \<times> 'b) tree \<times> ('a \<times> 'b) tree) \<Rightarrow> bool"
  proof -
    from that obtain Pf Pg where "eventually Pf tree_filter" "eventually Pg tree_filter"
      "\<And>x y. Pf x \<Longrightarrow> Pg y \<Longrightarrow> P (x, y)"
      unfolding tree_pair_filter_def eventually_prod_filter by blast
    \<comment> \<open>The witnesses are handed back in swapped order\<close>
    then have "eventually Pg tree_filter \<and> eventually Pf tree_filter
             \<and> (\<forall>x y. Pg x \<longrightarrow> Pf y \<longrightarrow> P (prod.swap (x, y)))"
      by simp
    then show ?thesis
      unfolding tree_pair_filter_def eventually_prod_filter by blast
  qed
  then show ?thesis
    unfolding filterlim_iff by blast
qed

theorem W_diff_bigo:
 "(\<lambda>(t1, t2). W_diff t1 t2) \<in> O[tree_pair_filter](\<lambda>(t1,t2).
   size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "(\<lambda>(ta, tb). W_diff tb ta) \<in> O[tree_pair_filter](\<lambda>(ta, tb).
          size_min ta tb * ln (size_max ta tb / size_min ta tb + 1))"
  proof -
    have "\<And>ta tb. 0 \<le> W_diff tb ta"
      by (rule W_diff_nonneg)
    moreover have "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk> \<Longrightarrow> W_diff tb ta
        \<le> 1 + length (split_parts ta tb) + join_work_diff tb ta + split_work ta tb"
      using W_diff_work_bound by blast
    moreover have "\<And>ta tb. \<lbrakk>inv ta; inv tb\<rbrakk>
        \<Longrightarrow> join_work_diff tb ta \<le> (\<Sum>t \<leftarrow> split_parts ta tb. KJk_diff + KJc_diff * rank t)"
      using join_work_diff_le_sum_rank by blast
    ultimately show ?thesis
      using KJk_diff_pos KJc_diff_pos
            W_bound_bigo_generic_ln[where k=KJk_diff and c=KJc_diff] by force
  qed
  then have "(\<lambda>x. (\<lambda>(ta, tb). W_diff tb ta) (prod.swap x))
      \<in> O[tree_pair_filter](\<lambda>x. (\<lambda>(ta, tb).
          size_min ta tb * ln (size_max ta tb / size_min ta tb + 1)) (prod.swap x))"
    using landau_o.big.compose filterlim_swap_tree_pair by blast
  then show ?thesis
    by (simp add: min.commute max.commute)
qed

corollary T_diff_bigo:
 "(\<lambda>(t1, t2). real (T_diff t1 t2)) \<in> O[tree_pair_filter](\<lambda>(t1,t2).
   size_min t1 t2 * ln (size_max t1 t2 / size_min t1 t2 + 1))"
proof -
  have "eventually (\<lambda>x. norm ((\<lambda>(t1, t2). real (T_diff t1 t2)) x)
          \<le> K_T * norm ((\<lambda>(t1, t2). W_diff t1 t2) x)) tree_pair_filter"
    unfolding tree_pair_filter_def using eventually_tree_pair_filter
    by (auto simp: W_diff_nonneg elim!: eventually_mono intro!: T_diff_bridge)
  then have "(\<lambda>(t1, t2). real (T_diff t1 t2))
      \<in> O[tree_pair_filter](\<lambda>(t1, t2). W_diff t1 t2)"
    using bigoI by fast
  then show ?thesis
    using W_diff_bigo landau_o.big_trans by blast
qed

end

end