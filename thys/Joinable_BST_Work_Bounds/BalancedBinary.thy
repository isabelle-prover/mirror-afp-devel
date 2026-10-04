section \<open>Balanced Binary Trees\<close>
theory BalancedBinary
imports
  "HOL-Library.Tree"
  Complex_Main
begin

text \<open>
  @{text BalancedShape} captures the \<^emph>\<open>shape\<close> of a balancing scheme i.e. a rank function
  together with the constants @{text "c\<^sub>l"} and @{text "c\<^sub>u"}. The @{text balanced} predicate is
  defined relative to these, the locale then captures the emergent properties of the scheme
  as defined by \<^cite>\<open>blelloch2022joinable\<close>.
  Here, \<open>c\<^sub>l > 0\<close> is demanded explicitly. With \<open>c\<^sub>l = 0\<close> the rank would
  never have to shrink towards the leaves, and the  \<^cite>\<open>blelloch2022joinable\<close> itself divides 
  by \<open>c\<^sub>l\<close> in its Property 7.
  The actual guarantee that a scheme keeps its trees balanced is
  added by the @{text BalancedTree} locale further below, which connects an invariant to
  @{text balanced}.
\<close>
locale BalancedShape =
fixes rank :: "('a * 'b) tree \<Rightarrow> real"
fixes c\<^sub>l c\<^sub>u :: real
assumes c_vals:"c\<^sub>l > 0 \<and> c\<^sub>l \<le> 1 \<and> c\<^sub>u \<ge> 1"
assumes rule_empty: "rank Leaf = 0"
begin

lemma c_l_pos: "0 < c\<^sub>l"
  using c_vals by blast

lemma c_l_le_one: "c\<^sub>l \<le> 1"
  using c_vals by blast

lemma c_u_ge_one: "1 \<le> c\<^sub>u"
  using c_vals by blast

corollary c_l_nonneg: "0 \<le> c\<^sub>l"
  using c_l_pos by linarith

corollary c_u_pos: "0 < c\<^sub>u"
  using c_u_ge_one by linarith

corollary c_u_nonneg: "0 \<le> c\<^sub>u"
  using c_u_pos by linarith

subsection \<open>Balance Predicate\<close>
text "The central balance predicate is defined as a recursive function
over the structure of the tree. For each node it ensures that left and right subtrees
of any given parent node 
differ only by the balancing constants @{term c\<^sub>l} and @{term c\<^sub>u} in terms of @{term rank}
relative to it."
fun balanced :: "('a * 'b) tree \<Rightarrow> bool" where
"balanced Leaf = True" |
"balanced (Node l a r) = 
  (max (rank l) (rank r) + c\<^sub>l \<le> rank (Node l a r) \<and> 
   min (rank l) (rank r) + c\<^sub>u \<ge> rank (Node l a r) \<and> 
   balanced l \<and> balanced r)"

text \<open>It follows immediately that the ranks of the left/right subtrees of a parent node can 
differ at most by a constant, namely @{term  "c\<^sub>\<delta> = c\<^sub>u - c\<^sub>l"} \<^cite>\<open>\<open>Property 4\<close> in blelloch2022joinable\<close>.\<close>

definition "c\<^sub>\<delta> = c\<^sub>u - c\<^sub>l"

(* Blelloch et al. property 4 *)
lemma dmax:"balanced (Node l a r) \<Longrightarrow> \<bar>rank l - rank r\<bar> \<le> c\<^sub>\<delta>"
  using c\<^sub>\<delta>_def by force

(* useful dest rules *)
lemma balanced_children_explD:
  assumes "balanced (Node l a r)"
  shows "rank l \<le> rank (Node l a r) - c\<^sub>l"
    and "rank r \<le> rank (Node l a r) - c\<^sub>l"
    and "rank (Node l a r) - c\<^sub>u \<le> rank l"
    and "rank (Node l a r) - c\<^sub>u \<le> rank r"
using assms by fastforce+

subsection \<open>Relationship between tree rank and height\<close>

text \<open>Rank is bounded below by $c_l \cdot \mathit{height~t}$ which is the 
  direction of \<^cite>\<open>\<open>Property 1\<close> in blelloch2022joinable\<close> needed for the 
  analysis.\<close>

lemma rank_lower_height:"balanced t \<Longrightarrow> c\<^sub>l * height t \<le> rank t"
proof(induction t)
  case Leaf
  then show ?case
    by (simp add: rule_empty)
next
  case (Node l a r)
  then have "c\<^sub>l * height l \<le> rank l"
    by simp
  moreover have "c\<^sub>l * height r \<le> rank r"
    using Node by simp
  ultimately have "c\<^sub>l * max (height l) (height r) \<le> max (rank l) (rank r)"
    by (simp add: mult_left_mono c_vals max_def)
  then have "c\<^sub>l * max (height l) (height r) + c\<^sub>l \<le> max (rank l) (rank r) + c\<^sub>l"
    by linarith
  also have "c\<^sub>l * max (height l) (height r) + c\<^sub>l = c\<^sub>l * (max (height l) (height r) + 1)"
    by (simp add: distrib_left)
  finally have "c\<^sub>l * (max (height l) (height r) + 1) \<le> max (rank l) (rank r) + c\<^sub>l"
    by linarith
  moreover have "c\<^sub>l * height (Node l a r) \<le> c\<^sub>l * (max (height l) (height r) + 1)"
    using c_vals by simp
  ultimately show ?case
    using Node by auto
qed

corollary rank_lower_height_inverse:"balanced t \<Longrightarrow> height t \<le> rank t / c\<^sub>l"
  by (metis c_vals rank_lower_height pos_le_divide_eq mult_of_nat_commute)


text \<open>Which also implies @{term rank} is never negative.\<close>
corollary rank_pos:"balanced t \<Longrightarrow> rank t \<ge> 0"
  by (metis rank_lower_height c_vals of_nat_0_le_iff mult_nonneg_nonneg order_trans order_less_le)

text \<open>The upper bound for @{term rank} holds as well and is added for sake of completeness.\<close>

lemma rank_upper_height:"balanced t \<Longrightarrow> rank t \<le> c\<^sub>u * height t"
proof(induction t)
  case Leaf
  then show ?case 
    by (simp add: rule_empty)
next
  case (Node l a r)
  then have "rank l \<le> c\<^sub>u * height l"
    by simp
  moreover have "rank r \<le> c\<^sub>u * height r"
    using Node by simp
  ultimately have "max (rank l) (rank r) \<le> c\<^sub>u * max (height l) (height r)"
    using c_vals by (auto simp: max_def intro: mult_left_mono order_trans)
  then have "max (rank l) (rank r) + c\<^sub>u \<le> c\<^sub>u * max (height l) (height r) + c\<^sub>u"
    using c_vals by argo
  also have "... \<le> c\<^sub>u * (max (height l) (height r) + 1)"
    using c_vals by (simp add: distrib_left)
  also have "... \<le> c\<^sub>u * height (Node l a r)"
    using c_vals by auto
  finally show ?case 
    using Node by auto
qed

subsection \<open>Relationship between tree rank and size\<close>

text \<open>Size grows exponentially in rank \<^cite>\<open>\<open>Property 2\<close> in blelloch2022joinable\<close>.\<close>
lemma pow_shift:
  assumes "c\<^sub>u \<noteq> 0"
  shows   "2 * 2 powr ((r - c\<^sub>u) / c\<^sub>u) = 2 powr (r / c\<^sub>u)"
proof -
  have "2 * 2 powr ((r - c\<^sub>u) / c\<^sub>u) = (2 powr 1) * 2 powr ((r - c\<^sub>u) / c\<^sub>u)"
    by simp
  also have "... = 2 powr (1 + (r - c\<^sub>u) / c\<^sub>u)"
    by (simp add: powr_add)
  also have "1 + (r - c\<^sub>u) / c\<^sub>u = r / c\<^sub>u"
    using assms by (simp add: field_simps)
  finally show ?thesis
    by simp
qed

lemma size1_ge_powr_rank:
  "balanced t \<Longrightarrow> size1 t \<ge> 2 powr (rank t / c\<^sub>u)"
proof (induction t)
  case Leaf
  show ?case
    by (simp add: rule_empty)
next
  case (Node l a r)
  then have 
    IHl: "size1 l \<ge> 2 powr (rank l / c\<^sub>u)"
  and 
    IHr: "size1 r \<ge> 2 powr (rank r / c\<^sub>u)"
    by auto

  have lower_l:
    "size1 l \<ge> 2 powr ((rank (Node l a r) - c\<^sub>u) / c\<^sub>u)"
  proof - 
    have "rank (Node l a r) - c\<^sub>u \<le> rank l"
      using Node.prems by auto
    then have "2 powr ((rank (Node l a r) - c\<^sub>u) / c\<^sub>u) \<le> 2 powr (rank l / c\<^sub>u)"
      using c_vals divide_right_mono by fastforce
    then show ?thesis 
       using IHl by argo
  qed

  have lower_r:
    "size1 r \<ge> 2 powr ((rank (Node l a r) - c\<^sub>u) / c\<^sub>u)"
  proof -
    have "rank (Node l a r) - c\<^sub>u \<le> rank r"
      using Node.prems by auto
    then have "2 powr ((rank (Node l a r) - c\<^sub>u) / c\<^sub>u) \<le> 2 powr (rank r / c\<^sub>u)"
      using c_vals divide_right_mono by fastforce
    then show ?thesis 
       using IHr by argo
  qed

  have "real (size1 (Node l a r)) = real (size1 l) + real (size1 r)"
    by simp
  also have "... \<ge> 2 * (2 powr ((rank (Node l a r) - c\<^sub>u) / c\<^sub>u))"
    using lower_l lower_r by linarith
  finally show ?case 
    using pow_shift by fastforce
qed

corollary rank_le_cu_log_size1:
  assumes "balanced t"
  shows "rank t \<le> c\<^sub>u * log 2 (size1 t)"
proof -
  have "size1 t \<ge> 2 powr (rank t / c\<^sub>u)"
    using size1_ge_powr_rank[OF assms] .
  then have "log 2 (size1 t) \<ge> log 2 (2 powr (rank t / c\<^sub>u))"
    using le_log_iff by auto
  then show ?thesis
    using c_vals by (simp add: field_simps)
qed

subsection \<open>Layers and rank-roots\<close>

text \<open>Layer $i$ of a tree collects all nodes whose rank falls into $[i, i+1)$ i.e. 
its rank lies in the unit band $[i, i+1)$ \<^cite>\<open>\<open>Definition 3\<close> in blelloch2022joinable\<close>.
In essence, \<open>layer\<close> discretizes the real valued \<open>rank\<close> into finite layers, enabling
the summation arguments used in the asymptotic analysis.\<close>

abbreviation in_band :: "nat \<Rightarrow> real \<Rightarrow> bool" where
  "in_band i x \<equiv> real i \<le> x \<and> x < real i + 1"

fun layer :: "('a * 'b) tree \<Rightarrow> nat \<Rightarrow> (('a * 'b) tree) list" where
"layer Leaf _ = []" |
"layer (Node l x r) i =
     ((if in_band i (rank (Node l x r)) then [(Node l x r)] else []) @
   layer l i
   @ layer r i)"

lemma layer_empty_if_rank_lt:
  assumes Bt: "balanced t"
  assumes lt: "rank t < i"
  shows "layer t i = []"
using Bt lt c_vals by(induction t) auto

text \<open>Where @{term layer} recurses the entire tree, @{term rank_roots} stops at the first
node whose rank falls into layer $i$, which is called the \<open>rank root\<close> of that layer
\<^cite>\<open>\<open>Definition 4\<close> in blelloch2022joinable\<close>.
A layer then decomposes as the concatenation of sub-layers rooted at these nodes
(cf. \<^cite>\<open>\<open>Definition 5\<close> in blelloch2022joinable\<close>).\<close>

fun rank_roots :: "('a * 'b) tree \<Rightarrow> nat \<Rightarrow> (('a * 'b) tree) list" where
"rank_roots Leaf _ = []" |
"rank_roots (Node l x r) i =
     (if in_band i (rank (Node l x r)) then [(Node l x r)] else
   rank_roots l i
   @ rank_roots r i)"

lemma rank_rank_roots: "r \<in> set(rank_roots t i) \<Longrightarrow> in_band i (rank r)"
  by(induction t) (auto split: if_splits)

text \<open>Balance is inherited.\<close>

lemma balanced_rank_roots: "\<lbrakk>balanced t; r \<in> set(rank_roots t i)\<rbrakk> \<Longrightarrow> balanced r"
  by(induction t) (auto split: if_splits)

lemma layer_eq_concat_rank_roots:
  "layer T i = concat (map (\<lambda>r. layer r i) (rank_roots T i))"
proof (induction T)
  case Leaf
  then show ?case by simp
next
  case (Node l x r)
  then show ?case
    by (cases "in_band i (rank (Node l x r))") auto
qed

subsection \<open>Size bound on layer and root nodes\<close>

text \<open>
  The work bounds for union, intersection and difference will ultimately be obtained by
  decomposing the total work into layers and bounding each layer's contribution
  separately. Two main ingredients make this work:

  \<^item> \<open>Across\<close> layers, the number of rank roots decays geometrically i.e. layer
    @{term i} has at most $\mathit{size1~t}/2^{i/c_u}$ rank roots. This sharpens
    \<^cite>\<open>\<open>Lemma 1\<close> in blelloch2022joinable\<close>, where the exponent is $i/(1 + c_u)$.

  \<^item> \<open>Within\<close> a layer, the number of nodes belonging to each rank root 
    is bounded by the constant $C = 2^{\lceil 1/c_l \rceil} - 1$. This absorbs intra-layer
    overhead into a constant factor  \<^cite>\<open>\<open>Property 7\<close> in blelloch2022joinable\<close>\<close>
text\<open>
  Both facts are established in this subsection and are consumed separately by the
  main theory, as the decay bound on rank roots and the constant bound per rank root.
  The combined geometric layer bound closing this subsection is not needed
  downstream, but is still shown to make it clear that it is an emergent property
  of balanced trees.
  First, each rank root in layer $i$ has rank at least $i$, so the exponential
  size lower bound applies.\<close>

corollary rank_roots_size_lower:
  assumes "balanced t"
  shows "r \<in> set (rank_roots t i) \<Longrightarrow> size1 r \<ge> 2 powr (i / c\<^sub>u)"
proof -
  fix r
  assume r_in: "r \<in> set (rank_roots t i)"

  have "i \<le> rank r"
    using rank_rank_roots[OF r_in] by auto
  then have "(2::real) powr (real i / c\<^sub>u) \<le> (2::real) powr (rank r / c\<^sub>u)"
    using c_vals by(simp add: divide_simps)
  then show "size1 r \<ge> 2 powr (real i / c\<^sub>u)"
    using size1_ge_powr_rank[OF balanced_rank_roots[OF assms r_in]] by linarith
qed

text \<open>Further, the combined size of all rank roots in a layer never exceeds the size of the whole tree.\<close>

lemma rank_roots_size_sum:
"sum_list (map size1 (rank_roots t i)) \<le> size1 t"
  by(induction t) auto

text \<open>Combining both gives the desired bound on the number of rank roots.\<close>
lemma rank_roots_count_powr:
  assumes "balanced t"
  shows "length (rank_roots t i) * 2 powr (i / c\<^sub>u) \<le> size1 t"
proof -
  have "length (rank_roots t i) * 2 powr (i / c\<^sub>u)
      = sum_list (map (\<lambda>_. 2 powr (i / c\<^sub>u)) (rank_roots t i))"
    by (simp add: sum_list_triv)
  also have "... \<le> sum_list (map (real o size1) (rank_roots t i))"
    using rank_roots_size_lower[OF assms] by (simp add: sum_list_mono)
  also have "... \<le> real (size1 t)"
    using rank_roots_size_sum[of t i]
    by (metis list.map_comp of_nat_le_iff sum_list_of_nat)
  finally show ?thesis .
qed

text \<open>Restated via division.\<close>

corollary rank_roots_count_powr_le:
  assumes "balanced t"
  shows "length (rank_roots t i)
        \<le> size1 t / (2 powr (i / c\<^sub>u))"
proof -
  have "length (rank_roots t i) * 2 powr (i / c\<^sub>u) \<le> size1 t"
    using rank_roots_count_powr[OF assms] .
  moreover have "0 < 2 powr (real i / c\<^sub>u)"
    by simp
  ultimately show ?thesis
    by (simp add: pos_le_divide_eq)
qed

text \<open>
  A balanced tree whose rank overshoots layer $i$ by at most $d$ has at most
  $2^{\left\lceil \frac{d}{c_l} \right\rceil} - 1$ nodes in that layer.
  The budget $d$ shrinks by @{term c\<^sub>l} at every level, giving the exponential bound.
  The parameter $d$ is generalized beyond the natural choice $d = 1$
  because the induction step requires applying the lemma to children 
  with a reduced budget.\<close>

lemma layer_len_budget:
  fixes d :: real
  assumes "balanced t"
  assumes "rank t < real i + d"
  assumes "0 \<le> d"
  shows "length (layer t i) \<le> 2^(nat (ceiling (d / c\<^sub>l))) - 1"
using assms
proof (induction t arbitrary: d)
  case Leaf
  then show ?case
    by simp
next
  case (Node l x r)

  let ?t = "Node l x r"
  let ?m = "nat (ceiling (d / c\<^sub>l))"

  have Bl: "balanced l" and Br: "balanced r"
    using Node by auto

  show ?case
  proof (cases "?m = 0")
    case True
    then show ?thesis
      using layer_empty_if_rank_lt[OF Node.prems(1)] Node.prems(2,3) c_l_pos 
      by (auto simp add: divide_le_0_iff)
  next
    case False
    have mpos: "?m \<ge> 1"
      using False by linarith
    have child_cut_l: "rank l < real i + (d - c\<^sub>l)"
      using Node.prems(1,2) by force
    have child_cut_r: "rank r < real i + (d - c\<^sub>l)"
      using Node.prems(1,2) by force
    have ceil_step:
      "nat (ceiling ((d - c\<^sub>l) / c\<^sub>l)) \<le> ?m - 1"
      using c_vals by (auto simp: diff_divide_distrib)

    have "length (layer ?t i) \<le> 1 + length (layer l i) + length (layer r i)"
      by simp
    also have "... \<le> 1 + (2^(?m - 1) - 1) + (2^(?m - 1) - 1)"
    proof - 
      have "length (layer l i) \<le> 2^(?m - 1) - 1"
      proof -
        have "length (layer l i) \<le> 2^(nat (ceiling ((d - c\<^sub>l) / c\<^sub>l))) - 1"
          using Bl Node.IH(1) child_cut_l layer_empty_if_rank_lt by force
        also have "... \<le> 2^(?m - 1) - 1"
          using ceil_step by (metis diff_le_mono le_add_same_cancel1 one_add_one power_increasing zero_le_one)
        finally show ?thesis .
      qed

      moreover have "length (layer r i) \<le> 2^(?m - 1) - 1"
      proof -
        have "length (layer r i) \<le> 2^(nat (ceiling ((d - c\<^sub>l) / c\<^sub>l))) - 1"
          using Br Node.IH(2) child_cut_r layer_empty_if_rank_lt by force
        also have "... \<le> 2^(?m - 1) - 1"
          using ceil_step by (metis diff_le_mono le_add_same_cancel1 one_add_one power_increasing zero_le_one)
        finally show ?thesis .
      qed
      
      ultimately show ?thesis by linarith
    qed
    also have "... = 2 * 2^(?m - 1) - 1"
        using one_le_power by fastforce
    also have "... = 2^?m - 1"
      using mpos False by (metis power_eq_if)
    finally show ?thesis .
  qed
qed

text \<open>Instantiating with $d=1$ begets the actual constant.\<close>
definition C :: nat where "C = 2^(nat (ceiling (1 / c\<^sub>l))) - 1"

lemma C_pos: "real C \<ge> 0"
  by force

corollary layer_bound_const:
  assumes "balanced t" "rank t < real i + 1"
  shows "length (layer t i) \<le> C"
  using layer_len_budget[OF assms(1) assms(2)] C_def by simp


text \<open>
  Thus the total number of nodes in layer $i$ is at most @{term C} times the
  number of rank roots.\<close>

lemma length_concat_map_le_sum:
  "length (concat (map f xs)) \<le> sum_list (map (\<lambda>x. length (f x)) xs)"
  by (induction xs) auto

lemma layer_bound_via_rank_roots:
  assumes BT: "balanced T"
  shows "length (layer T i)
       \<le> C * length (rank_roots T i)"
proof -
  have decomp: "layer T i = concat (map (\<lambda>r. layer r i) (rank_roots T i))"
    using layer_eq_concat_rank_roots .
  then have "length (layer T i)
      = length (concat (map (\<lambda>r. layer r i) (rank_roots T i)))"
    by simp
  also have "... \<le> sum_list (map (\<lambda>r. length (layer r i)) (rank_roots T i))"
    using length_concat_map_le_sum by metis
  also have "... \<le> sum_list (map (\<lambda>_. C) (rank_roots T i))"
    using balanced_rank_roots[OF BT] rank_rank_roots layer_bound_const C_def by (meson sum_list_mono)
  also have "sum_list (map (\<lambda>_. C) (rank_roots T i)) = C * (length (rank_roots T i))"
    by (simp add: sum_list_triv)
  finally show ?thesis 
   by simp
qed


text \<open>Together, this yields the fully combined geometric layer bound.\<close> 

corollary layer_bound_geometric:
  assumes "balanced t"
  shows "(length (layer t i)) \<le> C * (size1 t / (2 powr (i / c\<^sub>u)))"
proof -
  have
    "length (layer t i) \<le> C * length (rank_roots t i)"
    using layer_bound_via_rank_roots[OF assms] .
  also have
    " ... \<le> C * (size1 t / (2 powr (i / c\<^sub>u)))"
    using rank_roots_count_powr_le[OF assms] by (metis mult_left_mono of_nat_0_le_iff of_nat_mult)
  finally show ?thesis 
    by simp
qed

end

subsection \<open>Balanced schemes\<close>

text \<open>
  A @{text BalancedTree} is a @{text BalancedShape} together with an invariant
  that implies balance. This records the balancing rule of 
  \<^cite>\<open>blelloch2022joinable\<close>.
\<close>
locale BalancedTree = BalancedShape rank c\<^sub>l c\<^sub>u
  for rank :: "('a \<times> 'b) tree \<Rightarrow> real"
  and c\<^sub>l c\<^sub>u :: real
  +
  fixes inv :: "('a \<times> 'b) tree \<Rightarrow> bool"
  assumes rule_bal: "inv t \<Longrightarrow> balanced t"
begin

declare rule_bal[intro]

corollary rank_pos'[simp]: "inv t \<Longrightarrow> 0 \<le> rank t"
  using rank_pos rule_bal by blast

corollary dmax': "inv (Node l a r) \<Longrightarrow> \<bar>rank l - rank r\<bar> \<le> c\<^sub>\<delta>"
  using dmax rule_bal by blast

corollary rank_le_cu_log_size1': "inv t \<Longrightarrow> rank t \<le> c\<^sub>u * log 2 (size1 t)"
  using rank_le_cu_log_size1 rule_bal by blast

corollary rank_lower_height_inverse': "inv t \<Longrightarrow> height t \<le> rank t / c\<^sub>l"
  using rank_lower_height_inverse rule_bal by blast

corollary inv_children_explD:
  assumes "inv (Node l a r)"
  shows "rank l \<le> rank (Node l a r) - c\<^sub>l"
    and "rank r \<le> rank (Node l a r) - c\<^sub>l"
    and "rank (Node l a r) - c\<^sub>u \<le> rank l"
    and "rank (Node l a r) - c\<^sub>u \<le> rank r"
  using balanced_children_explD[OF rule_bal[OF assms]] by blast+
end

end