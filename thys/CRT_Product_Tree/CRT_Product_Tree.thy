(*
  File:    CRT_Product_Tree.thy
  Author:  Manuel Eberl, University of Innsbruck
*)
section \<open>Product and remainder trees\<close>
theory CRT_Product_Tree
  imports "HOL-Number_Theory.Number_Theory"
begin

(*<*)
subsection \<open>Auxiliary material\<close>

(* TODO: Move? *)
lemma mset_diff_irrelevant [simp]: "x \<notin># Y \<Longrightarrow> x \<in># X - Y \<longleftrightarrow> x \<in># X"
  by (simp add: in_diff_count not_in_iff)

context semiring_gcd
begin

lemma prod_mset_coprime_left:
  "coprime (prod_mset X) a" if "\<And>x. x \<in># X \<Longrightarrow> coprime x a"
  using that by (induct X) auto

lemma prod_mset_coprime_right:
  "coprime a (prod_mset X)" if "\<And>x. x \<in># X \<Longrightarrow> coprime a x"
  using coprime_commute prod_mset_coprime_left that by presburger

end

lemma modular_inverse_cong:
  fixes x x' m :: "'a :: {unique_euclidean_ring, euclidean_ring_gcd}"
  assumes "[x = x'] (mod m)" "coprime m x"
  shows   "modular_inverse m x = modular_inverse m x'"
proof -
  have x': "coprime m x'"
    using assms(1,2) cong_imp_coprime coprime_commute by blast
  have "[modular_inverse m x * x = 1] (mod m)"
    by (rule cong_modular_inverse2) (use assms in \<open>auto simp: coprime_commute\<close>)
  also have "[1 = modular_inverse m x' * x'] (mod m)"
    by (rule cong_sym, rule cong_modular_inverse2) (use x' in \<open>auto simp: coprime_commute\<close>)
  also have "[modular_inverse m x' * x' = modular_inverse m x' * x] (mod m)"
    by (intro cong_mult cong_refl cong_sym[OF assms(1)])
  finally have "[modular_inverse m x = modular_inverse m x'] (mod m)"
    using \<open>coprime m x\<close> by (simp add: cong_mult_rcancel coprime_commute)
  thus ?thesis
    by (auto simp: cong_def modular_inverse_def)
qed

lemma cong_sum_list:
  assumes "list_all2 (\<lambda>x y. [x = y] (mod m)) xs ys"
  shows   "[sum_list xs = sum_list ys] (mod m)"
  using assms by induction (auto intro!: cong_add)

lemma cong_sum_list':
  assumes "list_all2 (\<lambda>x y. [f x = g y] (mod m)) xs ys"
  shows   "[sum_list (map f xs) = sum_list (map g ys)] (mod m)"
  using assms by induction (auto intro!: cong_add)

lemma sorted_wrt_symD:
  assumes "sorted_wrt P xs" "P x y \<longleftrightarrow> P y x"
  assumes "x \<in> set xs" "y \<in> set xs" "x \<noteq> y"
  shows   "P x y"
  using assms by (induction xs) auto
(* END TODO *)
(*>*)


subsection \<open>Prerequisite: A ``pairwise'' operator for multisets\<close>

(* TODO: Move? *)

text \<open>
  The following is a multiset analogue of the \<^const>\<open>pairwise\<close> operator for sets.
\<close>
definition pairwise_mset :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "pairwise_mset P X \<longleftrightarrow> (\<forall>x\<in>#X. \<forall>y\<in>#X-{#x#}. P x y)"

lemma pairwise_msetI: "(\<And>x y. x \<in># X \<Longrightarrow> y \<in># X - {#x#} \<Longrightarrow> P x y) \<Longrightarrow> pairwise_mset P X"
  by (auto simp: pairwise_mset_def)

lemma pairwise_msetI': "(\<And>x y. {#x, y#} \<subseteq># X \<Longrightarrow> P x y) \<Longrightarrow> pairwise_mset P X"
  by (rule pairwise_msetI) (auto simp: insert_subset_eq_iff)

lemma pairwise_msetD: "pairwise_mset P X \<Longrightarrow> x \<in># X \<Longrightarrow> y \<in># X - {#x#} \<Longrightarrow> P x y"
  by (auto simp: pairwise_mset_def)

lemma pairwise_msetD': "pairwise_mset P X \<Longrightarrow> {#x, y#} \<subseteq># X \<Longrightarrow> P x y"
  by (erule pairwise_msetD) (auto simp: insert_subset_eq_iff)

lemma pairwise_mset_empty [simp, intro]: "pairwise_mset P {#}"
  by (auto simp: pairwise_mset_def)

lemma pairwise_mset_singleton [simp, intro]: "pairwise_mset P {#x#}"
  by (auto simp: pairwise_mset_def)

lemma pairwise_mset_doubleton_iff [simp]: "pairwise_mset P {#x, y#} \<longleftrightarrow> P x y \<and> P y x"
  by (auto simp: pairwise_mset_def)

lemma pairwise_mset_add_mset:
  "pairwise_mset P (add_mset x X) \<longleftrightarrow> pairwise_mset P X \<and> (\<forall>y\<in>#X. P x y \<and> P y x)"
  by (auto simp: pairwise_mset_def)

lemma pairwise_mset_plus:
  "pairwise_mset P (X + Y) \<longleftrightarrow> pairwise_mset P X \<and> pairwise_mset P Y \<and> (\<forall>x\<in>#X. \<forall>y\<in>#Y. P x y \<and> P y x)"
  by (induction Y) (auto simp: pairwise_mset_add_mset)

lemma pairwise_mset_mono:
  "pairwise_mset P X \<Longrightarrow> (\<And>x y. x \<in># Y \<Longrightarrow> y \<in># Y - {#x#} \<Longrightarrow> P x y \<Longrightarrow> Q x y) \<Longrightarrow> Y \<subseteq># X \<Longrightarrow> pairwise_mset Q Y"
  unfolding pairwise_mset_def by (metis insert_DiffM insert_subset_eq_iff)

lemma sorted_wrt_sym_conv_pairwise_mset:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> P x y \<longleftrightarrow> P y x"
  shows   "sorted_wrt P xs \<longleftrightarrow> pairwise_mset P (mset xs)"
  using assms by (induction xs) (auto simp: pairwise_mset_add_mset)


subsection \<open>Definition of product trees\<close>


text \<open>
  A product tree in the classical sense is a binary tree that has a non-zero number attached to
  each leaf and each internal node has the product of its two immediate child nodes attached to it.

  We use a slightly more general structure which can carry additional information at the leaves
  as well. We also introduce a relation between a product tree and the list of its
  leaves traversed left-to-right.
\<close>

datatype ('a, 'b) prodtree = Leaf 'a 'b | Node "('a, 'b) prodtree" 'b "('a, 'b) prodtree"

fun rootval_prodtree :: "('a, 'b) prodtree \<Rightarrow> 'b" where
  "rootval_prodtree (Leaf _ m) = m"
| "rootval_prodtree (Node _ m _) = m"

fun flat_prodtree :: "('a, 'b) prodtree \<Rightarrow> ('a \<times> 'b) list"  where
  "flat_prodtree (Leaf x m) = [(x, m)]"
| "flat_prodtree (Node l _ r) = flat_prodtree l @ flat_prodtree r"


context
  assumes "SORT_CONSTRAINT('b :: semiring_gcd)"
begin

fun wf_prodtree :: "('a, 'b) prodtree \<Rightarrow> bool"  where
  "wf_prodtree (Leaf x m) \<longleftrightarrow> m \<noteq> 0"
| "wf_prodtree (Node l m r) \<longleftrightarrow>
     m = rootval_prodtree l * rootval_prodtree r \<and> 
     wf_prodtree l \<and> wf_prodtree r"

text \<open>
  We introduce a relator between a product tree and its flattening as a list.
\<close>
definition rel_prodtree' :: "('a, 'b) prodtree \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" where
  "rel_prodtree' t xs \<longleftrightarrow> xs = flat_prodtree t \<and> wf_prodtree t"

lemma rel_prodtree'I [intro?]: "xs = flat_prodtree t \<Longrightarrow> wf_prodtree t \<Longrightarrow> rel_prodtree' t xs"
  by (auto simp: rel_prodtree'_def)

lemma rel_prodtree_Leaf [simp]: "rel_prodtree' (Leaf x m) xs \<longleftrightarrow> xs = [(x, m)] \<and> m \<noteq> 0"
  by (auto simp: rel_prodtree'_def)

lemma flat_prodtree_neq_Nil [simp]: "flat_prodtree t \<noteq> Nil"
  by (induction t) auto

lemma Nil_neq_flat_prodtree [simp]: "Nil \<noteq> flat_prodtree t"
  by (induction t) auto

lemma not_rel_prodtree'_Nil [simp]: "\<not>rel_prodtree' t []"
  by (auto simp: rel_prodtree'_def)

lemma rel_prodtree'_NodeI:
  assumes "rel_prodtree' l xs" "rel_prodtree' r ys" "m = rootval_prodtree l * rootval_prodtree r"
  shows   "rel_prodtree' (Node l m r) (xs @ ys)"
  using assms by (auto simp: rel_prodtree'_def)

lemma rel_prodtree'_NodeE:
  assumes "rel_prodtree' (Node l m r) zs"
  obtains xs ys where
    "zs = xs @ ys" "rel_prodtree' l xs" "rel_prodtree' r ys" 
    "m = rootval_prodtree l * rootval_prodtree r"
    using assms by (auto simp: rel_prodtree'_def)

lemma rel_prodtree'_flat:
  assumes "rel_prodtree' t xs"
  shows   "flat_prodtree t = xs"
  using assms by (simp add: rel_prodtree'_def)

lemma set_flat_prodtree_dvd: "wf_prodtree t \<Longrightarrow> (x, y) \<in> set (flat_prodtree t) \<Longrightarrow> y dvd rootval_prodtree t"
  by (induction t; fastforce simp: image_def)

lemma wf_prodtree_imp_nonzero: "wf_prodtree t \<Longrightarrow> (x, y) \<in> set (flat_prodtree t) \<Longrightarrow> y \<noteq> 0"
  by (induction t) auto

lemma prod_list_flat_prodtree:
  assumes "wf_prodtree t"
  shows   "prod_list (map snd (flat_prodtree t)) = rootval_prodtree t"
  using assms by (induction t) auto

lemma rel_prodtree'_rootval_prodtree:
  assumes "rel_prodtree' t xs"
  shows   "rootval_prodtree t = prod_list (map snd xs)"
  using assms unfolding rel_prodtree'_def by (simp add: prod_list_flat_prodtree)



subsection \<open>Product trees with coprime branches\<close>

text \<open>
  In some contexts one requires an additional invariant in the product tree, namely that 
  the numbers attached to two disjoint branches are all coprime.
\<close>

primrec coprime_prodtree :: "('b, 'c :: algebraic_semidom) prodtree \<Rightarrow> bool" where
  "coprime_prodtree (Leaf x m) \<longleftrightarrow> True"
| "coprime_prodtree (Node l m r) \<longleftrightarrow>
     coprime (rootval_prodtree l) (rootval_prodtree r) \<and> coprime_prodtree l \<and> coprime_prodtree r"

lemma coprime_prodtree_flat:
  assumes "coprime_prodtree t" "wf_prodtree t" 
  shows   "sorted_wrt coprime (map snd (flat_prodtree t))"
  using assms
proof (induction t)
  case (Node l m r)
  thus ?case
    by (auto simp: sorted_wrt_append coprime_divisors dest!: set_flat_prodtree_dvd[rotated])
qed auto

lemma coprime_prodtree_altdef:
  assumes "wf_prodtree t"
  shows   "coprime_prodtree t \<longleftrightarrow> sorted_wrt coprime (map snd (flat_prodtree t))"
proof
  assume "sorted_wrt coprime (map snd (flat_prodtree t))"
  thus "coprime_prodtree t"
    using assms
  proof (induction t)
    case (Node l m r)
    have "coprime (prod_list (map snd (flat_prodtree l))) (prod_list (map snd (flat_prodtree r)))"
      by (intro prod_list_coprime_left prod_list_coprime_right) (use Node in \<open>auto simp: sorted_wrt_append\<close>)
    hence "coprime (rootval_prodtree l) (rootval_prodtree r)"
      by (subst (asm) (1 2) prod_list_flat_prodtree) (use Node.prems in auto)
    thus ?case
      using Node by (auto simp: sorted_wrt_append)
  qed auto
qed (use coprime_prodtree_flat[OF _ assms] in auto)

lemma coprime_prodtree_rel_prodtree':
  assumes "rel_prodtree' t xs"
  shows   "coprime_prodtree t \<longleftrightarrow> sorted_wrt coprime (map snd (flat_prodtree t))"
  using assms by (simp add: rel_prodtree'_def coprime_prodtree_altdef)


subsection \<open>Mapping\<close>

text \<open>
  We introduce a map operator that can modify both the number attached to the nodes and the
  extra information at the leaves.
\<close>

primrec map_prodtree' :: "('a \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a \<Rightarrow> 'e) \<Rightarrow> ('d, 'a) prodtree \<Rightarrow> ('e, 'c) prodtree" where
  "map_prodtree' f g (Leaf x m) = Leaf (g x m) (f m)"
| "map_prodtree' f g (Node l m r) = Node (map_prodtree' f g l) (f m) (map_prodtree' f g r)"

lemma map_prodtree'_cong:
  assumes "wf_prodtree t"
  assumes "\<And>m. m dvd rootval_prodtree t \<Longrightarrow> f m = f' m"
  assumes "\<And>m x. m dvd rootval_prodtree t \<Longrightarrow> x \<in> set1_prodtree t \<Longrightarrow> g x m = g' x m" "t = t'"
  shows   "map_prodtree' f g t = map_prodtree' f' g' t'"
  unfolding assms(4)[symmetric] using assms(1-3) by (induction t) auto

lemma flat_map_prodtree' [simp]:
  "flat_prodtree (map_prodtree' f g t) = map (\<lambda>(x,m). (g x m, f m)) (flat_prodtree t)"
  by (induction t) auto

lemma rootval_map_prodtree' [simp]:
  "rootval_prodtree (map_prodtree' f g t) = f (rootval_prodtree t)"
  by (cases t) auto

lemma wf_map_prodtree':
  assumes "wf_prodtree t" "\<And>x. f x = 0 \<Longrightarrow> x = 0" "\<And>x y. f (x * y) = f x * f y"
  shows   "wf_prodtree (map_prodtree' f g t)"
  using assms(1) by (induction t) (auto simp: assms(2-))

lemma rel_prodtree'_map:
  assumes "rel_prodtree' t xs"
  assumes "\<And>x. f x = 0 \<Longrightarrow> x = 0" "\<And>x y. f (x * y) = f x * f y"
  shows   "rel_prodtree' (map_prodtree' f g t) (map (\<lambda>(x,m). (g x m, f m)) xs)"
  using assms unfolding rel_prodtree'_def by (auto intro!: wf_map_prodtree')



subsection \<open>Product trees in the classical sense\<close>

text \<open>
  The operations below turn a list of numbers (possibly tagged with some additional information)
  into the corresponding product tree.
\<close>
fun prodtree_aux1 :: "('a, 'b) prodtree list \<Rightarrow> ('a, 'b) prodtree list" where
  "prodtree_aux1 [] = []"
| "prodtree_aux1 [x] = [x]"
| "prodtree_aux1 (x # y # xs) = Node x (rootval_prodtree x * rootval_prodtree y) y # prodtree_aux1 xs"

lemma length_prodtree_aux [simp]: "length (prodtree_aux1 xs) = (length xs + 1) div 2"
  by (induction xs rule: prodtree_aux1.induct) auto

fun prodtree_aux2 :: "('a, 'b) prodtree list \<Rightarrow> ('a, 'b) prodtree" where
  "prodtree_aux2 [] = undefined"
| "prodtree_aux2 [t] = t"
| "prodtree_aux2 ts = prodtree_aux2 (prodtree_aux1 ts)"

definition prodtree' :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) prodtree" where
  "prodtree' xs = prodtree_aux2 (map (\<lambda>(x,m). Leaf x m) xs)"

definition prodtree :: "'b list \<Rightarrow> (unit, 'b) prodtree" where
  "prodtree xs = prodtree_aux2 (map (\<lambda>m. Leaf () m) xs)"

lemma rootval_prodtree' [simp]: 
  assumes [simp]: "xs \<noteq> []"
  shows   "rootval_prodtree (prodtree' xs) = prod_list (map snd xs)"
proof -
  have [simp]: "prod_list (map rootval_prodtree (prodtree_aux1 ts)) = prod_list (map rootval_prodtree ts)"
    for ts :: "('a, 'b) prodtree list"
    by (induction ts rule: prodtree_aux1.induct) (auto simp: mult_ac)
  have *: "rootval_prodtree (prodtree_aux2 ts) = prod_list (map rootval_prodtree ts)" if "ts \<noteq> []"
    for ts :: "('a, 'b) prodtree list"
    using that by (induction ts rule: prodtree_aux2.induct) (auto simp: mult_ac)
  show ?thesis
    unfolding prodtree'_def by (subst *) (auto simp: o_def case_prod_unfold)
qed

lemma rel_prodtree'_prodtree':
  assumes "xs \<noteq> []" "0 \<notin> snd ` set xs"
  shows   "rel_prodtree' (prodtree' xs) xs"
proof
  have 1: "concat (map flat_prodtree (prodtree_aux1 ts)) = concat (map flat_prodtree ts)"
    for ts :: "('a, 'b) prodtree list"
    by (induction ts rule: prodtree_aux1.induct) auto
  have 2: "flat_prodtree (prodtree_aux2 ts) = concat (map flat_prodtree ts)" if "ts \<noteq> []"
    for ts :: "('a, 'b) prodtree list"
    using that by (induction ts rule: prodtree_aux2.induct) (auto simp: 1)
  show "xs = flat_prodtree (prodtree' xs)"
    unfolding prodtree'_def using assms(1) by (subst 2) (auto simp: o_def case_prod_unfold)
next
  define P :: "('a, 'b) prodtree list \<Rightarrow> bool"
    where "P = (\<lambda>ts. list_all wf_prodtree ts \<and> 0 \<notin> rootval_prodtree ` set ts)"

  have *: "rootval_prodtree ` set (prodtree_aux1 ts) \<subseteq> rootval_prodtree ` set ts \<union> (\<lambda>(m1,m2). rootval_prodtree m1 * rootval_prodtree m2) ` (set ts \<times> set ts)"
    for ts :: "('a, 'b) prodtree list"
    by (induction ts rule: prodtree_aux1.induct) auto

  have 1: "P (prodtree_aux1 ts)" if "P ts" for ts
    using that
  proof (induction ts rule: prodtree_aux1.induct)
    case (3 t1 t2 ts)
    show ?case
      unfolding P_def
    proof (intro conjI)
      show "list_all wf_prodtree (prodtree_aux1 (t1 # t2 # ts))"
        using 3 by (simp_all add: P_def pairwise_def)
    next
      have "rootval_prodtree ` set (prodtree_aux1 (t1 # t2 # ts)) \<subseteq>
              insert (rootval_prodtree t1 * rootval_prodtree t2)
                (rootval_prodtree ` set ts \<union> (\<lambda>(m1,m2). rootval_prodtree m1 * rootval_prodtree m2) ` (set ts \<times> set ts))"
        using *[of ts] by auto
      also have "\<dots> \<subseteq> -{0}"
        using 3 by (auto simp: P_def)
      finally show "0 \<notin> rootval_prodtree ` set (prodtree_aux1 (t1 # t2 # ts))"
        by auto
    qed
  qed (auto simp: P_def)

  have 2: "wf_prodtree (prodtree_aux2 ts)" if "P ts" "ts \<noteq> []" for ts
    using that
  proof (induction ts rule: prodtree_aux2.induct)
    case (3 t1 t2 ts)
    show ?case
      unfolding prodtree_aux2.simps by (intro "3.IH" 1) (use "3.prems" in auto)
  qed (auto simp: P_def)

  show "wf_prodtree (prodtree' xs)"
    unfolding prodtree'_def
    by (intro 2) (use assms in \<open>auto simp: P_def o_def case_prod_unfold list.pred_set image_def\<close>)
qed

end


subsection \<open>Remainder trees\<close>

text \<open>
  Using a product tree of non-zero numbers $(m_1, \ldots, m_k)$, one can efficiently compute the
  remainders $(n\ \text{mod}\ m_1, \ldots, n\ \text{mod}\ m_k)$ simultaneously.
\<close>

context
  assumes "SORT_CONSTRAINT('a :: {euclidean_semiring_cancel, euclidean_semiring_gcd})"
begin

fun mod_prodtree :: "'a \<Rightarrow> ('b, 'a) prodtree \<Rightarrow> ('b \<times> 'a, 'a) prodtree"  where
  "mod_prodtree n (Leaf x m) = Leaf (x, n mod m) m"
| "mod_prodtree n (Node l m r) = (
     let n' = n mod m
     in  Node (mod_prodtree n' l) m (mod_prodtree n' r))"

lemma mod_prodtree_altdef:
  assumes "wf_prodtree t"
  shows   "mod_prodtree n t = map_prodtree' id (\<lambda>x m. (x, n mod m)) t"
  using assms
  by (induction t rule: mod_prodtree.induct)
     (auto simp: Let_def mod_mod_cancel intro!: map_prodtree'_cong)

lemma rel_prodtree'_mod:
  assumes "rel_prodtree' t xs"
  shows   "rel_prodtree' (mod_prodtree n t) (map (\<lambda>(x,m). ((x, n mod m), m)) xs)"
proof -
  have wf: "wf_prodtree t"
    using assms by (auto simp: rel_prodtree'_def)
  have "rel_prodtree' (mod_prodtree n t) (map (\<lambda>(x, m). ((x, n mod m), id m)) xs)"
    unfolding mod_prodtree_altdef[OF wf] by (rule rel_prodtree'_map) (use assms in auto)
  thus ?thesis
    by simp
qed

end


subsection \<open>Linear combinations\<close>

text \<open>
  Given a product tree of the pairwise non-zero numbers $(m_1, \ldots, m_k)$ and a
  sequence of numbers $(a_1, \ldots, a_k)$ attached to them, one can efficiently compute the
  linear combination $\sum_{i=1}^k a_i M / m_i$, where $M = m_1\cdot\ldots\cdot m_k$.
\<close>

context
  assumes "SORT_CONSTRAINT('b :: semiring_gcd)"
begin

fun comb_prodtree :: "('b, 'b) prodtree \<Rightarrow> 'b" where
  "comb_prodtree (Leaf x m) = x"
| "comb_prodtree (Node l m r) =
     comb_prodtree l * rootval_prodtree r + comb_prodtree r * rootval_prodtree l"

lemma rel_prodtree'_comb:
  assumes "rel_prodtree' t xs"
  defines "M \<equiv> prod_list (map snd xs)"
  shows   "comb_prodtree t = (\<Sum>(x, m)\<leftarrow>xs. x * (M div m))"
proof -
  have "wf_prodtree t"
    using assms by (simp add: rel_prodtree'_def)
  hence "comb_prodtree t = (\<Sum>(x, m)\<leftarrow>flat_prodtree t. x * (rootval_prodtree t div m))"
    unfolding M_def
  proof (induction t)
    case (Node l m r)
    define ls where "ls = flat_prodtree l"
    define rs where "rs = flat_prodtree r"
    define m1 where "m1 = rootval_prodtree l"
    define m2 where "m2 = rootval_prodtree r"
    have "(\<Sum>(x, a)\<leftarrow>flat_prodtree (Node l m r). x * (rootval_prodtree (Node l m r) div a)) =
          (\<Sum>(x, a)\<leftarrow>ls. x * ((m1 * m2) div a)) + (\<Sum>(x, a)\<leftarrow>rs. x * ((m1 * m2) div a))"
      using Node.prems by (simp add: ls_def rs_def m1_def m2_def)

    also have "map (\<lambda>(x, a). x * ((m1 * m2) div a)) ls = map (\<lambda>(x,a). x * m2 * (m1 div a)) ls"
      using Node.prems
      by (intro map_cong refl)
         (auto simp: ls_def m1_def div_mult_swap[OF set_flat_prodtree_dvd] mult_ac)
    also have "sum_list \<dots> = (\<Sum>(x, a)\<leftarrow>ls. x * (m1 div a)) * m2"
      by (induction ls) (auto simp: algebra_simps)
    also have "\<dots> = comb_prodtree l * m2"
      using Node by (simp add: ls_def m1_def m2_def)

    also have "map (\<lambda>(x, a). x * ((m1 * m2) div a)) rs = map (\<lambda>(x,a). x * (m1 * (m2 div a))) rs"
      using Node.prems
      by (intro map_cong refl)
         (auto simp: rs_def m2_def div_mult_swap[OF set_flat_prodtree_dvd] mult_ac)
    also have "sum_list \<dots> = (\<Sum>(x, a)\<leftarrow>rs. x * (m2 div a)) * m1"
      by (induction rs) (auto simp: algebra_simps)
    also have "\<dots> = comb_prodtree r * m1"
      using Node by (simp add: rs_def m1_def m2_def)

    finally show ?case
      by (simp add: m1_def m2_def mult_ac)
  qed auto

  also have "flat_prodtree t = xs"
    using assms by (simp add: rel_prodtree'_def)
  also have "rootval_prodtree t = M"
    using rel_prodtree'_rootval_prodtree[OF assms(1)] by (simp add: M_def)
  finally show ?thesis .
qed

end



subsection \<open>Chinese remaindering\<close>

text \<open>
  Putting all these ingredients together, we can implement an efficient Chinese remaindering
  algorithm using product trees: given $k$ pairs of numbers $(a_i, m_i)$ where the $m_i$ are
  pairwise coprime and non-zero, we compute the unique number $x \in [0, M)$ such that
  \[x\ \text{mod}\ m_1 = a_1\quad \ldots\quad x\ \text{mod}\ m_k = a_k\]
  where $M = m_1 \cdot\ldots\cdot m_k$.

  In contrast to the presentation in the book, we do some deforestation and fuse as many operations
  as possible together for a more concise implementation. The proof does not actually become any
  more complicated.
\<close>

context
  assumes "SORT_CONSTRAINT('a :: {euclidean_semiring_cancel, euclidean_ring_gcd})"
begin                                          

fun crt_prodtree_aux :: "'a \<Rightarrow> ('a, 'a) prodtree \<Rightarrow> 'a" where
  "crt_prodtree_aux M (Leaf x m) = x * modular_inverse m (M mod (m^2) div m)"
| "crt_prodtree_aux M (Node l m r) = (let M' = M mod m^2 in
     crt_prodtree_aux M' l * rootval_prodtree r + crt_prodtree_aux M' r * rootval_prodtree l)"

definition crt_prodtree :: "('a \<times> 'a) list \<Rightarrow> 'a \<times> 'a" where
  "crt_prodtree xs =
     (let t1 = prodtree' xs; M = rootval_prodtree t1 in (crt_prodtree_aux M t1 mod M, M))"


lemma crt_prodtree_aux_eq:
  fixes M :: 'a
  assumes "wf_prodtree t"
  defines "i \<equiv> (\<lambda>M m. modular_inverse m (M mod (m^2) div m))"
  shows   "crt_prodtree_aux M t = (\<Sum>(x,m)\<leftarrow>flat_prodtree t. x * i M m * rootval_prodtree t div m)"
  using assms(1)
proof (induction t arbitrary: M)
  case (Node l m' r)
  define L where "L = rootval_prodtree l"
  define R where "R = rootval_prodtree r"

  have "crt_prodtree_aux M (Node l m' r) =
          (\<Sum>(x,m)\<leftarrow>flat_prodtree l. x * modular_inverse m (M mod (L * R)\<^sup>2 mod m\<^sup>2 div m) * L div m * R) +
          (\<Sum>(x,m)\<leftarrow>flat_prodtree r. x * modular_inverse m (M mod (L * R)\<^sup>2 mod m\<^sup>2 div m) * R div m * L)"
    using Node by (simp add: i_def Let_def L_def R_def case_prod_unfold flip: sum_list_mult_const)
  also have "(\<Sum>(x,m)\<leftarrow>flat_prodtree l. x * modular_inverse m (M mod (L * R)\<^sup>2 mod m\<^sup>2 div m) * L div m * R) =
             (\<Sum>(x,m)\<leftarrow>flat_prodtree l. x * modular_inverse m (M mod (m^2) div m) * (L*R) div m)"
  proof (intro arg_cong[of _ _ sum_list] map_cong refl, safe)
    fix x m assume xm: "(x, m) \<in> set (flat_prodtree l)"
    have "m dvd L"
      using Node(3) set_flat_prodtree_dvd[OF _ xm] by (force simp: L_def)
    show "x * modular_inverse m (M mod (L * R)^2 mod m^2 div m) * L div m * R =
          x * modular_inverse m (M mod m^2 div m) * (L*R) div m"
      using \<open>m dvd L\<close> by (auto simp: mod_mod_cancel dvd_power_same)
  qed    
  also have "(\<Sum>(x,m)\<leftarrow>flat_prodtree r. x * modular_inverse m (M mod (L * R)\<^sup>2 mod m\<^sup>2 div m) * R div m * L) =
             (\<Sum>(x,m)\<leftarrow>flat_prodtree r. x * modular_inverse m (M mod (m^2) div m) * (L*R) div m)"
  proof (intro arg_cong[of _ _ sum_list] map_cong refl, safe)
    fix x m assume xm: "(x, m) \<in> set (flat_prodtree r)"
    have "m dvd R"
      using Node(3) set_flat_prodtree_dvd[OF _ xm] by (force simp: R_def)
    show "x * modular_inverse m (M mod (L * R)^2 mod m^2 div m) * R div m * L =
          x * modular_inverse m (M mod m^2 div m) * (L*R) div m"
      using \<open>m dvd R\<close> by (auto simp: mod_mod_cancel dvd_power_same)
  qed   
  finally show ?case using Node.prems
    by (simp add: i_def Let_def case_prod_unfold L_def R_def)
qed (auto simp: i_def)

end


context
  assumes "SORT_CONSTRAINT('a :: {euclidean_semiring_cancel, euclidean_ring_gcd})"
begin            

lemma crt_prodtree_aux_cong:
  assumes "wf_prodtree t" and "coprime_prodtree t" and "(y, n) \<in> set (flat_prodtree t)"
  defines "M \<equiv> rootval_prodtree t"
  shows   "[crt_prodtree_aux M t = y] (mod n)"
proof -
  define A' where "A' = mset (flat_prodtree t)"
  define A where "A = image_mset snd (mset (flat_prodtree t))"
  have pw_coprime: "pairwise_mset coprime A"
    unfolding A_def using coprime_prodtree_flat[OF assms(2,1)]
    by (simp add: coprime_commute sorted_wrt_sym_conv_pairwise_mset)

  have "crt_prodtree_aux M t = (\<Sum>(x,m)\<leftarrow>flat_prodtree t. x * modular_inverse m (M mod (m^2) div m) * M div m)"
    unfolding M_def by (rule crt_prodtree_aux_eq) fact
  also have "[\<dots> = (\<Sum>(x,m)\<leftarrow>flat_prodtree t. if m = n then x else 0)] (mod n)"
  proof (intro cong_sum_list' list.rel_refl_strong, safe)
    fix x m
    assume xm: "(x, m) \<in> set (flat_prodtree t)"
    have "m \<in># A" "n \<in># A"
      using xm assms unfolding A_def by force+

    have "m dvd M" "n dvd M"
      using assms xm by (simp_all add: set_flat_prodtree_dvd)
    show "[x * modular_inverse m (M mod m\<^sup>2 div m) * M div m = (if m = n then x else 0)] (mod n)"
    proof (cases "m = n")
      case True
      define z where "z = modular_inverse m (M mod m\<^sup>2 div m)"
      have cong: "[M div m = M mod m\<^sup>2 div m] (mod m)"
        by (smt (verit) \<open>m dvd M\<close> div_by_0 dvdE mod_mod_trivial mod_mult_mult1 nonzero_mult_div_cancel_left power2_eq_square unique_euclidean_semiring_class.cong_def)

      have "coprime m (M div m)"
      proof -
        define X where "X = A - {#m#}"
        have [simp]: "m \<noteq> 0"
          using xm assms wf_prodtree_imp_nonzero by fast
        have "M = prod_mset A" using assms
          by (simp add: A_def M_def prod_mset_prod_list prod_list_flat_prodtree flip: mset_map)
        also have "A = {#m#} + X"
          using \<open>m \<in># A\<close> unfolding X_def A_def by auto
        also have "prod_mset \<dots> = m * prod_mset X"
          by simp
        finally have "M div m = prod_mset X"
          by simp
    
        have "coprime m (prod_mset X)"
        proof (rule prod_mset_coprime_right)
          fix x assume x: "x \<in># X"
          show "coprime m x"
            using pw_coprime by (rule pairwise_msetD) (use x \<open>m \<in># A\<close> in \<open>auto simp: X_def\<close>)
        qed
        with \<open>M div m = prod_mset X\<close> show ?thesis
          by simp
      qed
      hence coprime: "coprime (M mod m\<^sup>2 div m) m"
        using cong_imp_coprime coprime_commute cong by blast

      have "x * modular_inverse m (M mod m\<^sup>2 div m) * M div m = x * (z * (M div m))"
        using \<open>m dvd M\<close> by (auto simp: algebra_simps z_def elim!: dvdE)
      also have "[\<dots> = x * (z * (M mod m\<^sup>2 div m))] (mod m)"
        using cong by (intro cong_mult cong_refl)
      also have "[x * (z * (M mod m\<^sup>2 div m)) = x * 1] (mod m)"
        unfolding z_def using coprime by (intro cong_mult cong_refl cong_modular_inverse2)
      finally show ?thesis
        by (simp add: True)
    next
      case False
      from pw_coprime have "coprime m n"
        by (rule pairwise_msetD') (use False \<open>m \<in># A\<close> \<open>n \<in># A\<close> in \<open>auto simp: insert_subset_eq_iff\<close>)
      with \<open>m dvd M\<close> and \<open>n dvd M\<close> have "n dvd (M div m)"
        using assms by (metis coprime_commute coprime_dvd_mult_left_iff dvd_div_mult_self)
      thus ?thesis
        using False \<open>m dvd M\<close> by (auto simp: cong_0_iff elim!: dvdE)
    qed
  qed
  also have "(\<Sum>(x,m)\<leftarrow>flat_prodtree t. if m = n then x else 0) = 
             (\<Sum>(x,m)\<leftarrow>filter (\<lambda>(x,m). m = n) (flat_prodtree t). x)"
    by (simp add: sum_list_map_filter' case_prod_unfold)

  also have "[\<dots> = y] (mod n)"
  proof (cases "is_unit n")
    case False
    have "(\<Sum>(x,m)\<leftarrow>filter (\<lambda>(x,m). m = n) (flat_prodtree t). x) = 
          (\<Sum>(x,m)\<in>#filter_mset (\<lambda>(x,m). m = n) A'. x)"
      by (simp flip: sum_mset_sum_list add: A'_def)
    also have "filter_mset (\<lambda>(x,m). m = n) A' = {#(y, n)#}"
    proof -
      define X where "X = A' - {#(y, n)#}"
      have *: "A' = {#(y, n)#} + X"
        using assms by (auto simp: X_def A'_def)
      hence "filter_mset (\<lambda>(x, m). m = n) A' = {#(y, n)#} + filter_mset (\<lambda>(x, m). m = n) X"
        by simp
      also have "filter_mset (\<lambda>(x, m). m = n) X = filter_mset (\<lambda>_. False) X"
      proof (intro filter_mset_cong refl; safe)
        fix x assume xn: "(x, n) \<in># X"
        have "{#(x,n), (y,n)#} \<subseteq># A'"
          using xn assms by (auto simp: *)
        hence "image_mset snd {#(x,n), (y,n)#} \<subseteq># A"
          unfolding A'_def A_def by (rule image_mset_subseteq_mono)
        hence "{#n, n#} \<subseteq># A"
          by simp
        from pw_coprime and this have "coprime n n"
          by (rule pairwise_msetD')
        hence "is_unit n"
          by auto
        thus False
          using \<open>\<not>is_unit n\<close> by contradiction
      qed
      finally show ?thesis
        by simp
    qed
    finally show ?thesis
      by simp
  qed (simp_all add: cong_def unit_imp_mod_eq_0)

  finally show ?thesis
    by simp
qed

theorem snd_crt_prodtree: "xs \<noteq> [] \<Longrightarrow> snd (crt_prodtree xs) = prod_list (map snd xs)"
  by (simp add: crt_prodtree_def Let_def)

theorem cong_fst_crt_prodtree:
  assumes "sorted_wrt coprime (map snd xs)" "0 \<notin> snd ` set xs" "xs \<noteq> []" "(x, m) \<in> set xs"
  shows   "[fst (crt_prodtree xs) = x] (mod m)"
proof -
  define t where "t = prodtree' xs"
  have t: "rel_prodtree' t xs"
    unfolding t_def by (rule rel_prodtree'_prodtree') (use assms in auto)

  have "[fst (crt_prodtree xs) = crt_prodtree_aux (rootval_prodtree t) t] (mod (prod_list (map snd xs)))"
    using \<open>xs \<noteq> []\<close> by (simp add: t_def crt_prodtree_def Let_def)
  moreover have "m dvd prod_mset (mset (map snd xs))"
    using assms by (intro dvd_prod_mset) force+
  ultimately have "[fst (crt_prodtree xs) = crt_prodtree_aux (rootval_prodtree t) t] (mod m)"
    unfolding prod_mset_prod_list using cong_dvd_mono_modulus by blast
  also have "[crt_prodtree_aux (rootval_prodtree t) t = x] (mod m)"
  proof (rule crt_prodtree_aux_cong)
    show "wf_prodtree t" "(x, m) \<in> set (flat_prodtree t)" "coprime_prodtree t"
      using t coprime_prodtree_rel_prodtree'[OF t] assms by (auto simp: rel_prodtree'_def)
  qed
  finally show "[fst (crt_prodtree xs) = x] (mod m)" .
qed

end

end
