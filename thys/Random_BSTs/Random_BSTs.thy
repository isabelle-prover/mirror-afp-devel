(*
  File:     Random_BSTs.thy
  Author:   Manuel Eberl <eberlm@in.tum.de>

  Expected shape of random Binary Search Trees
*)
section \<open>Expected shape of random Binary Search Trees\<close>
theory Random_BSTs
  imports
    Complex_Main
    "~~/src/HOL/Probability/Random_Permutations"
    "~~/src/HOL/Data_Structures/Tree_Set"
    "../Quick_Sort_Cost/Quick_Sort_Average_Case"
begin

(* TODO: Hide this in the proper place *)
hide_const (open) Tree_Set.insert  
  
subsection \<open>Auxiliary lemmas\<close>
  
(* TODO: Move? *)
lemma linorder_on_linorder_class [intro]: 
  "linorder_on UNIV {(x, y). x \<le> (y :: 'a :: linorder)}"
  by (auto simp: linorder_on_def refl_on_def antisym_def trans_def total_on_def)

lemma Nil_in_permutations_of_set_iff [simp]: "[] \<in> permutations_of_set A \<longleftrightarrow> A = {}"
  by (auto simp: permutations_of_set_def)

lemma max_power_distrib_right:
  fixes a :: "'a :: linordered_semidom"
  shows "a > 1 \<Longrightarrow> max (a ^ b) (a ^ c) = a ^ max b c"  
  by (auto simp: max_def)

lemma set_tree_empty_iff [simp]: "set_tree t = {} \<longleftrightarrow> t = Leaf"
  by (cases t) auto
    
lemma card_set_tree_bst: "bst t \<Longrightarrow> card (set_tree t) = size t"
proof (induction t) 
  case (Node l x r)
  have "set_tree \<langle>l, x, r\<rangle> = insert x (set_tree l \<union> set_tree r)" by simp
  also from Node.prems have "card \<dots> = Suc (card (set_tree l \<union> set_tree r))"
    by (intro card_insert_disjoint) auto
  also from Node have "card (set_tree l \<union> set_tree r) = size l + size r"
    by (subst card_Un_disjoint) force+
  finally show ?case by simp
qed simp_all

lemma pair_pmf_cong:
  "p = p' \<Longrightarrow> q = q' \<Longrightarrow> pair_pmf p q = pair_pmf p' q'"
  by simp

lemma expectation_add_pair_pmf:
  fixes f :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "finite (set_pmf p)" and "finite (set_pmf q)"
  shows "measure_pmf.expectation (pair_pmf p q) (\<lambda>(x,y). f x + g y) =
           measure_pmf.expectation p f + measure_pmf.expectation q g"
proof -
  have "measure_pmf.expectation (pair_pmf p q) (\<lambda>(x,y). f x + g y) =
          measure_pmf.expectation (pair_pmf p q) (\<lambda>z. f (fst z) + g (snd z))" 
    by (simp add: case_prod_unfold)
  also have "\<dots> = measure_pmf.expectation (pair_pmf p q) (\<lambda>z. f (fst z)) +
                  measure_pmf.expectation (pair_pmf p q) (\<lambda>z. g (snd z))"
    by (intro Bochner_Integration.integral_add integrable_measure_pmf_finite) (auto intro: assms)
  also have "measure_pmf.expectation (pair_pmf p q) (\<lambda>z. f (fst z)) =
               measure_pmf.expectation (map_pmf fst (pair_pmf p q)) f" by simp
  also have "map_pmf fst (pair_pmf p q) = p" by (rule map_fst_pair_pmf)
  also have "measure_pmf.expectation (pair_pmf p q) (\<lambda>z. g (snd z)) =
               measure_pmf.expectation (map_pmf snd (pair_pmf p q)) g" by simp
  also have "map_pmf snd (pair_pmf p q) = q" by (rule map_snd_pair_pmf)
  finally show ?thesis .
qed

  
subsection \<open>Creating a BST from a list\<close>

text \<open>
  The following recursive function creates a binary search tree from a given list of 
  elements by inserting them into an initially empty BST from left to right. We will prove
  that this is the case later, but the recursive definition has the advantage of giving us 
  a useful induction rule, so we chose that definition and prove the alternative definitions later.

  This recursion, which already almost looks like QuickSort, will be key in analysing the 
  shape distributions of random BSTs.
\<close>
fun bst_of_list :: "'a :: linorder list \<Rightarrow> 'a tree" where
  "bst_of_list [] = Leaf"
| "bst_of_list (x # xs) =
     Node (bst_of_list [y \<leftarrow> xs. y < x]) x (bst_of_list [y \<leftarrow> xs. y > x])"
  
lemma bst_of_list_eq_Leaf_iff [simp]: "bst_of_list xs = Leaf \<longleftrightarrow> xs = []"
  by (induction xs) auto

lemma bst_of_list_snoc [simp]:
  "bst_of_list (xs @ [y]) = Tree_Set.insert y (bst_of_list xs)"
  by (induction xs rule: bst_of_list.induct) auto
    
lemma bst_of_list_append:
  "bst_of_list (xs @ ys) = fold Tree_Set.insert ys (bst_of_list xs)"
proof (induction ys arbitrary: xs)
  case (Cons y ys)
  have "bst_of_list (xs @ (y # ys)) = bst_of_list ((xs @ [y]) @ ys)" by simp
  also have "\<dots> = fold Tree_Set.insert ys (bst_of_list (xs @ [y]))"
    by (rule Cons.IH)
  finally show ?case by simp
qed simp_all

text \<open>
  The following now shows that the recursive function indeed corresponds to the 
  notion of inserting the elements from the list from left to right.
\<close>
lemma bst_of_list_altdef: "bst_of_list xs = fold Tree_Set.insert xs Leaf"
  using bst_of_list_append[of "[]" xs] by simp

lemma size_bst_insert: "x \<notin> set_tree t \<Longrightarrow> size (Tree_Set.insert x t) = Suc (size t)"
  by (induction t) auto

lemma set_bst_insert [simp]: "set_tree (Tree_Set.insert x t) = insert x (set_tree t)"
  by (induction t) auto

lemma set_bst_of_list [simp]: "set_tree (bst_of_list xs) = set xs"
  by (induction xs rule: rev_induct) simp_all

lemma size_bst_of_list_distinct [simp]:
  assumes "distinct xs"
  shows   "size (bst_of_list xs) = length xs"
  using assms by (induction xs rule: rev_induct) (auto simp: size_bst_insert)
    


subsection \<open>Random BSTs\<close>

text \<open>
  Analogously to the previous section, we can now view the concept of a random BST 
  (i.\,e.\ a BST obtained by inserting a given set of elements in random order) in two 
  different ways.

  We again start with the recursive variant:
\<close>
function random_bst :: "'a :: linorder set \<Rightarrow> 'a tree pmf" where
  "random_bst A = 
     (if \<not>finite A \<or> A = {} then 
        return_pmf Leaf
      else do {
        x \<leftarrow> pmf_of_set A;
        l \<leftarrow> random_bst {y \<in> A. y < x};
        r \<leftarrow> random_bst {y \<in> A. y > x};
        return_pmf (Node l x r)
     })"
  by auto
termination by (relation finite_psubset) auto
    
declare random_bst.simps [simp del]
  
lemma random_bst_empty [simp]: "random_bst {} = return_pmf Leaf"
  by (simp add: random_bst.simps)

lemma set_pmf_random_permutation [simp]:
  "finite A \<Longrightarrow> set_pmf (pmf_of_set (permutations_of_set A)) = {xs. distinct xs \<and> set xs = A}"
  by (subst set_pmf_of_set) (auto dest: permutations_of_setD)

text \<open>
  The alternative characterisation is the more intuitive one where we simply pick a 
  random permutation of the set elements uniformly at random and insert them into an empty
  tree from left to right:
\<close>
lemma random_bst_altdef:
  assumes "finite A"
  shows   "random_bst A = map_pmf bst_of_list (pmf_of_set (permutations_of_set A))"
using assms
proof (induction A rule: finite_psubset_induct)
  case (psubset A)
  define L R where "L = (\<lambda>x. {y\<in>A. y < x})" and "R = (\<lambda>x. {y\<in>A. y > x})"
  {
    fix x assume x: "x \<in> A"
    hence *: "L x \<subset> A" "R x \<subset> A" by (auto simp: L_def R_def)
    note this [THEN psubset.IH]
  } note IH = this
    
  show ?case
  proof (cases "A = {}")
    case False
    note A = \<open>finite A\<close> \<open>A \<noteq> {}\<close>
    have "random_bst A = 
            do {
              x \<leftarrow> pmf_of_set A;
              (l, r) \<leftarrow> pair_pmf (random_bst (L x)) (random_bst (R x));
              return_pmf (Node l x r)
            }" using A unfolding pair_pmf_def L_def R_def
      by (subst random_bst.simps) (simp add: bind_return_pmf bind_assoc_pmf)
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      (l, r) \<leftarrow> pair_pmf 
                        (map_pmf bst_of_list (pmf_of_set (permutations_of_set (L x))))
                        (map_pmf bst_of_list (pmf_of_set (permutations_of_set (R x))));
                      return_pmf (Node l x r)
                    }"
     using A by (intro bind_pmf_cong refl) (simp_all add: IH)
    also have "\<dots> = do {
                     x \<leftarrow> pmf_of_set A;
                     (ls, rs) \<leftarrow> pair_pmf (pmf_of_set (permutations_of_set (L x))) 
                                          (pmf_of_set (permutations_of_set (R x)));
                     return_pmf (Node (bst_of_list ls) x (bst_of_list rs))
                   }" unfolding map_pair [symmetric]
      by (simp add: map_pmf_def case_prod_unfold bind_return_pmf bind_assoc_pmf)
    also have "L = (\<lambda>x. {y \<in> A - {x}. y \<le> x})" by (auto simp: L_def)
    also have "R = (\<lambda>x. {y \<in> A - {x}. \<not>y \<le> x})" by (auto simp: R_def)
    also have "do {
                 x \<leftarrow> pmf_of_set A;
                 (ls, rs) \<leftarrow> pair_pmf (pmf_of_set (permutations_of_set {y \<in> A - {x}. y \<le> x})) 
                                      (pmf_of_set (permutations_of_set {y \<in> A - {x}. \<not>y \<le> x}));
                 return_pmf (Node (bst_of_list ls) x (bst_of_list rs))
               } = 
               do {
                 x \<leftarrow> pmf_of_set A;
                 (ls, rs) \<leftarrow> map_pmf (partition (\<lambda>y. y \<le> x)) 
                               (pmf_of_set (permutations_of_set (A - {x})));
                 return_pmf (Node (bst_of_list ls) x (bst_of_list rs))
               }" using \<open>finite A\<close>
      by (intro bind_pmf_cong refl partition_random_permutations [symmetric]) auto
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      (ls, rs) \<leftarrow> map_pmf (\<lambda>xs. ([y\<leftarrow>xs. y < x], [y\<leftarrow>xs. y > x])) 
                                    (pmf_of_set (permutations_of_set (A - {x})));
                      return_pmf (Node (bst_of_list ls) x (bst_of_list rs))
                    }" using A
      by (intro bind_pmf_cong refl map_pmf_cong)
         (auto intro!: filter_cong dest: permutations_of_setD simp: order.strict_iff_order)
    also have "\<dots> = map_pmf bst_of_list (pmf_of_set (permutations_of_set A))"
      using A by (subst random_permutation_of_set[of A])
                 (auto simp: map_pmf_def bind_return_pmf o_def bind_assoc_pmf not_le)
    finally show ?thesis .
  qed (simp_all add: pmf_of_set_singleton)
qed

lemma finite_set_random_bst [simp, intro]:
  "finite A \<Longrightarrow> finite (set_pmf (random_bst A))"
  by (simp add: random_bst_altdef)

lemma random_bst_code [code]:
  "random_bst (set xs) = map_pmf bst_of_list (pmf_of_set (permutations_of_set (set xs)))"
  by (rule random_bst_altdef) simp_all

lemma random_bst_singleton [simp]: "random_bst {x} = return_pmf (Node Leaf x Leaf)"
  by (simp add: random_bst_altdef pmf_of_set_singleton)

lemma size_random_bst:
  assumes "t \<in> set_pmf (random_bst A)" "finite A"
  shows   "size t = card A"
proof -
  from assms obtain xs where "distinct xs" "A = set xs" "t = bst_of_list xs"
    by (auto simp: random_bst_altdef dest: permutations_of_setD)
  thus ?thesis using \<open>finite A\<close> by (simp add: distinct_card)
qed

text \<open>
  We can also re-phrase the non-recursive definition using the @{const fold_random_permutation}
  combinator from the HOL-Probability library, which folds over a given set in random order.
\<close>
lemma random_bst_altdef':
  assumes "finite A"
  shows   "random_bst A = fold_random_permutation Tree_Set.insert Leaf A"
proof -
  have "random_bst A = map_pmf bst_of_list (pmf_of_set (permutations_of_set A))"
    using assms by (simp add: random_bst_altdef)
  also have "\<dots> = map_pmf (\<lambda>xs. fold Tree_Set.insert xs Leaf) (pmf_of_set (permutations_of_set A))"
    using assms by (intro map_pmf_cong refl) (auto simp: bst_of_list_altdef)
  also from assms have "\<dots> = fold_random_permutation Tree_Set.insert Leaf A"
    by (simp add: fold_random_permutation_fold)
  finally show ?thesis .
qed


subsection \<open>Expected height\<close>

text \<open>
  For the purposes of the analysis of the expected height, we define the following notion
  of `expected height', which is essentially two to the power of the height (as defined
  by Cormen \textit{et al.}) with a special treatment for the empty tree, which has exponential 
  height 0.

  Note that the height defined by Cormen \textit{et al.}\ differs from the @{const height}
  function here in Isabelle in that for them, the height of the empty tree is undefined and 
  the height of a singleton tree is 0 etc., whereas in Isabelle, the height of the empty tree is
  0 and the height of a singleton tree is 1.
\<close>
definition eheight :: "'a tree \<Rightarrow> nat" where
  "eheight t = (if t = Leaf then 0 else 2 ^ (height t - 1))"

lemma eheight_Leaf [simp]: "eheight Leaf = 0"
  by (simp add: eheight_def)

lemma eheight_Node_singleton [simp]: "eheight (Node Leaf x Leaf) = 1"
  by (simp add: eheight_def)

lemma eheight_Node: 
  "l \<noteq> Leaf \<or> r \<noteq> Leaf \<Longrightarrow> eheight (Node l x r) = 2 * max (eheight l) (eheight r)"
  by (cases l; cases r) (simp_all add: eheight_def max_power_distrib_right)
  

text \<open>
  We now define the following upper bound on the expected exponential height due to 
  Cormen\ \textit{et\ al.}~\cite{cormen}:
\<close>  
definition eheight_exp_approx :: "nat \<Rightarrow> real" where
  "eheight_exp_approx n = real ((n + 3) choose 3) / 4"
 
text \<open>
  We then show that this is indeed an upper bound on the expected exponential height by induction
  over the set of elements. This proof mostly follows that by Cormen\ \textit{et al.}~\cite{cormen}, 
  and partially an answer on the Computer Science Stack Exchange~\cite{sofl}.
\<close>
lemma eheight_expectation_bound:
  assumes "finite A"
  shows   "measure_pmf.expectation (random_bst A) eheight \<le> eheight_exp_approx (card A)"
using assms
proof (induction A rule: finite_psubset_induct)
  case (psubset A)
  define n where "n = card A"
  write measure_pmf.expectation ("EXP _ _" [1000, 1000] 1000)
  consider "card A = 0" | "card A = 1" | "card A > 1" by linarith
  thus ?case
  proof cases
    assume "card A = 0"
    with \<open>finite A\<close> show ?thesis by (simp add: eheight_def eheight_exp_approx_def)
  next
    assume "card A = 1"
    then obtain x where "A = {x}" by (erule card_1_singletonE)
    thus ?thesis by (simp add: eheight_exp_approx_def eheight_def eval_nat_numeral)
  next
    assume "card A > 1"
    hence "A \<noteq> {}" by auto
    note A = \<open>finite A\<close> \<open>A \<noteq> {}\<close>
    from A have n: "n \<noteq> 0" by (auto simp: n_def)
    let ?rank = "linorder_rank {(x,y). x \<le> y} A"
    let ?eheight' = "\<lambda>t::'a tree. if t = Leaf then 0 else (2 ^ height t :: nat)"
      
    have "EXP (random_bst A) (\<lambda>t. real (eheight t)) =
            measure_pmf.expectation (map_pmf (\<lambda>t. real (eheight t)) (random_bst A)) id"
      unfolding integral_map_pmf using A
      by (intro integral_cong_AE) (auto simp: random_bst_altdef eheight_def AE_measure_pmf_iff)
    also have "map_pmf (\<lambda>t. real (eheight t)) (random_bst A) =
      pmf_of_set A \<bind> (\<lambda>x. map_pmf (\<lambda>(l,r). real (eheight (Node l x r))) 
        (pair_pmf (random_bst {y\<in>A. y < x}) (random_bst {y\<in>A. y > x})))"
      using A by (subst random_bst.simps)
                 (simp_all add: A map_pmf_def bind_assoc_pmf bind_return_pmf pair_pmf_def)
    also have "\<dots> = 
      pmf_of_set A \<bind> (\<lambda>x. map_pmf (\<lambda>(l,r). 2 * real (max (eheight l) (eheight r)))
        (pair_pmf (random_bst {y\<in>A. y < x}) (random_bst {y\<in>A. y > x})))"
    proof (intro bind_pmf_cong map_pmf_cong refl, clarify, goal_cases)
      case (1 x l r)
      from 1 and A have "card (A - {x}) = card A - 1" by simp
      with \<open>card A > 1\<close> have "A - {x} \<noteq> {}" by (intro notI) simp_all
      also have "A - {x} = {y \<in> A. y < x} \<union> {y \<in> A. y > x}" by auto
      finally have "{y \<in> A. y < x} \<noteq> {} \<or> {y \<in> A. y > x} \<noteq> {}" by blast
      with 1(2) and A have "l \<noteq> Leaf \<or> r \<noteq> Leaf" by (auto simp: random_bst_altdef)
      thus ?case by (simp add: eheight_Node)
    qed
    also from A have "EXP \<dots> id = 
      (\<Sum>x\<in>A. EXP (pair_pmf (random_bst {y \<in> A. y < x}) (random_bst {y \<in> A. x < y}))
                (\<lambda>(l,r). 2 * max (eheight l) (eheight r))) / n" (is "_ = ?S / _")
      by (subst pmf_expectation_bind_pmf_of_set)
         (auto intro!: finite_cartesian_product
               simp: case_prod_unfold n_def sum_divide_distrib field_simps)
    also have "?S \<le> (\<Sum>x\<in>A. 2 * (eheight_exp_approx (?rank x) +
                                 eheight_exp_approx (n - 1 - ?rank x)))"
    proof (intro sum_mono, goal_cases)
      case (1 x)
      define lhs where 
        "lhs = EXP (pair_pmf (random_bst {y \<in> A. y < x}) (random_bst {y \<in> A. x < y}))
                   (\<lambda>(l,r). 2 * real (max (eheight l) (eheight r)))"
      have "lhs = 2 * EXP (pair_pmf (random_bst {y \<in> A. y < x}) (random_bst {y \<in> A. x < y}))
                          (\<lambda>(l,r). real (max (eheight l) (eheight r)))" (is "_ = _ * ?E")
        by (subst integral_mult_right_zero [symmetric]) (simp add: case_prod_unfold lhs_def)
      also have "?E \<le> EXP (pair_pmf (random_bst {y \<in> A. y < x}) (random_bst {y \<in> A. x < y}))
                  (\<lambda>(l,r). real (eheight l) + real (eheight r))"
        using A by (intro integral_mono integrable_measure_pmf_finite)
                   (auto simp: finite_cartesian_product max_def split: if_splits)
      also have "\<dots> = EXP (random_bst {y \<in> A. y < x}) eheight +
                      EXP (random_bst {y \<in> A. y > x}) eheight"
        unfolding eheight_def using A by (intro expectation_add_pair_pmf) auto
      also have "\<dots> \<le> eheight_exp_approx (card {y \<in> A. y < x}) + 
                      eheight_exp_approx (card {y \<in> A. y > x})"
        using \<open>x \<in> A\<close> by (intro add_mono psubset.IH) auto
      also have "{y \<in> A. y > x} = A - {x} - {y \<in> A. y < x}" by auto
      also have "card \<dots> = n - 1 - card {y \<in> A. y < x}"
        using A and \<open>x \<in> A\<close>  by (subst card_Diff_subset) (auto simp: n_def)
      also have "card {y \<in> A. y < x} = ?rank x"
        by (simp add: linorder_rank_def order.strict_iff_order conj_comms)
      finally show ?case unfolding lhs_def by (simp_all add: case_prod_unfold)
    qed
    also have "\<dots> = 2 * (\<Sum>x\<in>A. eheight_exp_approx (?rank x) +
                                eheight_exp_approx (n - 1 - ?rank x))" (is "_ = _ * ?S")
      by (simp add: sum_distrib_left)
    also have "?S = (\<Sum>i<n. eheight_exp_approx i + eheight_exp_approx (n - 1 - i))"
      unfolding n_def using A by (intro sum.reindex_bij_betw bij_betw_linorder_rank[of UNIV]) auto
    also have "\<dots> = (\<Sum>i<n. eheight_exp_approx i) + (\<Sum>i<n. eheight_exp_approx (n - 1 - i))"
      by (simp add: sum.distrib)
    also have "(\<Sum>i<n. eheight_exp_approx (n - 1 - i)) = (\<Sum>i<n. eheight_exp_approx i)"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>i. n - 1 - i" "\<lambda>i. n - 1 - i"]) auto
    also have "2 * (\<dots> + \<dots>) = 4 * \<dots>" by simp
    also have "4 * (\<Sum>i<n. eheight_exp_approx i) / real n = 
                 (\<Sum>i<n. (i + 3) choose 3) / real n"
      using n by (simp add: eheight_exp_approx_def sum_divide_distrib [symmetric])
    also have "(\<Sum>i<n. (i + 3) choose 3) = (\<Sum>i\<le>n - 1. (i + 3) choose 3)"
      using n by (intro sum.cong refl) auto
    also have "\<dots> = (n + 3) choose 4"
      using choose_rising_sum(1)[of 3 "n - 1"] n by (simp add: add_ac Suc3_eq_add_3)
    also have "real ((n + 3) choose 4) = fact (n + 3) / (fact 4 * fact (n - 1))"
      using n by (subst binomial_fact) simp_all
    also have "\<dots> / n = fact (n + 3) / (fact 3 * fact n) / 4"
      using n by (simp add: divide_simps fact_reduce[of n] fact_reduce[of 4])
    also have "fact (n + 3) / (fact 3 * fact n) = ((n + 3) choose 3)"
      using n by (subst binomial_fact) simp_all
    also have "real ((n + 3) choose 3) / 4 = eheight_exp_approx n"
      by (simp add: eheight_exp_approx_def)
    finally show ?thesis using A by (simp add: n_def divide_simps)
  qed
qed


text \<open>
  Since the function $\uplambda x.\ 2 ^ x$ is convex, we can then easily derive a bound on the
  actual height using Jensen's inequality:
\<close>
definition height_exp_approx :: "nat \<Rightarrow> real" where
  "height_exp_approx n = log 2 (eheight_exp_approx n) + 1"
  
theorem height_expectation_bound:
  assumes "finite A" "A \<noteq> {}"
  shows   "measure_pmf.expectation (random_bst A) height
             \<le> height_exp_approx (card A)"
proof -
  have "convex_on UNIV (op powr 2)"
    by (intro convex_on_realI[where f' = "\<lambda>x. ln 2 * 2 powr x"])
       (auto intro!: derivative_eq_intros DERIV_powr simp: powr_def [abs_def])
  hence "2 powr measure_pmf.expectation (random_bst A) (\<lambda>t. real (height t - 1)) \<le>
          measure_pmf.expectation (random_bst A) (\<lambda>t. 2 powr real (height t - 1))"
    using assms
    by (intro measure_pmf.jensens_inequality[where I = UNIV])
       (auto intro!: integrable_measure_pmf_finite)
  also have "(\<lambda>t. 2 powr real (height t - 1)) = (\<lambda>t. 2 ^ (height t - 1))"
    by (simp add: powr_realpow)
  also have "measure_pmf.expectation (random_bst A) (\<lambda>t. 2 ^ (height t - 1)) = 
               measure_pmf.expectation (random_bst A) (\<lambda>t. real (eheight t))"
    using assms
    by (intro integral_cong_AE)
       (auto simp: AE_measure_pmf_iff random_bst_altdef eheight_def)
  also have "\<dots> \<le> eheight_exp_approx (card A)" by (rule eheight_expectation_bound) fact+
  also have "measure_pmf.expectation (random_bst A) (\<lambda>t. real (height t - 1)) =
               measure_pmf.expectation (random_bst A) (\<lambda>t. real (height t) - 1)"
  proof (intro integral_cong_AE AE_pmfI, goal_cases)
    case (3 t)
    with \<open>A \<noteq> {}\<close> and assms show ?case 
      by (subst of_nat_diff) (auto simp: Suc_le_eq random_bst_altdef height_0_iff_Leaf)
  qed auto
  finally have "2 powr measure_pmf.expectation (random_bst A) (\<lambda>t. real (height t) - 1)
                  \<le> eheight_exp_approx (card A)" .
  hence "log 2 (2 powr measure_pmf.expectation (random_bst A) (\<lambda>t. real (height t) - 1)) \<le>
           log 2 (eheight_exp_approx (card A))" (is "?lhs \<le> ?rhs")
    by (subst log_le_cancel_iff) (auto simp: eheight_exp_approx_def)
  also have "?lhs = measure_pmf.expectation (random_bst A) (\<lambda>t. real (height t) - 1)"
    by simp
  also have "\<dots> = measure_pmf.expectation (random_bst A) (\<lambda>t. real (height t)) - 1"
    using assms 
    by (subst Bochner_Integration.integral_diff) (auto intro!: integrable_measure_pmf_finite)
  finally show ?thesis by (simp add: height_exp_approx_def)
qed
  
text \<open>
  This upper bound is asymptotically equivalent to $c \ln n$ with 
  $c = \frac{3}{\ln 2} \approx 4.328$. This is actually a relatively tight upper bound, since 
  the exact asymptotics of the expected height of a random BST is $c \ln n$ with 
  $c \approx 4.311$.~\cite{reed} However, the proof of these precise asymptotics is very intricate
  and we will therefore be content with the upper bound.

  In particular, we can now show that the expected height is $O(\log n)$.
\<close>
lemma ln_sum_bigo_ln: "(\<lambda>x::real. ln (x + c)) \<in> O(ln)"
proof (rule bigoI_tendsto)
  from eventually_gt_at_top[of "1::real"] show "eventually (\<lambda>x::real. ln x \<noteq> 0) at_top"
    by eventually_elim simp_all
next
  show "((\<lambda>x. ln (x + c) / ln x) \<longlongrightarrow> 1) at_top"
  proof (rule lhospital_at_top_at_top)
    show "eventually (\<lambda>x. ((\<lambda>x. ln (x + c)) has_real_derivative inverse (x + c)) (at x)) at_top"
      using eventually_gt_at_top[of "-c"]
      by eventually_elim (auto intro!: derivative_eq_intros simp: field_simps)
    show "eventually (\<lambda>x. ((\<lambda>x. ln x) has_real_derivative inverse x) (at x)) at_top"
      using eventually_gt_at_top[of 0]
      by eventually_elim (auto intro!: derivative_eq_intros simp: field_simps)
    show "((\<lambda>x. inverse (x + c) / inverse x) \<longlongrightarrow> 1) at_top"
    proof (rule Lim_transform_eventually)
      show "eventually (\<lambda>x. inverse (1 + c / x) = inverse (x + c) / inverse x) at_top"
        using eventually_gt_at_top[of "0::real"] eventually_gt_at_top[of "-c"] 
        by eventually_elim (simp add: field_simps)
      have "((\<lambda>x. inverse (1 + c / x)) \<longlongrightarrow> inverse (1 + 0)) at_top"
        by (intro tendsto_inverse tendsto_add tendsto_const 
              real_tendsto_divide_at_top[OF tendsto_const] filterlim_ident) simp_all
      thus "((\<lambda>x. inverse (1 + c / x)) \<longlongrightarrow> 1) at_top" by simp
    qed
  qed (auto simp: ln_at_top eventually_at_top_not_equal)
qed

corollary height_expectation_bigo: "height_exp_approx \<in> O(ln)"
proof -
  let ?T = "\<lambda>x::real. log 2 (x + 1) + log 2 (x + 2) + log 2 (x + 3) + (1 - log 2 24)"
  have "eventually (\<lambda>n. height_exp_approx n = 
          log 2 (real n + 1) + log 2 (real n + 2) + log 2 (real n + 3) + (1 - log 2 24)) at_top"
    (is "eventually (\<lambda>n. _ = ?T n) at_top") using eventually_gt_at_top[of "0::nat"]
  proof eventually_elim
    case (elim n)
    have "height_exp_approx n = log 2 (real (n + 3 choose 3) / 4) + 1"
      by (simp add: height_exp_approx_def eheight_exp_approx_def log_divide)
    also have "real ((n + 3) choose 3) = real (n + 3) gchoose 3"
      by (simp add: binomial_gbinomial)
    also have "\<dots> / 4 = (real n + 1) * (real n + 2) * (real n + 3) / 24"
      by (simp add: gbinomial_pochhammer' numeral_3_eq_3 pochhammer_Suc add_ac)
    also have "log 2 \<dots> = log 2 (real n + 1) + log 2 (real n + 2) + log 2 (real n + 3) - log 2 24"
      by (simp add: log_divide log_mult)
    finally show ?case by simp
  qed
  hence "height_exp_approx \<in> \<Theta>(?T)" by (rule bigthetaI_cong)
  also have *: "(\<lambda>x. ln (x + c) / ln 2) \<in> O(ln)" for c :: real
    by (subst landau_o.big.cdiv_in_iff') (auto intro!: ln_sum_bigo_ln)
  have "?T \<in> O(\<lambda>n. ln (real n))" unfolding log_def
    by (intro bigo_real_nat_transfer sum_in_bigo ln_sum_bigo_ln *) simp_all
  finally show ?thesis .
qed


subsection \<open>Lookup costs\<close>

text \<open>
  The following function describes the cost incurred when looking up a specific element 
  in a specific BST. The cost corresponds to the number of edges traversed in the lookup.
\<close>

primrec lookup_cost :: "'a :: linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
  "lookup_cost x Leaf = 0"
| "lookup_cost x (Node l y r) = 
     (if x = y then 0
      else if x < y then Suc (lookup_cost x l)
      else Suc (lookup_cost x r))"
  
text \<open>
  Some of the literature defines these costs as 1 in the case that the current node is
  the correct one, i.\,e.\ their costs are our costs plus 1. These alternative costs are
  exactly the number of comparisons performed in the lookup. Our cost function has the 
  advantage of precisely summing up to the internal path length and therefore gives us 
  slightly nicer results, and since the difference is only a ${}+1$ in the end, this 
  variant seemed more reasonable.
\<close>

text \<open>
  It can be shown with a simple induction that The sum of all lookup costs in a tree is the 
  internal path length of the tree.
\<close>
theorem sum_lookup_costs: 
  fixes t :: "'a :: linorder tree"
  assumes "bst t"
  shows   "(\<Sum>x\<in>set_tree t. lookup_cost x t) = path_len t"
using assms
proof (induction t)
  case (Node l x r)
  from Node.prems 
    have disj: "x \<notin> set_tree l" "x \<notin> set_tree r" "set_tree l \<inter> set_tree r = {}" by force+
  have "set_tree (Node l x r) = insert x (set_tree l \<union> set_tree r)" by simp
  also have "(\<Sum>y\<in>\<dots>. lookup_cost y (Node l x r)) = lookup_cost x \<langle>l, x, r\<rangle> + 
               (\<Sum>y\<in>set_tree l. lookup_cost y \<langle>l, x, r\<rangle>) + (\<Sum>y\<in>set_tree r. lookup_cost y \<langle>l, x, r\<rangle>)"
    using disj by (simp add: sum.union_disjoint)
  also have "(\<Sum>y\<in>set_tree l. lookup_cost y \<langle>l, x, r\<rangle>) = (\<Sum>y\<in>set_tree l. 1 + lookup_cost y l)"
    using disj and Node by (intro sum.cong refl) auto
  also have "\<dots> = size l + path_len l" using Node 
    by (subst sum.distrib) (simp_all add: card_set_tree_bst)
  also have "(\<Sum>y\<in>set_tree r. lookup_cost y \<langle>l, x, r\<rangle>) = (\<Sum>y\<in>set_tree r. 1 + lookup_cost y r)"
    using disj and Node by (intro sum.cong refl) auto
  also have "\<dots> = size r + path_len r" using Node
    by (subst sum.distrib) (simp_all add: card_set_tree_bst)
  finally show ?case by simp
qed simp_all

text \<open>
  This allows us to easily show that the expected cost of looking up a random element in a 
  fixed tree is the internal path length divided by the number of elements.
\<close>
theorem expected_lookup_cost:
  assumes "bst t" "t \<noteq> Leaf"
  shows   "measure_pmf.expectation (pmf_of_set (set_tree t)) (\<lambda>x. lookup_cost x t) = 
             path_len t / size t"
  using assms by (subst integral_pmf_of_set)
                 (simp_all add: sum_lookup_costs of_nat_sum [symmetric] card_set_tree_bst)
                 
text \<open>
  Therefore, we will now turn to analysing the internal path length of a random BST. This 
  then clearly related to the expected lookup costs of a random element in a random BST by
  the above result.
\<close>


subsection \<open>Average Path Length\<close>

text \<open>
  The internal path length satisfies the recursive equation @{thm path_len.simps(2)[of l x r]}.
  This is quite similar to the number of comparisons performed by QuickSort, and indeed, we can
  reduce the internal path length of a random BST to the number of comparisons performed by 
  QuickSort on a randomly-ordered list relatively easily:
\<close>
theorem map_pmf_random_bst_eq_rqs_cost:
  assumes "finite A"
  shows   "map_pmf path_len (random_bst A) = rqs_cost (card A)"
using assms
proof (induction A rule: finite_psubset_induct)
  case (psubset A)
  show ?case
  proof (cases "A = {}")
    case False
    note A = \<open>finite A\<close> \<open>A \<noteq> {}\<close>
    define n where "n = card A - 1"
    define rank :: "'a \<Rightarrow> nat" where "rank = linorder_rank {(x,y). x \<le> y} A"
    from A have card: "card A = Suc n" by (cases "card A") (auto simp: n_def)
    from A have "map_pmf path_len (random_bst A) =
                   do {
                     x \<leftarrow> pmf_of_set A;
                     (l,r) \<leftarrow> pair_pmf (random_bst {y \<in> A. y < x}) (random_bst {y \<in> A. y > x});
                     return_pmf (path_len (Node l x r))
                   }" 
      by (subst random_bst.simps) 
         (simp_all add: pair_pmf_def card map_pmf_def bind_assoc_pmf bind_return_pmf)
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      (l,r) \<leftarrow> pair_pmf (random_bst {y \<in> A. y < x}) (random_bst {y \<in> A. y > x});
                      return_pmf (n + path_len l + path_len r)
                    }"
    proof (intro bind_pmf_cong refl, clarify, goal_cases)
      case (1 x l r)
      from 1 and A have "n = card (A - {x})" by (simp add: n_def)
      also have "A - {x} = {y\<in>A. y < x} \<union> {y\<in>A. y > x}" by auto
      also have "card \<dots> = card {y\<in>A. y < x} + card {y\<in>A. y > x}"
        using \<open>finite A\<close> by (intro card_Un_disjoint) auto
      also from 1 and A have "card {y\<in>A. y < x} = size l" by (auto dest: size_random_bst)
      also from 1 and A have "card {y\<in>A. y > x} = size r" by (auto dest: size_random_bst)   
      finally show ?case by simp
    qed
    also have "\<dots> = do {
                      x \<leftarrow> pmf_of_set A;
                      (l,r) \<leftarrow> pair_pmf (map_pmf path_len (random_bst {y \<in> A. y < x})) 
                                        (map_pmf path_len (random_bst {y \<in> A. y > x}));
                      return_pmf (n + l + r)
                    }" by (simp add: map_pair [symmetric] case_prod_unfold bind_map_pmf)
    also have "\<dots> = do {
                      i \<leftarrow> map_pmf rank (pmf_of_set A);
                      (l,r) \<leftarrow> pair_pmf (rqs_cost i) (rqs_cost (n - i));
                      return_pmf (n + l + r)
                    }" (is "_ = bind_pmf _ ?f") unfolding bind_map_pmf
    proof (intro bind_pmf_cong refl pair_pmf_cong, goal_cases)
      case (1 x)
      have "map_pmf path_len (random_bst {y \<in> A. y < x}) = rqs_cost (card {y \<in> A. y < x})"
        using 1 and A by (intro psubset.IH) auto
      also have "{y \<in> A. y < x} = {y \<in> A - {x}. y \<le> x}" by auto
      hence "card {y \<in> A. y < x} = rank x" by (simp add: rank_def linorder_rank_def)
      finally show ?case .
    next
      case (2 x)
      have "map_pmf path_len (random_bst {y \<in> A. y > x}) = rqs_cost (card {y \<in> A. y > x})"
        using 2 and A by (intro psubset.IH) auto
      also have "{y \<in> A. y > x} = A - {x} - {y \<in> A - {x}. y \<le> x}" by auto
      hence "card {y \<in> A. y > x} = card \<dots>" by (simp only:)
      also from 2 and A have "\<dots> = n - rank x"
        by (subst card_Diff_subset) (auto simp: rank_def linorder_rank_def n_def)
      finally show ?case .
    qed
    also from A have "map_pmf rank (pmf_of_set A) = pmf_of_set {..<card A}"
      unfolding rank_def by (intro map_pmf_of_set_bij_betw bij_betw_linorder_rank[of UNIV]) auto
    also have "{..<card A} = {..n}" by (auto simp: card)
    also have "pmf_of_set \<dots> \<bind> ?f = rqs_cost (card A)"
      by (simp add: pair_pmf_def bind_assoc_pmf bind_return_pmf card)
    finally show ?thesis .
  qed simp_all
qed

text \<open>
  In particular, this means that the expected values are the same:
\<close>
corollary expected_path_len_random_bst_eq:
  assumes "finite A"
  shows   "measure_pmf.expectation (random_bst A) path_len = rqs_cost_exp (card A)"
proof -
  have "measure_pmf.expectation (random_bst A) path_len =
          measure_pmf.expectation (map_pmf path_len (random_bst A)) real" by simp
  also from assms have "map_pmf path_len (random_bst A) = rqs_cost (card A)"
    by (rule map_pmf_random_bst_eq_rqs_cost)
  also have "measure_pmf.expectation \<dots> real = rqs_cost_exp (card A)"
    by (rule expectation_rqs_cost)
  finally show ?thesis .
qed
  
text \<open>
  Therefore, the results about the expected number of comparisons of QuickSort carry over 
  to the expected internal path length:
\<close>
corollary expected_path_len_random_bst_eq':
  assumes "finite A"
  shows   "measure_pmf.expectation (random_bst A) path_len = 
             2 * real (card A + 1) * harm (card A) - 4 * real (card A)"
  by (simp add: expected_path_len_random_bst_eq rqs_cost_exp_eq assms)  
  
end
