section \<open>Increasing binary trees\<close>
theory Increasing_Binary_Trees
  imports Alternating_Permutations "HOL-Library.Tree"
begin

text \<open>
  We will now look at a second combinatorial application of the zigzag numbers $E_n$.

  An increasing binary trees is one where

    \<^item> the root contains the smallest element

    \<^item> no element is contained in the tree twice

    \<^item> if a node has exactly one non-leaf child, it must be the left child

    \<^item> if a node has two non-leaf children, the element attached to the left one must be
      smaller than that of the right one

  Another way to think of this is as a heap with no duplicate elements where each node
  has either 0, 1, or 2 children and the order of the children does not matter. This is however
  slightly more awkward to express.

  We will show below that the number of increasing binary trees with $n$ nodes with values 
  from a set with $n$ elements is $E_n$.

  We do this by showing that the number of increasing binary trees satisfies the same recurrence
  as $E_n$.
\<close>


text \<open>
  The following relation represents the condition that a non-leaf child must always be to the
  left of a leaf child, and a right node child must have a value greater than a left node child.
\<close>
definition le_root :: "'a :: ord tree \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "le_root t1 t2 =
     (case t1 of
        Leaf \<Rightarrow> t2 = Leaf 
      | Node _ x _ \<Rightarrow> (case t2 of Leaf \<Rightarrow> True | Node _ y _ \<Rightarrow> x \<le> y))"

text \<open>
  The following predicate models the notion that a binary tree is increasing.
\<close>
primrec inc_tree :: "'a :: linorder tree \<Rightarrow> bool" where
  "inc_tree Leaf = True"
| "inc_tree (Node l x r) \<longleftrightarrow> inc_tree l \<and> inc_tree r \<and> le_root l r \<and>
     (\<forall>y\<in>set_tree l \<union> set_tree r. x < y) \<and> set_tree l \<inter> set_tree r = {}"


text \<open>
  We introduce the following abbreviation for the set of increasing binary trees that have
  exactly the values from the given set attached to them.
\<close>
definition Inc_Trees :: "'a :: linorder set \<Rightarrow> 'a tree set" where
  "Inc_Trees A = {t. set_tree t = A \<and> inc_tree t}"

lemma Inc_Trees_empty [simp]: "Inc_Trees {} = {Leaf}"
  by (auto simp: Inc_Trees_def)

lemma Inc_Trees_infinite_eq_empty [simp]:
  assumes "\<not>finite A"
  shows   "Inc_Trees A = {}"
  using assms finite_set_tree unfolding Inc_Trees_def by blast


text \<open>
  For our proof later, we will need to also consider the set of ``almost'' increasing
  binary trees, i.e.\ binary trees that are increasing if the left and right child of the
  root are swapped.
\<close>
primrec mirror_root :: "'a tree \<Rightarrow> 'a tree" where
  "mirror_root Leaf = Leaf"
| "mirror_root (Node l x r) = Node r x l"

lemma mirror_root_mirror_root [simp]: "mirror_root (mirror_root t) = t"
  by (cases t) auto

lemma set_tree_mirror_root [simp]: "set_tree (mirror_root t) = set_tree t"
  by (cases t) auto

definition Inc_Trees' :: "'a :: linorder set \<Rightarrow> 'a tree set" where
  "Inc_Trees' A = {t. set_tree t = A \<and> inc_tree (mirror_root t)}"

lemma Inc_Trees'_empty [simp]: "Inc_Trees' {} = {Leaf}"
  by (auto simp: Inc_Trees'_def)

lemma Inc_Trees'_infinite_eq_empty [simp]:
  assumes "\<not>finite A"
  shows   "Inc_Trees' A = {}"
  using assms finite_set_tree unfolding Inc_Trees'_def by blast

text \<open>
  Since swapping the children of the root is an involution, the number of increasing binary trees
  and the number of almost increasing binary trees is the same.
\<close>
lemma bij_betw_mirror_root_Inc_Trees: "bij_betw mirror_root (Inc_Trees A) (Inc_Trees' A)"
  by (rule bij_betwI[of mirror_root _ _ mirror_root]) (auto simp: Inc_Trees_def Inc_Trees'_def)

lemma card_Inc_Trees' [simp]: "card (Inc_Trees' A) = card (Inc_Trees A)"
  using bij_betw_same_card[OF bij_betw_mirror_root_Inc_Trees[of A]] by simp

text \<open>
  Except for the obvious case $|A| \leq 1$, a tree cannot be both increasing and almost
  increasing.
\<close>
lemma disjoint_Inc_Trees_Inc_Trees':
  assumes "card A > 1"
  shows   "Inc_Trees A \<inter> Inc_Trees' A = {}"
proof safe
  fix t assume t: "t \<in> Inc_Trees A" "t \<in> Inc_Trees' A"
  obtain l x r where t_eq: "t = Node l x r"
    using t assms by (cases t) (auto simp: Inc_Trees_def)
  have "le_root l r \<and> le_root r l" "set_tree l \<inter> set_tree r = {}"
    using t by (auto simp: t_eq Inc_Trees_def Inc_Trees'_def)
  hence "l = Leaf \<and> r = Leaf"
    by (cases l; cases r; force simp: le_root_def)
  moreover have "A = {x} \<union> set_tree l \<union> set_tree r"
    using t by (simp add: Inc_Trees_def t_eq)
  ultimately have "A = {x}"
    by simp
  thus "t \<in> {}"
    using assms by simp
qed
    


text \<open>
  If we take any subset $X$ of a set $A$, pick increasing binary trees $l$ on $X$ and $r$ on
  $A\setminus X$ and then make them the left and right child, respectively, of a new node with a
  value $x$ that is smaller than all values in $A$, then we obtain exactly all increasing 
  and almost increasing binary trees on $A\cup\{x\}$.
\<close>
lemma Inc_Trees_insert_min:
  assumes "\<And>y. y \<in> A \<Longrightarrow> x < y"
  shows   "Inc_Trees (insert x A) \<union> Inc_Trees' (insert x A) =
             (\<Union>X\<in>Pow A. \<Union>l\<in>Inc_Trees X. \<Union>r\<in>Inc_Trees (A-X). {Node l x r})"
proof ((intro equalityI subsetI; (elim UN_E)?), goal_cases)
  case (1 t)
  then obtain l x' r where t_eq: "t = Node l x' r"
    using assms by (cases t) (auto simp: Inc_Trees_def Inc_Trees'_def)
  define X where "X = set_tree l"
  have "x \<notin> A"
    using assms by force
  have "x' \<notin> set_tree l \<union> set_tree r"
    using 1 unfolding Inc_Trees_def Inc_Trees'_def t_eq by auto
  have "set_tree t = insert x' (set_tree l \<union> set_tree r)"
    by (simp add: Inc_Trees_def t_eq)
  also have "set_tree t = insert x A"
    using 1 by (auto simp: Inc_Trees_def Inc_Trees'_def)
  finally have [simp]: "x' = x" using assms
    using assms 1 \<open>x \<notin> A\<close> \<open>x' \<notin> set_tree l \<union> set_tree r\<close>
    by (fastforce simp: Inc_Trees_def Inc_Trees'_def t_eq insert_eq_iff Un_commute)
  have "X \<inter> set_tree r = {}"
    using 1 unfolding X_def by (auto simp: Inc_Trees_def Inc_Trees'_def t_eq)
  have "set_tree t = insert x (X \<union> set_tree r)"
    by (simp add: t_eq X_def)
  also have "set_tree t = insert x A"
    using 1 by (auto simp: Inc_Trees_def Inc_Trees'_def t_eq)
  finally have "set_tree r = A - X"
    using \<open>X \<inter> set_tree r = {}\<close> \<open>x' \<notin> _\<close> \<open>x \<notin> A\<close>
    by (auto simp: insert_eq_iff)

  have "X \<in> Pow A"
    using \<open>set_tree t = insert x A\<close> \<open>x' \<notin> _\<close> unfolding X_def t_eq by auto
  moreover have "l \<in> Inc_Trees X"
    using 1 by (auto simp add: X_def Inc_Trees_def Inc_Trees'_def t_eq)
  moreover have "r \<in> Inc_Trees (A - X)"
    using 1 \<open>set_tree r = A - X\<close> by (auto simp add: Inc_Trees_def Inc_Trees'_def t_eq)
  ultimately show "t \<in> (\<Union>X\<in>Pow A. \<Union>l\<in>Inc_Trees X. \<Union>r\<in>Inc_Trees (A - X). {\<langle>l, x, r\<rangle>})"
    unfolding t_eq \<open>x' = x\<close> by blast
next
  case (2 t X l r)
  have "le_root l r \<or> le_root r l"
    by (cases l; cases r) (force simp: le_root_def)+    
  thus ?case
    using 2 assms
    by (auto simp: Inc_Trees_def Inc_Trees'_def)
qed

lemma Inc_Trees_singleton [simp]: "Inc_Trees {x} = {Node Leaf x Leaf}"
  and Inc_Trees'_singleton [simp]: "Inc_Trees' {x} = {Node Leaf x Leaf}"
proof -
  have "Inc_Trees {x} \<union> Inc_Trees' {x} = {Node Leaf x Leaf}"
    by (subst Inc_Trees_insert_min) auto
  moreover have "Inc_Trees {x} \<noteq> {}"
    by (auto simp: Inc_Trees_def le_root_def intro!: exI[of _ "Node Leaf x Leaf"])
  moreover have "Inc_Trees' {x} \<noteq> {}"
    by (auto simp: Inc_Trees'_def le_root_def intro!: exI[of _ "Node Leaf x Leaf"])
  ultimately show "Inc_Trees {x} = {Node Leaf x Leaf}" "Inc_Trees' {x} = {Node Leaf x Leaf}"
    by (simp_all add: Un_singleton_iff)
qed

lemma Diff_right_commute: "A - B - C = A - C - (B :: 'a set)"
  by blast

text \<open>
  We can therefore derive the following recurrence on the set of increasing and almost increasing
  binary trees on a set $A$: pick the smallest element $x$ in $A$ as a minimum, then pick
  a subset $X$ of $A\setminus\{x\}$ and any increasing trees on $X$ as the left child and any
  increasing tree on $X\setminus(A\cup\{x\})$ as the right child.
\<close>
lemma Inc_Trees_rec:
  assumes "finite A" "A \<noteq> {}"
  defines "x \<equiv> Min A"
  shows   "Inc_Trees A \<union> Inc_Trees' A = 
             (\<Union>X\<in>Pow (A-{x}). \<Union>l\<in>Inc_Trees X. \<Union>r\<in>Inc_Trees (A-X-{x}). {Node l x r})"
proof -
  define A' where "A' = A - {x}"
  have 1: "x \<le> y" if "y \<in> A" for y
    unfolding x_def by (rule Min.coboundedI) (use assms that in auto)
  have 2: "x < y" if "y \<in> A'" for y
    using 1[of y] that by (auto simp: A'_def)
  have "x \<in> A"
    unfolding x_def by (rule Min_in) (use assms in auto)
  hence "A = insert x A'"
    by (auto simp: A'_def)
  also have "Inc_Trees (insert x A') \<union> Inc_Trees' (insert x A') = 
               (\<Union>X\<in>Pow A'. \<Union>l\<in>Inc_Trees X. \<Union>r\<in>Inc_Trees (A' - X). {\<langle>l, x, r\<rangle>})"
    by (subst Inc_Trees_insert_min) (use 2 in auto)
  finally show ?thesis
    by (simp add: A'_def Diff_right_commute)
qed

lemma Inc_Trees_rec':
  assumes "finite A" "A \<noteq> {}"
  defines "x \<equiv> Min A"
  shows   "Inc_Trees A \<union> Inc_Trees' A = 
             (\<lambda>(_, (l, r)). Node l x r) ` (SIGMA X:Pow (A-{x}). Inc_Trees X \<times> Inc_Trees (A - X - {x}))"
  unfolding Inc_Trees_rec[OF assms(1,2)] x_def
  unfolding Sigma_def image_UN image_insert image_empty image_Union image_image prod.case
  by blast

lemma finite_Inc_Trees [intro]: "finite (Inc_Trees A)"
  and finite_Inc_Trees' [intro]: "finite (Inc_Trees' A)"
proof -
  have "finite (Inc_Trees A \<union> Inc_Trees' A)"
  proof (cases "finite A")
    case True
    thus ?thesis
    proof (induction rule: finite_psubset_induct)
      case (psubset A)
      have IH: "finite (Inc_Trees B)" if "B \<subset> A" for B
        using psubset.IH[of B] that by blast
      show ?case
      proof (cases "A = {}")
        case False
        hence "Min A \<in> A"
          using psubset.hyps by (intro Min_in) auto
        have "Inc_Trees A \<union> Inc_Trees' A = (\<lambda>(_, l, y). \<langle>l, Min A, y\<rangle>) ` 
                 (SIGMA X:Pow (A - {Min A}). Inc_Trees X \<times> Inc_Trees (A - X - {Min A}))"
          by (intro Inc_Trees_rec') (use False psubset.hyps in auto)
        also have "finite \<dots>"
          using \<open>Min A \<in> A\<close> psubset.hyps
          by (intro finite_imageI finite_SigmaI IH) auto
        finally show ?thesis .
      qed auto
    qed
  qed simp_all
  thus "finite (Inc_Trees A)" and "finite (Inc_Trees' A)"
    by auto
qed

text \<open>
  By taking the cardinality of both sides, we obtain the following recurrence on twice the
  number of increasing trees. Note that this only holds for $|A| > 1$ since otherwise the set
  of increasing and almost increasing trees are not disjoint.
\<close>
lemma card_Inc_Trees_rec:
  assumes "finite A" "card A > 1"
  defines "x \<equiv> Min A"
  shows   "2 * card (Inc_Trees A) =
             (\<Sum>X\<in>Pow (A - {x}). card (Inc_Trees X) * card (Inc_Trees (A - X - {x})))"
proof -
  have "A \<noteq> {}"
    using assms by auto
  have "Inc_Trees A \<union> Inc_Trees' A =
          (\<lambda>(_, (l, r)). Node l x r) ` (SIGMA X:Pow (A-{x}). Inc_Trees X \<times> Inc_Trees (A - X - {x}))"
    unfolding x_def by (rule Inc_Trees_rec') fact+
  also have "card \<dots> = card (SIGMA X:Pow (A - {x}). Inc_Trees X \<times> Inc_Trees (A - X - {x}))"
  proof (rule card_image)
    show "inj_on (\<lambda>(_, l, r). \<langle>l, x, r\<rangle>)
            (SIGMA X:Pow (A - {x}). Inc_Trees X \<times> Inc_Trees (A - X - {x}))"
      by (rule inj_onI) (auto simp: Inc_Trees_def)
  qed
  also have "\<dots> = (\<Sum>X\<in>Pow (A - {x}). card (Inc_Trees X) * card (Inc_Trees (A - X - {x})))"
    using assms by (subst card_SigmaI) (auto simp: card_cartesian_product)
  also have "card (Inc_Trees A \<union> Inc_Trees' A) = card (Inc_Trees A) + card (Inc_Trees' A)"
  proof (rule card_Un_disjoint)
    have False if t: "t \<in> Inc_Trees A \<inter> Inc_Trees' A" for t
    proof -
      from t obtain l x r where t_eq: "t = Node l x r"
        using \<open>A \<noteq> {}\<close> by (cases t) (auto simp: Inc_Trees_def)
      have "le_root l r \<and> le_root r l"
        using t by (auto simp: Inc_Trees_def Inc_Trees'_def t_eq)
      hence "A = {x}"
        by (use t in \<open>force simp: Inc_Trees_def Inc_Trees'_def le_root_def t_eq split: tree.splits\<close>)
      with assms show False
        by simp
    qed
    thus "Inc_Trees A \<inter> Inc_Trees' A = {}"
      by blast
  qed auto
  also have "card (Inc_Trees' A) = card (Inc_Trees A)"
    by simp
  also have "\<dots> + \<dots> = 2 * \<dots>"
    by simp
  finally show ?thesis .
qed

text \<open>
  By induction, our main result follows:
\<close>
theorem card_Inc_Trees:
  assumes "finite A"
  shows   "card (Inc_Trees A) = zigzag_number (card A)"
  using assms
proof (induction rule: finite_psubset_induct)
  case (psubset A)
  show ?case
  proof (cases "card A < 2")
    case False
    have "card A > 1"
      using False by (simp add: card_gt_0_iff)
    have "A \<noteq> {}"
      using False by auto
    define x where "x = Min A"
    have "x \<in> A"
      unfolding x_def by (intro Min_in) fact+
    have "2 * card (Inc_Trees A) =
             (\<Sum>X\<in>Pow (A - {x}). card (Inc_Trees X) * card (Inc_Trees (A - X - {x})))"
      unfolding x_def by (rule card_Inc_Trees_rec) fact+
    also have "\<dots> = (\<Sum>X\<in>Pow (A - {x}). zigzag_number (card X) * zigzag_number (card A - card X - 1))"
    proof (intro sum.cong, goal_cases)
      case (2 X)
      have "finite X"
        by (rule finite_subset[of _ A]) (use 2 \<open>finite A\<close> in auto)
      have "card (Inc_Trees X) * card (Inc_Trees (A - X - {x})) =
            zigzag_number (card X) * zigzag_number (card (A - X - {x}))"
        by (intro arg_cong2[of _ _ _ _ "(*)"] psubset.IH)
           (use 2 \<open>x \<in> A\<close> in auto)
      also have "card (A - X - {x}) = card (A - X) - 1"
        by (subst card_Diff_subset) (use 2 \<open>x \<in> A\<close> in auto)
      also have "card (A - X) = card A - card X"
        by (subst card_Diff_subset) (use 2 psubset.hyps \<open>finite X\<close> in auto)
      finally show ?case .
    qed auto
    also have "\<dots> = (\<Sum>X\<in>(\<Union>k\<le>card (A - {x}). {X. X \<subseteq> A - {x} \<and> card X = k}).
                      zigzag_number (card X) * zigzag_number (card A - card X - 1))"
      by (subst Pow_conv_subsets_of_size) (use psubset.hyps in simp_all)
    also have "\<dots> = (\<Sum>k\<le>card (A - {x}). card {X. X \<subseteq> A-{x} \<and> card X = k} * 
                      (zigzag_number k * zigzag_number (card A - k - 1)))"
      by (subst sum.UNION_disjoint) (use finite_subset[OF _ \<open>finite A\<close>] in auto)
    also have "\<dots> = (\<Sum>k\<le>card (A - {x}). (card (A-{x}) choose k) * 
                      (zigzag_number k * zigzag_number (card A - k - 1)))"
      by (intro sum.cong refl, subst n_subsets) (use \<open>finite A\<close> in auto)
    also have "card (A - {x}) = card A - 1"
      by (subst card_Diff_subset) (use \<open>x \<in> A\<close> \<open>finite A\<close> in auto)
    also have "(\<Sum>k\<le>card A - 1. (card A - 1 choose k) * (zigzag_number k * zigzag_number (card A - k - 1))) =
               2 * zigzag_number (card A)"
      using zigzag_number_Suc[of "card A - 1"] \<open>card A > 1\<close> by simp
    finally show ?thesis
      by simp
  next
    case True
    hence "card A = 0 \<or> card A = 1"
      by auto
    then consider "A = {}" | x where "A = {x}"
      using card_1_singletonE[of A] \<open>finite A\<close> by auto
    thus ?thesis
      by cases simp_all
  qed
qed

end