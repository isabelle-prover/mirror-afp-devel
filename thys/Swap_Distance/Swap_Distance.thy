section \<open>The swap distance\<close>
theory Swap_Distance
  imports "Rankings.Rankings" "List_Inversions.List_Inversions"
begin

text \<open>
  The swap distance (also known as the Kendall tau distance) of two finite linear orders $R$, $S$ 
  is the number of pairs $(x,y)$ such that $(x,y)\in R$ and $(y,x)\in S$.

  By using the obvious correspondence between finite linear orders and lists of fixed length,
  the notion is transferred to lists. In this case, an alternative interpretation of the swap
  distance is as the smallest number of swaps of adjacent elements one can perform in order 
  to make one list match the other one.

  The swap distance is strongly related to the number of inversions of a list of linearly-ordered
  elements: if we rename the elements from $1$ to $n$ such that the first list becomes
  $[1,\ldots,n]$, the swap distance is exactly the number of inversions in the second list.

  This correspondence can be used to compute the swap distance in $O(n\log n)$ time using the 
  merge sort inversion count algorithm (which is available in the AFP).
\<close>

subsection \<open>Preliminaries\<close>

(* TODO Move *)
(* tail-recursive code *)
primrec find_index_aux :: "nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index_aux acc P [] = acc"
| "find_index_aux acc P (x # xs) = (if P x then acc else find_index_aux (acc+1) P xs)"

lemma find_index_aux_correct: "find_index_aux acc P xs = find_index P xs + acc"
  by (induction xs arbitrary: acc) simp_all

lemma find_index_aux_code [code]: "find_index P xs = find_index_aux 0 P xs"
  by (simp add: find_index_aux_correct)


(* TODO Move *)
lemma inversions_map:
  fixes xs :: "'a :: linorder list"
  assumes "strict_mono_on (set xs) f"
  shows   "inversions (map f xs) = inversions xs"
proof -
  have f_less_iff: "f x < f y \<longleftrightarrow> x < y" if "x \<in> set xs" "y \<in> set xs" for x y
    using strict_mono_onD[OF assms, of x y] strict_mono_onD[OF assms, of y x] that
    by (metis not_less_iff_gr_or_eq order_less_imp_not_less)
  show ?thesis
    unfolding inversions_altdef by (auto simp: f_less_iff)
qed

lemma inversion_number_map:
  fixes xs :: "'a :: linorder list"
  assumes "strict_mono_on (set xs) f"
  shows   "inversion_number (map f xs) = inversion_number xs"
  using inversions_map[OF assms] by (simp add: inversion_number_def)

lemma inversion_number_Cons:
  "inversion_number (x # xs) = length (filter (\<lambda>y. y < x) xs) + inversion_number xs"
proof -
  have "inversion_number (x # xs) = inversion_number ([x] @ xs)"
    by simp
  also have "\<dots> = inversion_number xs + inversion_number_between [x] xs"
    by (subst inversion_number_append) simp_all
  also have "inversion_number_between [x] xs = 
               card {(i, j). i = 0 \<and> j < length xs \<and> xs ! j < [x] ! i}"
    by (simp add: inversion_number_between_def inversions_between_def)
  also have "{(i, j). i = 0 \<and> j < length xs \<and> xs ! j < [x] ! i} =
             (\<lambda>j. (0, j)) ` {j. j < length xs \<and> xs ! j < x}"
    by auto
  also have "card \<dots> = card {j. j < length xs \<and> xs ! j < x}"
    by (rule card_image) (auto simp: inj_on_def)
  also have "\<dots> = length (filter (\<lambda>y. y < x) xs)"
    by (subst length_filter_conv_card) auto
  finally show ?thesis
    by simp
qed


(* tail-recursive code *)
fun (in preorder) inversion_number_between_sorted_aux :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "inversion_number_between_sorted_aux acc [] ys = acc"
| "inversion_number_between_sorted_aux acc xs [] = acc"
| "inversion_number_between_sorted_aux acc (x # xs) (y # ys) =
             (if \<not>less y x then
                inversion_number_between_sorted_aux acc xs (y # ys)
              else
                inversion_number_between_sorted_aux (acc + length (x # xs)) (x # xs) ys)"

lemma inversion_number_between_sorted_aux_correct:
  "inversion_number_between_sorted_aux acc xs ys = acc + inversion_number_between_sorted xs ys"
  by (induction acc xs ys rule: inversion_number_between_sorted_aux.induct) simp_all

lemma inversion_number_between_sorted_code [code]:
  "inversion_number_between_sorted xs ys = inversion_number_between_sorted_aux 0 xs ys"
  by (simp add: inversion_number_between_sorted_aux_correct)


subsection \<open>The swap distance of two linear orders\<close>

text \<open>
  We first define the set of ``discrepancies'' between the two orders.
\<close>
definition swap_dist_relation_aux :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set" where
  "swap_dist_relation_aux R1 R2 = {(x,y). R1 x y \<and> \<not>R1 y x \<and> R2 y x \<and> \<not>R2 x y}"

text \<open>
  On a linear order, the following simpler definition holds.
\<close>
lemma swap_dist_relation_aux_def_linorder:
  assumes "linorder_on A R1" "linorder_on A R2"
  shows   "swap_dist_relation_aux R1 R2 = {(x,y). R1 x y \<and> \<not>R2 x y}"
proof -
  interpret R1: linorder_on A R1 by fact
  interpret R2: linorder_on A R2 by fact
  show ?thesis unfolding swap_dist_relation_aux_def
    using R1.antisymmetric R1.total R2.antisymmetric R2.total
          R1.refl R2.refl R1.not_outside R2.not_outside by metis
qed

lemma swap_dist_relation_aux_same [simp]: "swap_dist_relation_aux R R = {}"
  by (auto simp: swap_dist_relation_aux_def)

lemma swap_dist_relation_aux_commute: "swap_dist_relation_aux R1 R2 = prod.swap ` swap_dist_relation_aux R2 R1"
  by (auto simp: swap_dist_relation_aux_def)

lemma swap_dist_relation_aux_commute': "bij_betw prod.swap (swap_dist_relation_aux R1 R2) (swap_dist_relation_aux R2 R1)"
  by (rule bij_betwI[of _ _ _ prod.swap]) (auto simp: swap_dist_relation_aux_def)

lemma swap_dist_relation_aux_dual:
  "swap_dist_relation_aux R1 R2 = prod.swap ` swap_dist_relation_aux (\<lambda>x y. R1 y x) (\<lambda>x y. R2 y x)"
  unfolding swap_dist_relation_aux_def by auto

lemma swap_dist_relation_aux_triangle:
  assumes "linorder_on A R1" "linorder_on A R2" "linorder_on A R3"
  shows   "swap_dist_relation_aux R1 R3 \<subseteq> swap_dist_relation_aux R1 R2 \<union> swap_dist_relation_aux R2 R3"
proof -
  interpret R1: linorder_on A R1 by fact
  interpret R2: linorder_on A R2 by fact
  interpret R3: linorder_on A R3 by fact
  show ?thesis
    unfolding swap_dist_relation_aux_def
    using R1.not_outside(1,2) R2.total R2.antisymmetric by fast
qed

lemma finite_swap_dist_relation_aux:
  assumes "linorder_on A R1" "finite A" "linorder_on B R2" "finite B"
  shows   "finite (swap_dist_relation_aux R1 R2)"
proof (rule finite_subset)
  interpret R1: linorder_on A R1 by fact
  interpret R2: linorder_on B R2 by fact
  show "swap_dist_relation_aux R1 R2 \<subseteq> A \<times> B"
    using R1.not_outside R2.not_outside unfolding swap_dist_relation_aux_def by blast
qed (use assms in auto)

lemma split_Bex_pair_iff: "(\<exists>z\<in>A. P z) \<longleftrightarrow> (\<exists>x y. (x, y) \<in> A \<and> P (x, y))"
  by auto

lemma swap_dist_relation_aux_comap_relation:
  assumes "inj_on f A" "linorder_on A R" "linorder_on A S"
  shows   "swap_dist_relation_aux (comap_relation f R) (comap_relation f S) = map_prod f f ` swap_dist_relation_aux R S"
    (is "?lhs = ?rhs")
proof -
  interpret R: linorder_on A R by fact
  interpret S: linorder_on A S by fact
  have "(x, y) \<in> ?lhs \<longleftrightarrow> (x, y) \<in> ?rhs" for x y
    unfolding swap_dist_relation_aux_def comap_relation_def map_prod_def image_iff case_prod_unfold 
              split_Bex_pair_iff mem_Collect_eq fst_conv snd_conv prod.inject
    using inj_onD[OF assms(1)] R.not_outside S.not_outside by smt
  thus ?thesis
    by force
qed

lemma swap_dist_relation_aux_restrict_subset:
  "swap_dist_relation_aux (restrict_relation A R) (restrict_relation A S) \<subseteq> 
   swap_dist_relation_aux R S"
  unfolding swap_dist_relation_aux_def restrict_relation_def by blast


text \<open>
  The swap distance is then simply the number of such discrepancies.
\<close>
definition swap_dist_relation :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat" where
  "swap_dist_relation R1 R2 = card (swap_dist_relation_aux R1 R2)"

lemma swap_dist_relation_same [simp]: "swap_dist_relation R R = 0"
  by (simp add: swap_dist_relation_def)

lemma swap_dist_relation_commute: "swap_dist_relation R1 R2 = swap_dist_relation R2 R1"
  using bij_betw_same_card[OF swap_dist_relation_aux_commute'[of R1 R2]]
  by (simp add: swap_dist_relation_def)

lemma swap_dist_relation_dual:
  "swap_dist_relation R1 R2 = swap_dist_relation (\<lambda>x y. R1 y x) (\<lambda>x y. R2 y x)"
  unfolding swap_dist_relation_def 
  by (subst swap_dist_relation_aux_dual, subst card_image) auto

lemma swap_dist_relation_triangle:
  assumes "linorder_on A R1" "linorder_on A R2" "linorder_on A R3" "finite A"
  shows   "swap_dist_relation R1 R3 \<le> swap_dist_relation R1 R2 + swap_dist_relation R2 R3"
proof -
  interpret R1: linorder_on A R1 by fact
  interpret R2: linorder_on A R2 by fact
  interpret R3: linorder_on A R3 by fact

  have "swap_dist_relation R1 R3 = card (swap_dist_relation_aux R1 R3)"
    by (simp add: swap_dist_relation_def)
  also {
    have "swap_dist_relation_aux R1 R3 \<subseteq> swap_dist_relation_aux R1 R2 \<union> swap_dist_relation_aux R2 R3"
      by (rule swap_dist_relation_aux_triangle) fact+
    moreover have "finite (swap_dist_relation_aux R1 R2)" "finite (swap_dist_relation_aux R2 R3)"
      using finite_swap_dist_relation_aux assms by blast+
    ultimately have "card (swap_dist_relation_aux R1 R3) \<le> card (swap_dist_relation_aux R1 R2 \<union> swap_dist_relation_aux R2 R3)"
      by (intro card_mono) auto
  }
  also have "card (swap_dist_relation_aux R1 R2 \<union> swap_dist_relation_aux R2 R3) \<le> 
               card (swap_dist_relation_aux R1 R2) + card (swap_dist_relation_aux R2 R3)"
    by (rule card_Un_le)
  also have "\<dots> = swap_dist_relation R1 R2 + swap_dist_relation R2 R3"
    by (simp add: swap_dist_relation_def)
  finally show ?thesis .
qed

lemma swap_dist_relation_aux_empty_iff:
  assumes "linorder_on A R" "linorder_on A S"
  shows   "swap_dist_relation_aux R S = {} \<longleftrightarrow> R = S"
proof (rule iffI)
  fix x y :: 'a
  assume *: "swap_dist_relation_aux R S = {}"
  interpret R: linorder_on A R by fact
  interpret S: linorder_on A S by fact
  show "R = S"
  proof (intro ext)
    fix x y
    from * have "\<not>R x y \<or> R y x \<or> \<not>S y x \<or> S x y" "\<not>R y x \<or> R x y \<or> \<not>S x y \<or> S y x"
      unfolding swap_dist_relation_aux_def by blast+
    thus "R x y \<longleftrightarrow> S x y"
      using R.total[of x y] S.total[of x y] R.not_outside[of x y] S.not_outside[of x y]
            R.antisymmetric[of x y] S.antisymmetric[of x y]
      by metis
  qed
qed auto
      
lemma swap_dist_relation_eq_0_iff:
  assumes "linorder_on A R" "linorder_on A S" "finite A"
  shows   "swap_dist_relation R S = 0 \<longleftrightarrow> R = S"
  unfolding swap_dist_relation_def
  using swap_dist_relation_aux_empty_iff[OF assms(1,2)] finite_swap_dist_relation_aux[OF assms(1,3,2,3)]
  by (metis card_eq_0_iff)

lemma swap_dist_relation_comap_relation:
  assumes "inj_on f A" "linorder_on A R" "linorder_on A S"
  shows   "swap_dist_relation (comap_relation f R) (comap_relation f S) = swap_dist_relation R S"
proof -
  interpret R: linorder_on A R by fact
  interpret S: linorder_on A S by fact
  have "swap_dist_relation (comap_relation f R) (comap_relation f S) = card (map_prod f f ` swap_dist_relation_aux R S)"
    using assms by (simp add: swap_dist_relation_def swap_dist_relation_aux_comap_relation)
  also have "\<dots> = swap_dist_relation R S"
    unfolding swap_dist_relation_def
  proof (rule card_image)
    show "inj_on (map_prod f f) (swap_dist_relation_aux R S)"
    proof (rule inj_on_subset)
      show "inj_on (map_prod f f) (A \<times> A)"
        using assms(1) by (auto simp: inj_on_def)
      show "swap_dist_relation_aux R S \<subseteq> A \<times> A"
        unfolding swap_dist_relation_aux_def using R.not_outside S.not_outside by blast
    qed
  qed
  finally show ?thesis .
qed


lemma swap_dist_relation_le:
  assumes "preorder_on A R1" "preorder_on A R2" "finite A"
  shows   "swap_dist_relation R1 R2 \<le> (card A) choose 2"
proof -
  interpret R1: preorder_on A R1 by fact
  interpret R2: preorder_on A R2 by fact
  have "swap_dist_relation R1 R2 = card (swap_dist_relation_aux R1 R2)"
    by (simp add: swap_dist_relation_def)
  also have "card (swap_dist_relation_aux R1 R2) = 
               card ((\<lambda>(x,y). {x,y}) ` swap_dist_relation_aux R1 R2)"
    by (rule card_image [symmetric])
       (auto simp: inj_on_def swap_dist_relation_aux_def doubleton_eq_iff)
  also have "\<dots> \<le> card {X. X \<subseteq> A \<and> card X = 2}"
    by (rule card_mono)
       (use \<open>finite A\<close> R1.not_outside R2.not_outside
        in  \<open>auto simp: swap_dist_relation_aux_def card_insert_if\<close>)
  also have "\<dots> = (card A) choose 2"
    by (rule n_subsets) fact
  finally show ?thesis .
qed

text \<open>
  The swap distance reaches its maximum of $n(n-1)/2$ if and only if the two orders are inverse
  to each other.
\<close>
lemma swap_dist_relation_inverse:
  assumes "linorder_on A R" "finite A"
  shows   "swap_dist_relation R (\<lambda>x y. R y x) = (card A) choose 2"
proof -
  interpret R: linorder_on A R by fact
  have "card (swap_dist_relation_aux R (\<lambda>x y. R y x)) =
        card ((\<lambda>(x, y). {x, y}) ` swap_dist_relation_aux R (\<lambda>x y. R y x))"
    by (subst card_image) (auto simp: inj_on_def doubleton_eq_iff swap_dist_relation_aux_def)
  also have "(\<lambda>(x, y). {x, y}) ` swap_dist_relation_aux R (\<lambda>x y. R y x) = 
             {X. X \<subseteq> A \<and> card X = 2}"
    using R.total R.not_outside R.antisymmetric
    by (fastforce simp: swap_dist_relation_aux_def card_insert_if image_iff card_2_iff doubleton_eq_iff)
  also have "card \<dots> = (card A) choose 2"
    by (rule n_subsets) fact
  finally show ?thesis
    by (simp add: swap_dist_relation_def)
qed

lemma swap_dist_relation_maximal_imp_inverse:
  assumes "preorder_on A R1" "preorder_on A R2" "finite A"
  assumes "swap_dist_relation R1 R2 \<ge> (card A) choose 2"
  shows   "R2 = (\<lambda>y x. R1 x y)"
proof -
  interpret R1: preorder_on A R1 by fact
  interpret R2: preorder_on A R2 by fact

  have *: "(\<lambda>(x,y). {x,y}) ` swap_dist_relation_aux R1 R2 = {X. X \<subseteq> A \<and> card X = 2}"
  proof (rule card_subset_eq)
    show "finite {X. X \<subseteq> A \<and> card X = 2}"
      using assms(3) by simp
    show "(\<lambda>(x, y). {x, y}) ` swap_dist_relation_aux R1 R2 \<subseteq> {X. X \<subseteq> A \<and> card X = 2}"
      using  R1.not_outside R2.not_outside by (auto simp: swap_dist_relation_aux_def card_insert_if)
    have "card ((\<lambda>(x, y). {x, y}) ` swap_dist_relation_aux R1 R2) = swap_dist_relation R1 R2"
      unfolding swap_dist_relation_def
      by (rule card_image) (auto simp: inj_on_def swap_dist_relation_aux_def doubleton_eq_iff)
    also have "\<dots> = (card A) choose 2"
      using swap_dist_relation_le[OF assms(1-3)] assms(4) by linarith
    also have "\<dots> = card {X. X \<subseteq> A \<and> card X = 2}"
      by (rule n_subsets [symmetric]) fact
    finally show "card ((\<lambda>(x, y). {x, y}) ` swap_dist_relation_aux R1 R2) =
                    card {X. X \<subseteq> A \<and> card X = 2}" .
  qed

  show ?thesis
  proof (intro ext)
    fix x y :: 'a
    show "R2 y x \<longleftrightarrow> R1 x y"
    proof (cases "x \<in> A \<and> y \<in> A \<and> x \<noteq> y")
      case False
      thus ?thesis
        using R1.refl R2.refl R1.not_outside R2.not_outside by auto
    next
      case True
      hence "{x, y} \<in> {X. X \<subseteq> A \<and> card X = 2}"
        by auto
      also note * [symmetric]
      finally show ?thesis
        using True by (auto simp: swap_dist_relation_aux_def doubleton_eq_iff)
    qed
  qed
qed

lemma swap_dist_relation_maximal_iff_inverse:
  assumes "linorder_on A R1" "linorder_on A R2" "finite A"
  shows   "swap_dist_relation R1 R2 = (card A) choose 2 \<longleftrightarrow> R2 = (\<lambda>y x. R1 x y)"
proof -
  interpret R1: linorder_on A R1 by fact
  interpret R2: linorder_on A R2 by fact
  note preorder = R1.preorder_on_axioms R2.preorder_on_axioms
  show ?thesis
    using swap_dist_relation_inverse[OF assms(1,3)] swap_dist_relation_le[OF preorder(1,2) assms(3)]
          swap_dist_relation_maximal_imp_inverse[OF preorder(1,2) assms(3)]
    by metis
qed


lemma swap_dist_relation_restrict:
  assumes "linorder_on B R" "linorder_on B S" "finite B"
  shows   "swap_dist_relation (restrict_relation A R) (restrict_relation A S) \<le>
             swap_dist_relation R S"
  unfolding swap_dist_relation_def
proof (rule card_mono)
  interpret R: linorder_on B R by fact
  interpret S: linorder_on B S by fact
  show "finite (swap_dist_relation_aux R S)"
    by (rule finite_subset[of _ "B \<times> B"]) 
       (use \<open>finite B\<close> R.not_outside S.not_outside in \<open>auto simp: swap_dist_relation_aux_def\<close>)
qed (use swap_dist_relation_aux_restrict_subset[of A R S] in auto)

text \<open>
  If the restriction of two relations to some set $A$ has the same swap distance as the 
  full relations, the two relations must agree everywhere except inside $A$.
\<close>
lemma swap_dist_relation_restrict_eq_imp_eq:
  fixes R S A B
  assumes "linorder_on A R" "linorder_on A S" "finite A"
  defines "R' \<equiv> restrict_relation B R"
  defines "S' \<equiv> restrict_relation B S"
  assumes "swap_dist_relation R' S' \<ge> swap_dist_relation R S"
  assumes xy: "x \<notin> B \<or> y \<notin> B"
  shows   "R x y \<longleftrightarrow> S x y"
proof -
  have "swap_dist_relation_aux R' S' = swap_dist_relation_aux R S"
  proof (rule card_subset_eq)
    show "finite (swap_dist_relation_aux R S)"
      by (rule finite_swap_dist_relation_aux[OF assms(1,3,2,3)])
    show "swap_dist_relation_aux R' S' \<subseteq> swap_dist_relation_aux R S"
      unfolding R'_def S'_def by (rule swap_dist_relation_aux_restrict_subset)
    have "swap_dist_relation R' S' \<le> swap_dist_relation R S"
      unfolding R'_def S'_def by (rule swap_dist_relation_restrict[OF assms(1,2,3)])
    with assms have "swap_dist_relation R' S' = swap_dist_relation R S"
      by linarith
    thus "card (swap_dist_relation_aux R' S') = card (swap_dist_relation_aux R S)"
      by (simp add: swap_dist_relation_def)
  qed
  hence *: "(a, b) \<in> swap_dist_relation_aux R' S' \<longleftrightarrow> (a, b) \<in> swap_dist_relation_aux R S" for a b
    by force
  interpret R: linorder_on A R by fact
  interpret S: linorder_on A S by fact
  show ?thesis 
    using xy *[of x y] *[of y x] R.not_outside[of x y] S.not_outside[of x y] 
          R.total[of x y] S.total[of x y] R.antisymmetric[of x y] S.antisymmetric[of x y]
    unfolding swap_dist_relation_aux_def R'_def S'_def restrict_relation_def mem_Collect_eq prod.case
    by metis
qed


subsection \<open>The swap distance of two lists\<close>

text \<open>
  The swap distance of two lists is defined as the swap distance of the relations they correspond
  to when interpreting them as rankings of ``biggest'' to ``smallest''.
\<close>
definition swap_dist :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "swap_dist xs ys =
     (if distinct xs \<and> distinct ys \<and> set xs = set ys
      then swap_dist_relation (of_ranking xs) (of_ranking ys) else 0)"

lemma swap_dist_le: "swap_dist xs ys \<le> (length xs) choose 2"
proof (cases "set xs = set ys \<and> distinct xs \<and> distinct ys")
  case True
  hence "length xs = length ys"
    using distinct_card by metis
  interpret xs: linorder_on "set xs" "of_ranking xs"
    by (rule linorder_of_ranking) (use True in auto)
  interpret ys: linorder_on "set xs" "of_ranking ys"
    by (rule linorder_of_ranking) (use True in auto)
  show ?thesis
    using swap_dist_relation_le[OF xs.preorder_on_axioms ys.preorder_on_axioms] True
          \<open>length xs = length ys\<close> by (auto simp: swap_dist_def distinct_card)
qed (auto simp: swap_dist_def)

lemma swap_dist_same [simp]: "swap_dist xs xs = 0"
  by (auto simp: swap_dist_def)

lemma swap_dist_commute: "swap_dist xs ys = swap_dist ys xs"
  by (simp add: swap_dist_def swap_dist_relation_commute)

lemma swap_dist_rev [simp]: "swap_dist (rev xs) (rev ys) = swap_dist xs ys"
proof (cases "distinct xs \<and> distinct ys \<and> set xs = set ys")
  case True
  show ?thesis
    using True swap_dist_relation_dual[of "of_ranking xs" "of_ranking ys"]
    by (simp add: of_ranking_rev[abs_def] swap_dist_def)
qed (auto simp: swap_dist_def)

lemma swap_dist_rev_left: "swap_dist (rev xs) ys = swap_dist xs (rev ys)"
  using swap_dist_rev by (metis rev_rev_ident)

lemma swap_dist_triangle:
  assumes "set xs = set ys" "distinct ys"
  shows "swap_dist xs zs \<le> swap_dist xs ys + swap_dist ys zs"
  using swap_dist_relation_triangle[of "set xs" "of_ranking xs" "of_ranking ys" "of_ranking zs"] assms
  unfolding swap_dist_def by (simp add: linorder_of_ranking)

lemma swap_dist_eq_0_iff:
  assumes "distinct xs" "distinct ys" "set xs = set ys"
  shows   "swap_dist xs ys = 0 \<longleftrightarrow> xs = ys"
proof -
  have "swap_dist xs ys = 0 \<longleftrightarrow> swap_dist_relation (of_ranking xs) (of_ranking ys) = 0"
    using assms by (auto simp: swap_dist_def)
  also have "\<dots> \<longleftrightarrow> xs = ys"
    using assms by (metis List.finite_set linorder_of_ranking ranking_of_ranking swap_dist_relation_eq_0_iff)
  finally show ?thesis .
qed

lemma swap_dist_pos_iff:
  assumes "distinct xs" "distinct ys" "set xs = set ys"
  shows   "swap_dist xs ys > 0 \<longleftrightarrow> xs \<noteq> ys"
  using swap_dist_eq_0_iff[OF assms] by linarith

lemma swap_dist_map:
  assumes "inj_on f (set xs \<union> set ys)"
  shows   "swap_dist (map f xs) (map f ys) = swap_dist xs ys"
proof (cases "set xs = set ys \<and> distinct xs \<and> distinct ys")
  case True
  define A where "A = set xs"
  have inj: "inj_on f A"
    using assms True unfolding A_def by simp
  have linorder: "linorder_on A (of_ranking xs)" "linorder_on A (of_ranking ys)"
    unfolding A_def using True by (simp_all add: linorder_of_ranking)
  have "swap_dist (map f xs) (map f ys) = 
          swap_dist_relation (comap_relation f (of_ranking xs)) (comap_relation f (of_ranking ys))"
    by (use inj True in \<open>auto simp: swap_dist_def distinct_map of_ranking_map A_def\<close>)
  also have "\<dots> = swap_dist xs ys"
    by (subst swap_dist_relation_comap_relation[OF inj linorder])
       (use True in \<open>auto simp: swap_dist_def\<close>)
  finally show ?thesis .
next
  case False
  have inj: "inj_on f (set xs)" "inj_on f (set ys)"
    by (rule inj_on_subset[OF assms(1)]; simp; fail)+
  show ?thesis using inj False inj_on_Un_image_eq_iff[OF assms]
    by (auto simp: swap_dist_def distinct_map)
qed


text \<open>
  The swap distance reaches its maximum of $n(n-1)/2$ iff the two lists are reverses of
  one another.
\<close>
lemma swap_dist_rev_same:
  assumes "distinct xs"
  shows   "swap_dist xs (rev xs) = (length xs) choose 2"
proof -
  have "swap_dist xs (rev xs) = swap_dist_relation (of_ranking xs) (\<lambda>x y. of_ranking xs y x)"
    using assms by (simp add: swap_dist_def of_ranking_rev [abs_def])
  also have "\<dots> = (length xs) choose 2"
    by (subst swap_dist_relation_inverse[where A = "set xs"])
       (use assms in \<open>simp_all add: linorder_of_ranking distinct_card\<close>)
  finally show ?thesis .
qed

lemma swap_dist_maximalD:
  assumes "set xs = set ys" "distinct xs" "distinct ys"
  assumes "swap_dist xs ys \<ge> (length xs) choose 2"
  shows   "ys = rev xs"
proof -
  interpret xs: linorder_on "set xs" "of_ranking xs"
    by (rule linorder_of_ranking) (use assms in auto)
  interpret ys: linorder_on "set xs" "of_ranking ys"
    by (rule linorder_of_ranking) (use assms in auto)
  have "length xs = length ys"
    using assms by (metis distinct_card)
  have "of_ranking ys = (\<lambda>x y. of_ranking xs y x)"
    using assms \<open>length xs = length ys\<close>
    by (intro swap_dist_relation_maximal_imp_inverse[where A = "set xs"])
       (use xs.preorder_on_axioms ys.preorder_on_axioms in \<open>simp_all add: swap_dist_def distinct_card\<close>)
  also have "\<dots> = of_ranking (rev xs)"
    by (simp add: fun_eq_iff)
  finally have "ranking (of_ranking ys) = ranking (of_ranking (rev xs))"
    by (rule arg_cong)
  thus ?thesis
    using assms by (subst (asm) (1 2) ranking_of_ranking) auto
qed

lemma swap_dist_maximal_iff:
  assumes "set xs = set ys" "distinct xs" "distinct ys"
  shows   "swap_dist xs ys = (length xs) choose 2 \<longleftrightarrow> ys = rev xs"
  using assms swap_dist_maximalD[OF assms] swap_dist_le[of xs ys] swap_dist_rev_same by metis


lemma swap_dist_append_left:
  assumes "distinct zs"
  assumes "set zs \<inter> set xs = {}" "set zs \<inter> set ys = {}"
  shows   "swap_dist (zs @ xs) (zs @ ys) = swap_dist xs ys"
proof (cases "distinct xs \<and> distinct ys \<and> set xs = set ys")
  case False
  thus ?thesis using assms
    by (auto simp: swap_dist_def)
next
  case True
  have "swap_dist_relation_aux (of_ranking (zs @ xs)) (of_ranking (zs @ ys)) = 
        swap_dist_relation_aux (of_ranking xs) (of_ranking ys)"
    unfolding swap_dist_relation_aux_def of_ranking_append
    using assms True of_ranking_imp_in_set[of xs] of_ranking_imp_in_set[of zs]
    by blast
  thus ?thesis
    using True assms by (simp add: swap_dist_def swap_dist_relation_def)
qed

lemma swap_dist_append_right:
  assumes "distinct zs"
  assumes "set zs \<inter> set xs = {}" "set zs \<inter> set ys = {}"
  shows   "swap_dist (xs @ zs) (ys @ zs) = swap_dist xs ys"
proof (cases "distinct xs \<and> distinct ys \<and> set xs = set ys")
  case False
  thus ?thesis using assms
    by (auto simp add: swap_dist_def Int_commute)
next
  case True
  have "swap_dist_relation_aux (of_ranking (xs @ zs)) (of_ranking (ys @ zs)) = 
        swap_dist_relation_aux (of_ranking xs) (of_ranking ys)"
    unfolding swap_dist_relation_aux_def of_ranking_append
    using assms True of_ranking_imp_in_set[of xs] of_ranking_imp_in_set[of zs]
    by blast
  thus ?thesis
    using True assms by (simp add: swap_dist_def swap_dist_relation_def Int_commute)
qed

lemma swap_dist_Cons_same:
  assumes "z \<notin> set xs \<union> set ys"
  shows   "swap_dist (z # xs) (z # ys) = swap_dist xs ys"
  using swap_dist_append_left[of "[z]" xs ys] assms by simp

lemma swap_dist_swap_first:
  assumes "distinct (x # y # xs)"
  shows   "swap_dist (x # y # xs) (y # x # xs) = 1"
proof -
  have "swap_dist (x # y # xs) (y # x # xs) = 
          card (swap_dist_relation_aux (of_ranking (x # y # xs)) (of_ranking (y # x # xs)))"
    using assms by (simp add: swap_dist_def swap_dist_relation_def insert_commute)
  also have "swap_dist_relation_aux (of_ranking (x # y # xs)) (of_ranking (y # x # xs)) = {(y,x)}"
    using assms of_ranking_imp_in_set[of xs] by (auto simp: swap_dist_relation_aux_def of_ranking_Cons)
  finally show ?thesis
    by simp
qed


subsection \<open>The relationship between swap distance and inversions\<close>

text \<open>
  The swap distance between a list \<open>xs\<close> containing the numbers $0, \ldots, n-1$ and the list
  $[0, \ldots, n-1]$ is exactly the number of inversions of \<open>xs\<close>.
\<close>
lemma swap_dist_zero_upt_n:
  assumes "mset xs = mset_set {0..<n}"
  shows   "swap_dist [0..<n] xs = inversion_number xs"
proof -
  define A where "A = {xy\<in>{..<n}\<times>{..<n}. fst xy > snd xy \<and> snd xy \<prec>[of_ranking xs] fst xy}"
  define B where "B = {ij\<in>{..<n}\<times>{..<n}. fst ij < snd ij \<and> xs ! fst ij > xs ! snd ij}"
  define f where "f = (\<lambda>i. xs ! i)"

  have distinct: "distinct xs"
    using assms by (metis finite_atLeastLessThan mset_eq_mset_set_imp_distinct)
  have set_xs: "set xs = {0..<n}"
    using assms by (metis mset_eq_setD mset_upt set_upt)
  have length_xs: "length xs = n"
    using assms by (metis diff_zero length_upt mset_eq_length mset_upt)
  have "swap_dist ([0..<n]) xs = swap_dist_relation (of_ranking ([0..<n])) (of_ranking xs)"
    unfolding swap_dist_def using distinct set_xs by simp
  also have "\<dots> = card (swap_dist_relation_aux (of_ranking ([0..<n])) (of_ranking xs))"
    unfolding swap_dist_relation_def ..
  also have "swap_dist_relation_aux (of_ranking ([0..<n])) (of_ranking xs) = A"
    unfolding A_def swap_dist_relation_aux_def of_ranking_zero_upt_nat strongly_preferred_def by auto
  finally have "swap_dist ([0..<n]) xs = card A" .

  also have "bij_betw (map_prod f f) B A"
    unfolding inversions_altdef case_prod_unfold A_def B_def
  proof (rule bij_betw_Collect, goal_cases)
    case 1
    have "bij_betw f {..<n} (set xs)"
      unfolding f_def by (rule bij_betw_nth) (use distinct in \<open>simp_all add: length_xs\<close>)
    hence "bij_betw f {..<n} {..<n}"
      by (simp add: set_xs atLeast0LessThan)
    show "bij_betw (map_prod f f) ({..<n} \<times> {..<n}) ({..<n} \<times> {..<n})"
      by (rule bij_betw_map_prod) fact+
  next
    case (2 xy)
    thus ?case
      using distinct
      by (auto simp: strongly_preferred_of_ranking_nth_iff f_def length_xs set_xs)
  qed
  hence "card B = card A"
    by (rule bij_betw_same_card)
  hence "card A = card B" ..
  also have "card B = inversion_number xs"
    unfolding inversion_number_def inversions_altdef B_def
    by (rule arg_cong[of _ _ card]) (auto simp: set_xs length_xs)
  finally show ?thesis .
qed

text \<open>
  Hence, computing the swap distance of two arbitrary lists can be reduced to computing the
  number of inversions of a list by renaming all the elements such that the first list becomes
  $[0, \ldots, n-1]$.
\<close>
lemma swap_dist_conv_inversion_number:
  assumes distinct: "distinct xs" "distinct ys" and set_eq: "set xs = set ys"
  shows   "swap_dist xs ys = inversion_number (map (index xs) ys)"
proof -
  have "length xs = length ys"
    using distinct set_eq by (metis distinct_card)
  define n where "n = length xs"
  have "n = length ys"
    using \<open>length xs = length ys\<close> unfolding n_def by simp

  define f where "f = index xs"
  have inj: "inj_on f (set xs)"
    unfolding f_def using inj_on_index[of xs] by simp

  have "swap_dist xs ys = swap_dist (map f xs) (map f ys)"
    by (rule swap_dist_map [symmetric]) (use set_eq inj in simp_all)
  also have "map f xs = [0..<n]" unfolding f_def n_def
    by (rule map_index_self) fact+
  also have "swap_dist [0..<n] (map f ys) = inversion_number (map f ys)"
  proof (rule swap_dist_zero_upt_n)
    show "mset (map f ys) = mset_set {0..<n}"
      by (metis \<open>map f xs = [0..<n]\<close> distinct(1,2) mset_map mset_set_set mset_upt set_eq)
  qed
  finally show ?thesis
    by (simp add: f_def)
qed

lemma swap_dist_code' [code]:
  "swap_dist xs ys =
     (if distinct xs \<and> distinct ys \<and> set xs = set ys then
        inversion_number (map (index xs) ys) else 0)"
proof (cases "distinct xs \<and> distinct ys \<and> set xs = set ys")
  case False
  thus ?thesis
    by (auto simp: swap_dist_def)
next
  case True
  thus ?thesis
    by (subst swap_dist_conv_inversion_number) auto
qed


subsection \<open>Swapping adjacent list elements\<close>

definition swap_adj_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "swap_adj_list i xs = (if Suc i < length xs then xs[i := xs ! Suc i, Suc i := xs ! i] else xs)"

lemma length_swap_adj_list [simp]: "length (swap_adj_list i xs) = length xs"
  by (simp add: swap_adj_list_def)

lemma distinct_swap_adj_list_iff [simp]:
  "distinct (swap_adj_list i xs) \<longleftrightarrow> distinct xs"
  by (simp add: swap_adj_list_def)

lemma mset_swap_adj_list [simp]:
  "mset (swap_adj_list i xs) = mset xs"
  by (simp add: swap_adj_list_def mset_update)

lemma set_swap_adj_list [simp]:
  "set (swap_adj_list i xs) = set xs"
  by (simp add: swap_adj_list_def)

lemma swap_adj_list_append_left:
  assumes "i \<ge> length xs"
  shows   "swap_adj_list i (xs @ ys) = xs @ swap_adj_list (i - length xs) ys"
  using assms by (auto simp: swap_adj_list_def list_update_append nth_append Suc_diff_le)

lemma swap_adj_list_Cons:
  assumes "i > 0"
  shows   "swap_adj_list i (x # xs) = x # swap_adj_list (i - 1) xs"
  using swap_adj_list_append_left[of "[x]" i xs] assms by simp

lemma swap_adj_list_append_right:
  assumes "Suc i < length xs"
  shows   "swap_adj_list i (xs @ ys) = swap_adj_list i xs @ ys"
  using assms by (auto simp: swap_adj_list_def list_update_append nth_append)

lemma swap_dist_swap_adj_list:
  assumes "Suc i < length xs" "distinct xs"
  shows   "swap_dist xs (swap_adj_list i xs) = 1"
proof -
  define x y where "x = xs ! i" and "y = xs ! Suc i"
  define ys zs where "ys = take i xs" and "zs = drop (i+2) xs"
  have "length ys = i"
    using assms(1) by (simp add: ys_def)
  have 1: "xs = ys @ x # y # zs"
    unfolding x_def y_def ys_def zs_def using assms(1) by (simp add: Cons_nth_drop_Suc)
  have 2: "swap_adj_list i xs = ys @ y # x # zs"
    by (simp add: swap_adj_list_def 1 list_update_append \<open>length ys = i\<close> nth_append)
  have "swap_dist xs (swap_adj_list i xs) =
        swap_dist (ys @ x # y # zs) (ys @ y # x # zs)"
    by (subst 1, subst 2) (rule refl)
  also have "\<dots> = 1"
    using assms by (simp add: 1 swap_dist_swap_first swap_dist_append_left)
  finally show ?thesis .
qed

fun swap_adjs_list :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "swap_adjs_list [] xs = xs"
| "swap_adjs_list (i # is) xs = swap_adjs_list is (swap_adj_list i xs)"

lemma length_swap_adjs_list [simp]: "length (swap_adjs_list is xs) = length xs"
  by (induction "is" arbitrary: xs) simp_all

lemma distinct_swap_adjs_list_iff [simp]:
  "distinct (swap_adjs_list is xs) \<longleftrightarrow> distinct xs"
  by (induction "is" arbitrary: xs) (auto simp: swap_adj_list_def)

lemma mset_swap_adjs_list [simp]:
  "mset (swap_adjs_list is xs) = mset xs"
  by (induction "is" arbitrary: xs) (auto simp: swap_adj_list_def mset_update)

lemma set_swap_adjs_list_list [simp]:
  "set (swap_adjs_list is xs) = set xs"
  by (induction "is" arbitrary: xs) (auto simp: swap_adj_list_def mset_update)

lemma swap_adjs_list_append:
  "swap_adjs_list (is @ js) xs = swap_adjs_list js (swap_adjs_list is xs)"
  by (induction "is" arbitrary: xs) simp_all

lemma swap_adjs_list_append_left:
  assumes "\<forall>i\<in>set is. i \<ge> length xs"
  shows   "swap_adjs_list is (xs @ ys) = xs @ swap_adjs_list (map (\<lambda>i. i - length xs) is) ys"
  using assms by (induction "is" arbitrary: ys) (simp_all add: swap_adj_list_append_left)

lemma swap_adjs_list_Cons:
  assumes "0 \<notin> set is"
  shows   "swap_adjs_list is (x # xs) = x # swap_adjs_list (map (\<lambda>i. i - 1) is) xs"
proof -
  have "\<forall>i\<in>set is. Suc 0 \<le> i"
    using assms by (auto simp: Suc_le_eq intro!: Nat.gr0I)
  thus ?thesis
    using swap_adjs_list_append_left[of "is" "[x]" xs] by simp
qed

lemma swap_adjs_list_append_right:
  assumes "\<forall>i\<in>set is. Suc i < length xs"
  shows   "swap_adjs_list is (xs @ ys) = swap_adjs_list is xs @ ys"
  using assms by (induction "is" arbitrary: xs) (simp_all add: swap_adj_list_append_right)


text \<open>
  Swapping two adjacent elements either increases or decreases the swap distance by 1, depending
  on the orientation of the swapped pair in the other relation.
\<close>
lemma swap_dist_relation_of_ranking_swap:
  assumes "distinct (xs @ x # y # ys)"
  shows   "swap_dist_relation R (of_ranking (xs @ x # y # ys)) + (if y \<prec>[R] x then 1 else 0) =
           swap_dist_relation R (of_ranking (xs @ y # x # ys)) + (if x \<prec>[R] y then 1 else 0)"
proof -
  have "swap_dist_relation_aux R (of_ranking (xs @ x # y # ys)) \<union> (if y \<prec>[R] x then {(y,x)} else {}) =
        swap_dist_relation_aux R (of_ranking (xs @ y # x # ys)) \<union> (if x \<prec>[R] y then {(x,y)} else {})"
    (is "?lhs = ?rhs")
    using assms
    by (auto simp: swap_dist_relation_aux_def of_ranking_append of_ranking_Cons strongly_preferred_def
             dest: of_ranking_imp_in_set) (* takes a few seconds *)
  moreover have "card ?lhs = card (swap_dist_relation_aux R (of_ranking (xs @ x # y # ys))) + (if y \<prec>[R] x then 1 else 0)"
  proof (subst card_Un_disjoint)
    show "finite (swap_dist_relation_aux R (of_ranking (xs @ x # y # ys)))"
    proof (rule finite_subset)
      show "swap_dist_relation_aux R (of_ranking (xs @ x # y # ys)) \<subseteq>
              set (xs @ x # y # ys) \<times> set (xs @ x # y # ys)"
        unfolding swap_dist_relation_aux_def using of_ranking_imp_in_set[of "(xs @ x # y # ys)"]
        by blast
    qed auto
  qed (auto simp: swap_dist_relation_aux_def of_ranking_append of_ranking_Cons)
  moreover have "card ?rhs = card (swap_dist_relation_aux R (of_ranking (xs @ y # x # ys))) + (if x \<prec>[R] y then 1 else 0)"
  proof (subst card_Un_disjoint)
    show "finite (swap_dist_relation_aux R (of_ranking (xs @ y # x # ys)))"
    proof (rule finite_subset)
      show "swap_dist_relation_aux R (of_ranking (xs @ y # x # ys)) \<subseteq>
              set (xs @ y # x # ys) \<times> set (xs @ y # x # ys)"
        unfolding swap_dist_relation_aux_def using of_ranking_imp_in_set[of "(xs @ y # x # ys)"]
        by blast
    qed auto
  qed (auto simp: swap_dist_relation_aux_def of_ranking_append of_ranking_Cons)
  ultimately show ?thesis
    unfolding swap_dist_relation_def by metis
qed


subsection \<open>Swapping non-adjacent list elements\<close>

text \<open>
  If $x$ and $y$ are two not necessarily adjacent elements that are ``in the wrong order'',
  swapping them always strictly decreases the swap distance.
\<close>
lemma swap_dist_relation_swap_less:
  assumes "linorder_on A R" "finite A"
  assumes xy: "R x y"
  assumes distinct: "distinct (xs @ x # ys @ y # zs)"
  assumes subset: "set (xs @ x # ys @ y # zs) = A"
  shows   "swap_dist_relation R (of_ranking (xs @ x # ys @ y # zs)) >
           swap_dist_relation R (of_ranking (xs @ y # ys @ x # zs))"
proof -
  interpret R: linorder_on A R by fact
  from distinct have [simp]: "x \<noteq> y" "y \<noteq> x"
    by auto
  have yx: "\<not>y \<preceq>[R] x"
    using xy R.antisymmetric[of x y] by auto

  define f where "f = (\<lambda>xs. swap_dist_relation_aux R (of_ranking xs))"
  have fin: "finite (f xs)" for xs
    by (rule finite_subset[of _ "set xs \<times> set xs"])
       (auto simp: f_def swap_dist_relation_aux_def dest: of_ranking_imp_in_set)

  have f_eq: "f xs = {(x, y). x \<prec>[R] y \<and> x \<succ>[of_ranking xs] y}" for xs
    unfolding f_def swap_dist_relation_aux_def by (auto simp: strongly_preferred_def)
  have "distinct xs" "distinct ys" "distinct zs"
    using distinct by auto
  hence *: "a \<prec>[of_ranking xs] b \<longleftrightarrow> a \<noteq> b \<and> of_ranking xs a b"
           "a \<prec>[of_ranking ys] b \<longleftrightarrow> a \<noteq> b \<and> of_ranking ys a b"
           "a \<prec>[of_ranking zs] b \<longleftrightarrow> a \<noteq> b \<and> of_ranking zs a b" for a b
    by (metis linorder_of_ranking linorder_on_def order_on.antisymmetric
              strongly_preferred_def)+
  have **: "a \<prec>[R] b \<longleftrightarrow> a \<noteq> b \<and> R a b" for a b
    using R.antisymmetric R.total unfolding strongly_preferred_def by blast

  define lhs where 
    "lhs = f (xs @ x # ys @ y # zs) \<union> ({(y,b) |b. R y b \<and> b \<in> set ys} \<union> {(a,x) |a. R a x \<and> a \<in> set (y#ys)})"
  define rhs where
    "rhs = f (xs @ y # ys @ x # zs) \<union> ({(x,b) |b. R x b \<and> b \<in> set ys} \<union> {(a,y) |a. R a y \<and> a \<in> set (x#ys)})"

  have "lhs = rhs"
  proof -
    have "(a, b) \<in> lhs \<longleftrightarrow> (a, b) \<in> rhs" for a b
    proof -
      have "(a, b) \<in> lhs \<longleftrightarrow> (a, b) \<in> f (xs @ x # ys @ y # zs) \<or> R a b \<and> ((a = y \<and> (b = x \<or> b \<in> set ys)) \<or> (a \<in> set ys \<and> b = x))"
        unfolding lhs_def using subset by auto
      also have "\<dots> \<longleftrightarrow> (a, b) \<in> f (xs @ y # ys @ x # zs) \<or> R a b \<and> ((a = x \<and> (b = y \<or> b \<in> set ys)) \<or> (a \<in> set ys \<and> b = y))"
        using distinct subset unfolding f_eq 
        by (force simp: of_ranking_strongly_preferred_Cons_iff of_ranking_strongly_preferred_append_iff 
                        eq_commute not_strongly_preferred_of_ranking_iff * **)
      also have "\<dots> \<longleftrightarrow> (a, b) \<in> rhs"
        unfolding rhs_def using subset yx by auto
      finally show "(a, b) \<in> lhs \<longleftrightarrow> (a, b) \<in> rhs" .
    qed
    thus ?thesis
      by auto
  qed

  define d1 where "d1 = card {a. R a y \<and> R y a \<and> a \<in> set ys}"
  define d2 where "d2 = card {a. R x a \<and> R a y \<and> a \<in> set ys}"

  have "card lhs = card (f (xs @ x # ys @ y # zs)) +
               card ({(y,b) |b. R y b \<and> b \<in> set ys} \<union> {(a,x) |a. R a x \<and> a \<in> set (y#ys)})"
    unfolding lhs_def
    by (intro card_Un_disjoint fin)
       (auto simp: f_def swap_dist_relation_aux_def of_ranking_Cons of_ranking_append
             dest: of_ranking_imp_in_set)
  also have "card ({(y,b) |b. R y b \<and> b \<in> set ys} \<union> {(a,x) |a. R a x \<and> a \<in> set (y#ys)}) =
             card {(y,b) |b. R y b \<and> b \<in> set ys} + card {(a,x) |a. R a x \<and> a \<in> set (y#ys)}"
    using distinct by (intro card_Un_disjoint) auto
  also have "{(y,b) |b. R y b \<and> b \<in> set ys} = (\<lambda>b. (y,b)) ` {b. R y b \<and> b \<in> set ys}"
    by auto
  also have "card \<dots> = card {b. R y b \<and> b \<in> set ys}"
    by (rule card_image) (auto simp: inj_on_def)
  also have "{(a,x) |a. R a x \<and> a \<in> set (y#ys)} = (\<lambda>a. (a,x)) ` {a. R a x \<and> a \<in> set (y#ys)}"
    by auto
  also have "card \<dots> = card {a. R a x \<and> a \<in> set (y#ys)}"
    by (rule card_image) (auto simp: inj_on_def)
  also have "{a. R a x \<and> a \<in> set (y#ys)} = {a. R a x \<and> a \<in> set ys}"
    using yx by auto
  finally have 1:
    "card lhs = 
       card (f (xs @ x # ys @ y # zs)) + card {a. R a x \<and> a \<in> set ys} + card {b. R y b \<and> b \<in> set ys}" 
    by (simp only: add_ac)

  have "card rhs = card (f (xs @ y # ys @ x # zs)) +
               card ({(x,b) |b. R x b \<and> b \<in> set ys} \<union> {(a,y) |a. R a y \<and> a \<in> set (x#ys)})"
    unfolding rhs_def
    by (intro card_Un_disjoint fin)
       (auto simp: f_def swap_dist_relation_aux_def of_ranking_Cons of_ranking_append
             dest: of_ranking_imp_in_set)
  also have "card ({(x,b) |b. R x b \<and> b \<in> set ys} \<union> {(a,y) |a. R a y \<and> a \<in> set (x#ys)}) =
             card ({(x,b) |b. R x b \<and> b \<in> set ys}) + card ({(a,y) |a. R a y \<and> a \<in> set (x#ys)})"
    using distinct by (intro card_Un_disjoint) auto
  also have "{(x,b) |b. R x b \<and> b \<in> set ys} = (\<lambda>b. (x,b)) ` {b. R x b \<and> b \<in> set ys}"
    by auto
  also have "card \<dots> = card {b. R x b \<and> b \<in> set ys}"
    by (rule card_image) (auto simp: inj_on_def)
  also have "{(a,y) |a. R a y \<and> a \<in> set (x#ys)} = (\<lambda>a. (a,y)) ` {a. R a y \<and> a \<in> set (x#ys)}"
    by auto
  also have "card \<dots> = card {a. R a y \<and> a \<in> set (x#ys)}"
    by (rule card_image) (auto simp: inj_on_def)
  also have "{a. R a y \<and> a \<in> set (x#ys)} = {a. R a y \<and> a \<in> set ys} \<union> {x}"
    using xy by auto
  also have "card \<dots> = card {a. R a y \<and> a \<in> set ys} + 1"
    using distinct by (subst card_Un_disjoint) auto

  finally have 2:
    "card rhs = 
       card (f (xs @ y # ys @ x # zs)) + card {a. R a y \<and> a \<in> set ys} + card {b. R x b \<and> b \<in> set ys} + 1" 
    by (simp only: add_ac)

  have 3: "card {a. R a x \<and> a \<in> set ys} \<le> card {a. R a y \<and> a \<in> set ys}"
    by (rule card_mono) (use xy R.trans in auto)
  have 4: "card {b. R y b \<and> b \<in> set ys} \<le> card {b. R x b \<and> b \<in> set ys}"
    by (rule card_mono) (use xy R.trans in auto)

  have "int (card lhs) = int (card rhs)"
    using \<open>lhs = rhs\<close> by (rule arg_cong)
  hence "int (card lhs) - card {a. R a x \<and> a \<in> set ys} - card {b. R y b \<and> b \<in> set ys} \<ge> 
         int (card rhs) - card {a. R a y \<and> a \<in> set ys} - card {b. R x b \<and> b \<in> set ys}"
    using 3 4 by linarith
  hence "card (f (xs @ x # ys @ y # zs)) > card (f (xs @ y # ys @ x # zs))"
    unfolding 1 2 by simp
  thus ?thesis
    unfolding f_def swap_dist_relation_def by simp
qed

lemma swap_dist_relation_swap_less':
  assumes xy: "R (ys ! i) (ys ! j) \<longleftrightarrow> i < j"
  assumes R: "finite_linorder_on A R"
  assumes distinct: "distinct ys" "set ys = A"
  assumes ij: "i < length ys" "j < length ys" "i \<noteq> j"
  shows   "swap_dist_relation R (of_ranking ys) > 
           swap_dist_relation R (of_ranking (ys[i := ys ! j, j := ys ! i]))"
  using ij xy
proof (induction i j rule: linorder_wlog)
  case (le i j)
  hence "i < j"
    by linarith
  interpret R: finite_linorder_on A R
    by fact
  define ys1 ys2 ys3 where "ys1 = take i ys" 
    and "ys2 = take (j - i - 1) (drop (i+1) ys)" and "ys3 = drop (j+1) ys"
  have [simp]: "length ys1 = i" "length ys2 = j - i - 1" "length ys3 = length ys - j - 1"
    using le by (simp_all add: ys1_def ys2_def ys3_def)
  define y y' where "y = ys ! i" and "y' = ys ! j"

  have ys_eq: "ys = ys1 @ y # ys2 @ y' # ys3"
    apply (subst id_take_nth_drop[of i])
    subgoal by (use le in simp)
    apply (subst id_take_nth_drop[of "j - i - 1" "drop (Suc i) ys"])
     apply (use le in \<open>simp_all add: ys1_def ys2_def ys3_def y_def y'_def\<close>)
    done

  have "swap_dist_relation R (of_ranking (ys1 @ y # ys2 @ y' # ys3)) >
        swap_dist_relation R (of_ranking (ys1 @ y' # ys2 @ y # ys3))"
  proof (rule swap_dist_relation_swap_less)
    show "linorder_on A R" ..
    show "R y y'"
      unfolding y_def y'_def using le by auto
    show "distinct (ys1 @ y # ys2 @ y' # ys3)"
      using distinct unfolding ys_eq by simp
    show "set (ys1 @ y # ys2 @ y' # ys3) = A"
      using distinct unfolding ys_eq by simp
  qed auto
  also have "ys1 @ y # ys2 @ y' # ys3 = ys"
    using ys_eq by simp
  also have "ys1 @ y' # ys2 @ y # ys3 = ys[i := y', j := y]"
    by (subst ys_eq) (use le \<open>i < j\<close> in \<open>auto simp: list_update_append split: nat.splits\<close>)
  finally show ?case
    unfolding swap_dist_def y_def y'_def using distinct by simp
next
  case (sym i j)
  interpret R: finite_linorder_on A R
    by fact
  have "swap_dist_relation R (of_ranking (ys[j := ys ! i, i := ys ! j])) < 
        swap_dist_relation R (of_ranking ys)"
  proof (rule sym.IH)
    show "R (ys ! j) (ys ! i) \<longleftrightarrow> (j < i)"
      using sym.prems distinct R.antisymmetric R.total'
      by (metis less_imp_le_nat linorder_not_le nat_neq_iff nth_eq_iff_index_eq nth_mem)
  qed (use sym.prems in auto)
  thus ?case
    using sym.prems by (simp add: list_update_swap)
qed

text \<open>
  The following formulation for lists is probably the nicest one.
\<close>
lemma swap_dist_swap_less:
  assumes xy: "of_ranking xs (ys ! i) (ys ! j) \<longleftrightarrow> i < j"
  assumes distinct: "distinct xs" "distinct ys" "set xs = set ys"
  assumes ij: "i < length ys" "j < length ys" "i \<noteq> j"
  shows   "swap_dist xs ys > swap_dist xs (ys[i := ys ! j, j := ys ! i])"
proof -
  have "swap_dist_relation (of_ranking xs) (of_ranking ys) > 
        swap_dist_relation (of_ranking xs) (of_ranking (ys[i := ys ! j, j := ys ! i]))"
    by (rule swap_dist_relation_swap_less'[where A = "set xs"])
       (use assms in \<open>auto intro: finite_linorder_of_ranking\<close>)
  thus ?thesis
    using distinct by (simp add: swap_dist_def)
qed


subsection \<open>Swap distance as minimal number of adjacent swaps to make two lists equal\<close>

text \<open>
  The swap distance between the original list and the list obtained after swapping adjacent
  elements $n$ times is at most $n$.
\<close>
lemma swap_dist_swap_adjs_list:
  assumes "distinct xs"
  shows   "swap_dist xs (swap_adjs_list is xs) \<le> length is"
  using assms
proof (induction "is" arbitrary: xs)
  case (Cons i "is" xs)
  define ys where "ys = swap_adj_list i xs"
  have "swap_dist xs (swap_adjs_list (i#is) xs) =
          swap_dist xs (swap_adjs_list is ys)"
    by (simp add: ys_def)
  also have "\<dots> \<le> swap_dist xs ys + swap_dist ys (swap_adjs_list is ys)"
    by (rule swap_dist_triangle) (use Cons.prems in \<open>simp_all add: ys_def\<close>)
  also have "swap_dist xs ys \<le> 1"
  proof (cases "Suc i < length xs")
    case True
    hence "swap_dist xs ys = 1"
      unfolding ys_def by (intro swap_dist_swap_adj_list) (use Cons.prems in auto)
    thus ?thesis
      by simp
  qed (auto simp: ys_def swap_adj_list_def)
  also have "swap_dist ys (swap_adjs_list is ys) \<le> length is"
    by (rule Cons.IH) (use Cons.prems in \<open>auto simp: ys_def\<close>)
  finally show ?case
    by simp
qed simp_all

text \<open>
  Phrased in another way, any sequence of adjacent swaps that makes two lists the same must
  have a length at least as big as the swap distance of the two lists.
\<close>
theorem swap_dist_minimal:
  assumes "distinct xs"
  assumes "\<forall>i\<in>set is. Suc i < length xs"
  assumes "swap_adjs_list is xs = ys"
  shows   "length is \<ge> swap_dist xs ys"
  using swap_dist_swap_adjs_list[of xs "is"] assms by blast


text \<open>
  Next, we will show that this lower bound is sharp, i.e.\ there exists a sequence of swaps
  that makes the two lists the same whose length is exactly the swap distance.

  To this end, we derive an algorithm to compute a sequence of swaps whose effect is equivalent to
  the permutation $[0, 1, \ldots, n-1] \mapsto [i_0, i_1, \ldots, i_{n-1}]$.

  We first define the following function, which returns a list of swaps that pulls the
  $i$-th element of a list to the front, i.e.\ it corresponds to the permutation
  $[0,1,\ldots,n-1] \mapsto [i,0,1,\ldots,i-1,i+1,\ldots,n-1]$.
\<close>

definition pull_to_front_swaps :: "nat \<Rightarrow> nat list" where
  "pull_to_front_swaps i = rev [0..<i]"

lemma length_pull_to_front_swaps [simp]: "length (pull_to_front_swaps i) = i"
  by (simp add: pull_to_front_swaps_def)

lemma set_pull_to_front_swaps [simp]: "set (pull_to_front_swaps i) = {0..<i}"
  by (simp add: pull_to_front_swaps_def)

lemma pull_to_front_swaps_0 [simp]: "pull_to_front_swaps 0 = []"
  and pull_to_front_swaps_Suc: "pull_to_front_swaps (Suc i) = i # pull_to_front_swaps i"
  by (simp_all add: pull_to_front_swaps_def)

lemma swap_adjs_list_pull_to_front:
  assumes "i < length xs"
  shows   "swap_adjs_list (pull_to_front_swaps i) xs = (xs ! i) # take i xs @ drop (Suc i) xs"
  using assms
proof (induction i arbitrary: xs)
  case 0
  have "xs = xs ! 0 # drop (Suc 0) xs"
    using 0 by (cases xs) auto
  thus ?case by simp
next
  case (Suc i xs)
  define x y where "x = xs ! i" and "y = xs ! Suc i"
  define ys zs where "ys = take i xs" and "zs = drop (i+2) xs"
  have [simp]: "length ys = i"
    using Suc.prems by (simp add: ys_def)
  have xs_eq: "xs = ys @ x # y # zs"
    unfolding x_def y_def ys_def zs_def using Suc.prems by (simp add: Cons_nth_drop_Suc)

  have "swap_adjs_list (pull_to_front_swaps (Suc i)) xs = 
          y # ys @ drop (Suc i) (xs[i := y, Suc i := x])" using Suc.prems
    by (simp add: pull_to_front_swaps_Suc swap_adj_list_def Suc.IH x_def y_def ys_def zs_def)
  also have "drop (Suc i) (xs[i := y, Suc i := x]) = x # zs"
    by (simp add: xs_eq list_update_append)
  also have "y # ys @ x # zs = xs ! Suc i # take (Suc i) xs @ drop (Suc (Suc i)) xs"
    by (simp add: xs_eq nth_append)
  finally show ?case .
qed


text \<open>
  We now simply perform the ``pull to front'' operation so that the first element is the desired
  one. We then do the same thing again for the remaining $n-1$ indices (shifted accordingly)
  etc.\ until we reach the end of the index list.

  This corresponds to a variant of selection sort that only uses adjacent swaps, or it can also 
  be seen as a kind of reversal of insertion sort.
\<close>
fun swaps_of_perm :: "nat list \<Rightarrow> nat list" where
  "swaps_of_perm [] = []"
| "swaps_of_perm (i # is) =
     pull_to_front_swaps i @ map Suc (swaps_of_perm (map (\<lambda>j. if j \<ge> i then j - 1 else j) is))"

lemma set_swaps_of_perm_subset: "set (swaps_of_perm is) \<subseteq> (\<Union>i\<in>set is. {0..<i})"
  by (induction "is" rule: swaps_of_perm.induct; fastforce)

lemma swap_adjs_list_swaps_of_perm_aux:
  fixes i :: nat
  assumes "mset (i # is) = mset_set {0..<n}"
  shows   "mset (map (\<lambda>j. if i \<le> j then j - 1 else j) is) = mset_set {0..<n - 1}"
proof -
  define is1 where "is1 = filter_mset (\<lambda>j. i \<le> j) (mset is)"
  define is2 where "is2 = filter_mset (\<lambda>j. \<not>(i \<le> j)) (mset is)"

  have "i \<in># mset (i # is)"
    by simp
  also have "mset (i # is) = mset_set {0..<n}"
    by fact
  finally have i: "i < n"
    by simp

  have "mset_set {0..<n} = mset (i # is)"
    using assms by simp
  also have "\<dots> = add_mset i (mset is)"
    by simp
  finally have "mset is = mset_set {0..<n} - {#i#}"
    by simp
  also have "\<dots> = mset_set ({0..<n} - {i})"
    by (subst mset_set_Diff) (use i in auto)
  finally have mset_is: "mset is = mset_set ({0..<n} - {i})" .

  have "mset (map (\<lambda>j. if i \<le> j then j - 1 else j) is) = 
          {#if i \<le> j then j - 1 else j. j \<in># mset is#}"
    by simp
  also have "mset is = is1 + is2"
    unfolding is1_def is2_def by (rule multiset_partition)
  also have "{#if i \<le> j then j - 1 else j. j \<in># is1 + is2#} =
             {#j - 1. j \<in># is1#} + {#j. j \<in># is2#}" unfolding image_mset_union
    by (intro arg_cong2[of _ _ _ _ "(+)"] image_mset_cong) (auto simp: is1_def is2_def)
  also have "{#j - 1. j \<in># is1#} = {#j - 1 . j \<in># mset_set {x. x < n \<and> x \<noteq> i \<and> i \<le> x}#}"
    unfolding is1_def by (simp add: mset_is)
  also have "\<dots> = mset_set ((\<lambda>j. j - 1) ` {x. x < n \<and> x \<noteq> i \<and> i \<le> x})"
    by (intro image_mset_mset_set) (auto simp: inj_on_def)
  also have "{x. x < n \<and> x \<noteq> i \<and> i \<le> x} = {i<..<n}"
    by auto
  also have "bij_betw (\<lambda>j. j - 1) {i<..<n} {i..<n - 1}"
    by (rule bij_betwI[of _ _ _ "\<lambda>i. i+1"]) auto
  hence "(\<lambda>j. j - 1) ` {i<..<n} = {i..<n - 1}"
    by (simp add: bij_betw_def)
  also have "{#j. j \<in># is2#} = mset_set {x. x < n \<and> x \<noteq> i \<and> \<not> i \<le> x}"
    by (simp add: is2_def mset_is)
  also have "{x. x < n \<and> x \<noteq> i \<and> \<not> i \<le> x} = {..<i}"
    using i by auto
  also have "mset_set {i..<n - 1} + mset_set {..<i} =
             mset_set ({i..<n - 1} \<union> {..<i})"
    by (rule mset_set_Union [symmetric]) auto
  also have "{i..<n - 1} \<union> {..<i} = {0..<n - 1}"
    using i by auto
  finally show ?thesis .
qed

text \<open>
  The following result shows that the list of swaps returned by \<^const>\<open>swaps_of_perm\<close> indeed
  have the desired effect.  
\<close>
lemma swap_adjs_list_swaps_of_perm:
  assumes "mset is = mset_set {0..<length xs}"
  shows   "swap_adjs_list (swaps_of_perm is) xs = map (\<lambda>i. xs ! i) is"
  using assms
proof (induction "is" arbitrary: xs rule: swaps_of_perm.induct)
  case (1 xs)
  thus ?case
    by (simp add: mset_set_empty_iff)
next
  case (2 i "is" xs)
  define is' where "is' = map (\<lambda>j. if i \<le> j then j - 1 else j) is"
  have i: "i < length xs"
  proof -
    have "i \<in># mset (i # is)"
      by simp
    also have "mset (i # is) = mset_set {0..<length xs}"
      by fact
    finally show ?thesis
      by simp
  qed
  have "distinct (i # is)"
    using "2.prems" by (metis distinct_upt mset_eq_imp_distinct_iff mset_upt)

  have "swap_adjs_list (swaps_of_perm (i # is)) xs =
          swap_adjs_list (map Suc (swaps_of_perm is'))
            (swap_adjs_list (pull_to_front_swaps i) xs)"
    by (simp add: swap_adjs_list_append is'_def)
  also have "swap_adjs_list (pull_to_front_swaps i) xs = xs ! i # take i xs @ drop (Suc i) xs"
    by (subst swap_adjs_list_pull_to_front) (use i in auto)
  also have "swap_adjs_list (map Suc (swaps_of_perm is')) \<dots> =
             xs ! i # swap_adjs_list (swaps_of_perm is') (take i xs @ drop (Suc i) xs)"
    by (subst swap_adjs_list_Cons) (simp_all add: o_def)
  also have "swap_adjs_list (swaps_of_perm is') (take i xs @ drop (Suc i) xs) =
               map ((!) (take i xs @ drop (Suc i) xs)) is'"
    unfolding is'_def
  proof (rule "2.IH")
    have "mset (map (\<lambda>j. if i \<le> j then j - 1 else j) is) = 
            mset_set {0..<length xs - 1}"
      by (rule swap_adjs_list_swaps_of_perm_aux) (use "2.prems" in simp_all)
    also have "length xs - 1 = length (take i xs @ drop (Suc i) xs)"
      using i by simp
    finally show "mset (map (\<lambda>j. if i \<le> j then j - 1 else j) is) =
                    mset_set {0..<length (take i xs @ drop (Suc i) xs)}" .
  qed
  also have "xs ! i # map ((!) (take i xs @ drop (Suc i) xs)) is' = map ((!) xs) (i # is)"
    by (rule nth_equalityI)
       (use i \<open>distinct (i # is)\<close>
        in \<open>force simp: is'_def o_def nth_append nth_Cons set_conv_nth split: nat.splits\<close>)+
  finally show ?case .
qed

text \<open>
  The number of swaps returned by \<^const>\<open>swaps_of_perm\<close> is exactly the number of inversions in the
  input list (i.e.\ of the index permutation described by it).
\<close>
lemma length_swaps_of_perm:
  assumes "mset is = mset_set {0..<length is}"
  shows   "length (swaps_of_perm is) = inversion_number is"
  using assms
proof (induction "is" rule: swaps_of_perm.induct)
  case (2 i "is")
  define n where "n = length is"
  define is' where "is' = map (\<lambda>j. if i \<le> j then j - 1 else j) is"
  have "mset is' = mset_set {0..<Suc (length is)-1}"
    unfolding is'_def by (rule swap_adjs_list_swaps_of_perm_aux) (use "2.prems" in simp_all)
  also have "Suc (length is) - 1 = length (map (\<lambda>j. if i \<le> j then j - 1 else j) is)"
    by simp
  finally have is': "mset is' = mset_set {0..<\<dots>}" .

  have i: "i \<le> n"
  proof -
    have "i \<in># mset (i # is)"
      by simp
    also have "mset (i # is) = mset_set {0..n}"
      unfolding n_def using "2.prems" by (simp add: atLeastLessThanSuc_atLeastAtMost)
    finally show ?thesis
      by simp
  qed

  have "mset_set {0..n} = mset (i # is)"
    using "2.prems" by (simp add: n_def atLeastLessThanSuc_atLeastAtMost)
  also have "\<dots> = add_mset i (mset is)"
    by simp
  finally have "mset is = mset_set {0..n} - {#i#}"
    by simp
  also have "\<dots> = mset_set ({0..n} - {i})"
    by (subst mset_set_Diff) (use i in auto)
  finally have mset_is: "mset is = mset_set ({0..n} - {i})" .

  have set_is: "set is = {0..n} - {i}"
  proof -
    have "set is = set_mset (mset is)"
      by simp
    also have "\<dots> = {0..n} - {i}"
      by (subst mset_is) simp_all
    finally show ?thesis .
  qed

  have "length (swaps_of_perm (i # is)) = i + length (swaps_of_perm is')"
    by (simp add: is'_def)
  also have "length (swaps_of_perm is') = inversion_number is'"
    using is' unfolding is'_def by (rule "2.IH")
  also have "inversion_number is' = inversion_number is" unfolding is'_def
    by (rule inversion_number_map) (auto intro!: strict_mono_onI simp: set_is split: if_splits)
  finally have 1: "length (swaps_of_perm (i # is)) = i + inversion_number is"
    by simp

  have "inversion_number (i # is) = length (filter (\<lambda>y. y < i) is) + inversion_number is"
    by (simp add: is'_def inversion_number_Cons)
  also have "length (filter (\<lambda>y. y < i) is) = size (filter_mset (\<lambda>y. y < i) (mset is))"
    by (metis mset_filter size_mset)
  also have "\<dots> = card {x. x \<le> n \<and> x \<noteq> i \<and> x < i}"
    by (subst mset_is) simp
  also have "{x. x \<le> n \<and> x \<noteq> i \<and> x < i} = {0..<i}"
    using i by auto
  also have "card \<dots> = i"
    by simp
  finally have 2: "inversion_number (i # is) = i + inversion_number is" .

  show ?case
    using 1 2 by metis
qed simp_all


text \<open>
  Finally, we use the above to give a list of swap operations that map one list to another.
  The number of swap operations produced by this is exactly the swap distance of the two lists.
\<close>
definition swaps_of_perm' :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat list" where
  "swaps_of_perm' xs ys = swaps_of_perm (map (index xs) ys)" 

theorem swaps_of_perm':
  assumes "distinct xs" "distinct ys" "set xs = set ys"
  shows   "\<forall>i\<in>set (swaps_of_perm' xs ys). Suc i < length xs"
          "swap_adjs_list (swaps_of_perm' xs ys) xs = ys"
          "length (swaps_of_perm' xs ys) = swap_dist xs ys"
proof -
  have length_eq: "length xs = length ys"
    using assms by (metis distinct_card)
  have mset_eq: "mset xs = mset ys"
    using assms by (simp add: set_eq_iff_mset_eq_distinct)

  have mset_eq': "image_mset (index xs) (mset ys) = mset_set {0..<length xs}"
    by (metis assms(1) map_index_self mset_eq mset_map mset_upt)

  have "swap_adjs_list (swaps_of_perm' xs ys) xs = map ((!) xs) (map (index xs) ys)"
    unfolding swaps_of_perm'_def
    by (rule swap_adjs_list_swaps_of_perm) (simp add: mset_eq')
  also have "\<dots> = map id ys"
    unfolding map_map by (intro map_cong) (simp_all add: assms)
  finally show "swap_adjs_list (swaps_of_perm' xs ys) xs = ys"
    by simp

  have "set (swaps_of_perm' xs ys) \<subseteq> (\<Union>i\<in>set (map (index xs) ys). {0..<i})"
    unfolding swaps_of_perm'_def by (rule set_swaps_of_perm_subset)
  also have "set (map (index xs) ys) = {0..<length xs}"
    by (simp add: assms(1,3) index_image)
  also have "(\<Union>i\<in>{0..<length xs}. {0..<i}) \<subseteq> {i. Suc i < length xs}"
    by auto
  finally show "\<forall>i\<in>set (swaps_of_perm' xs ys). Suc i < length xs"
    by blast

  have "length (swaps_of_perm' xs ys) = inversion_number (map (index xs) ys) "
    unfolding swaps_of_perm'_def by (rule length_swaps_of_perm) (simp_all add: mset_eq' length_eq)
  also have "\<dots> = swap_dist xs ys"
    using assms by (simp add: swap_dist_conv_inversion_number)
  finally show "length (swaps_of_perm' xs ys) = swap_dist xs ys" .
qed

text \<open>
  Finally, we can derive the alternative characterisation of the swap distance.
\<close>
lemma swap_dist_altdef:
  assumes "distinct xs" "distinct ys" "set xs = set ys"
  shows   "swap_dist xs ys = (INF is\<in>{is. swap_adjs_list is xs = ys}. length is)"
proof (rule antisym)
  show "swap_dist xs ys \<le> (INF is\<in>{is. swap_adjs_list is xs = ys}. length is)"
  proof (rule cINF_greatest)
    show "{is. swap_adjs_list is xs = ys} \<noteq> {}"
      using swaps_of_perm'[OF assms] by auto
    show "swap_dist xs ys \<le> length is" if "is \<in> {is. swap_adjs_list is xs = ys}" for "is"
      using that assms(1) swap_dist_swap_adjs_list by auto
  qed
next
  have "(INF is\<in>{is. swap_adjs_list is xs = ys}. length is) \<le> length (swaps_of_perm' xs ys)"
    by (rule cINF_lower) (use swaps_of_perm'[OF assms] in auto)
  also have "\<dots> = swap_dist xs ys"
    using swaps_of_perm'[OF assms] by simp
  finally show "swap_dist xs ys \<ge> (INF is\<in>{is. swap_adjs_list is xs = ys}. length is)" .
qed

end
