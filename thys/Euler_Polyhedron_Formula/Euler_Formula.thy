section \<open>Euler's Polyhedron Formula\<close>

text \<open>One of the Famous 100 Theorems, ported from HOL Light\<close>
text\<open>Cited source:  
Lawrence, J. (1997). A Short Proof of Euler's Relation for Convex Polytopes. 
\emph{Canadian Mathematical Bulletin}, \textbf{40}(4), 471--474.\<close>

theory Euler_Formula
  imports 
    "HOL-Analysis.Analysis" 
    Library_Extras
    Inclusion_Exclusion
begin


text\<open> Interpret which "side" of a hyperplane a point is on.                     \<close>

definition hyperplane_side
  where "hyperplane_side \<equiv> \<lambda>(a,b). \<lambda>x. sgn (a \<bullet> x - b)"

text\<open> Equivalence relation imposed by a hyperplane arrangement.                 \<close>

definition hyperplane_equiv
 where "hyperplane_equiv \<equiv> \<lambda>A x y. \<forall>h \<in> A. hyperplane_side h x = hyperplane_side h y"

lemma hyperplane_equiv_refl [iff]: "hyperplane_equiv A x x"
  by (simp add: hyperplane_equiv_def)

lemma hyperplane_equiv_sym:
   "hyperplane_equiv A x y \<longleftrightarrow> hyperplane_equiv A y x"
  by (auto simp: hyperplane_equiv_def)

lemma hyperplane_equiv_trans:
   "\<lbrakk>hyperplane_equiv A x y; hyperplane_equiv A y z\<rbrakk> \<Longrightarrow> hyperplane_equiv A x z"
  by (auto simp: hyperplane_equiv_def)

lemma hyperplane_equiv_Un:
   "hyperplane_equiv (A \<union> B) x y \<longleftrightarrow> hyperplane_equiv A x y \<and> hyperplane_equiv B x y"
  by (meson Un_iff hyperplane_equiv_def)

subsection\<open> Cells of a hyperplane arrangement\<close>

definition hyperplane_cell :: "('a::real_inner \<times> real) set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "hyperplane_cell \<equiv> \<lambda>A C. \<exists>x. C = Collect (hyperplane_equiv A x)"

lemma hyperplane_cell: "hyperplane_cell A C \<longleftrightarrow> (\<exists>x. C = {y. hyperplane_equiv A x y})"
  by (simp add: hyperplane_cell_def)

lemma not_hyperplane_cell_empty [simp]: "\<not> hyperplane_cell A {}"
  using hyperplane_cell by auto

lemma nonempty_hyperplane_cell: "hyperplane_cell A C \<Longrightarrow> (C \<noteq> {})"
  by auto

lemma Union_hyperplane_cells: "\<Union> {C. hyperplane_cell A C} = UNIV"
  using hyperplane_cell by blast

lemma disjoint_hyperplane_cells:
   "\<lbrakk>hyperplane_cell A C1; hyperplane_cell A C2; C1 \<noteq> C2\<rbrakk> \<Longrightarrow> disjnt C1 C2"
  by (force simp: hyperplane_cell_def disjnt_iff hyperplane_equiv_def)

lemma disjoint_hyperplane_cells_eq:
   "\<lbrakk>hyperplane_cell A C1; hyperplane_cell A C2\<rbrakk> \<Longrightarrow> (disjnt C1 C2 \<longleftrightarrow> (C1 \<noteq> C2))"
  using disjoint_hyperplane_cells by auto

lemma hyperplane_cell_empty [iff]: "hyperplane_cell {} C \<longleftrightarrow> C = UNIV"
  by (simp add: hyperplane_cell hyperplane_equiv_def)

lemma hyperplane_cell_singleton_cases:
  assumes "hyperplane_cell {(a,b)} C"
  shows "C = {x. a \<bullet> x = b} \<or> C = {x. a \<bullet> x < b} \<or> C = {x. a \<bullet> x > b}"
proof -
  obtain x where x: "C = {y. hyperplane_side (a, b) x = hyperplane_side (a, b) y}"
    using assms by (auto simp: hyperplane_equiv_def hyperplane_cell)
  then show ?thesis
    by (auto simp: hyperplane_side_def sgn_if split: if_split_asm)
qed

lemma hyperplane_cell_singleton:
   "hyperplane_cell {(a,b)} C \<longleftrightarrow>
    (if a = 0 then C = UNIV else C = {x. a \<bullet> x = b} \<or> C = {x. a \<bullet> x < b} \<or> C = {x. a \<bullet> x > b})"
  apply (simp add: hyperplane_cell_def hyperplane_equiv_def hyperplane_side_def sgn_if split: if_split_asm)
  by (smt (verit) Collect_cong gt_ex hyperplane_eq_Ex lt_ex)

lemma hyperplane_cell_Un:
   "hyperplane_cell (A \<union> B) C \<longleftrightarrow>
        C \<noteq> {} \<and>
        (\<exists>C1 C2. hyperplane_cell A C1 \<and> hyperplane_cell B C2 \<and> C = C1 \<inter> C2)"
  by (auto simp: hyperplane_cell hyperplane_equiv_def)

lemma finite_hyperplane_cells:
   "finite A \<Longrightarrow> finite {C. hyperplane_cell A C}"
proof (induction rule: finite_induct)
  case (insert p A)
  obtain a b where peq: "p = (a,b)"
    by fastforce
  have "Collect (hyperplane_cell {p}) \<subseteq> {{x. a \<bullet> x = b},{x. a \<bullet> x < b},{x. a \<bullet> x > b}}"
    using hyperplane_cell_singleton_cases
    by (auto simp: peq)
  then have *: "finite (Collect (hyperplane_cell {p}))"
    by (simp add: finite_subset)
  define \<C> where "\<C> \<equiv> (\<Union>C1 \<in> {C. hyperplane_cell A C}.  \<Union>C2 \<in> {C. hyperplane_cell {p} C}. {C1 \<inter> C2})"
  have "{a. hyperplane_cell (insert p A) a} \<subseteq>  \<C>"
    using hyperplane_cell_Un [of "{p}" A] by (auto simp: \<C>_def)
  moreover have "finite \<C>"
    using * \<C>_def insert.IH by blast
  ultimately show ?case
    using finite_subset by blast
qed auto

lemma finite_restrict_hyperplane_cells:
   "finite A \<Longrightarrow> finite {C. hyperplane_cell A C \<and> P C}"
  by (simp add: finite_hyperplane_cells)

lemma finite_set_of_hyperplane_cells:
   "\<lbrakk>finite A; \<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C\<rbrakk> \<Longrightarrow> finite \<C>"
  by (metis finite_hyperplane_cells finite_subset mem_Collect_eq subsetI)

lemma pairwise_disjoint_hyperplane_cells:
   "(\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C) \<Longrightarrow> pairwise disjnt \<C>"
  by (metis disjoint_hyperplane_cells pairwiseI)

lemma hyperplane_cell_Int_open_affine:
  assumes "finite A" "hyperplane_cell A C"
  obtains S T where "open S" "affine T" "C = S \<inter> T"
  using assms
proof (induction arbitrary: thesis C rule: finite_induct)
  case empty
  then show ?case
    by auto 
next
  case (insert p A thesis C')
  obtain a b where peq: "p = (a,b)"
    by fastforce
  obtain C C1 where C1: "hyperplane_cell {(a,b)} C1" and C: "hyperplane_cell A C" 
              and "C' \<noteq> {}" and C': "C' = C1 \<inter> C"
    by (metis hyperplane_cell_Un insert.prems(2) insert_is_Un peq)
  then obtain S T where ST: "open S" "affine T" "C = S \<inter> T"
    by (meson insert.IH)
  show ?case
  proof (cases "a=0")
    case True
    with insert.prems show ?thesis
      by (metis C1 Int_commute ST \<open>C' = C1 \<inter> C\<close> hyperplane_cell_singleton inf_top.right_neutral) 
  next
    case False
    then consider "C1 = {x. a \<bullet> x = b}" | "C1 = {x. a \<bullet> x < b}" | "C1 = {x. b < a \<bullet> x}"
      by (metis C1 hyperplane_cell_singleton)
    then show ?thesis
    proof cases
      case 1
      then show thesis
        by (metis C' ST affine_Int affine_hyperplane inf_left_commute insert.prems(1))
    next
      case 2
      with ST show thesis
          by (metis Int_assoc C' insert.prems(1) open_Int open_halfspace_lt)
    next
      case 3
      with ST show thesis
        by (metis Int_assoc C' insert.prems(1) open_Int open_halfspace_gt)
    qed
  qed
qed

lemma hyperplane_cell_relatively_open:
  assumes "finite A" "hyperplane_cell A C"
  shows "openin (subtopology euclidean (affine hull C)) C"
proof -
  obtain S T where "open S" "affine T" "C = S \<inter> T"
    by (meson assms hyperplane_cell_Int_open_affine)
  show ?thesis
  proof (cases "S \<inter> T = {}")
    case True
    then show ?thesis
      by (simp add: \<open>C = S \<inter> T\<close>)
  next
    case False
    then have "affine hull (S \<inter> T) = T"
      by (metis \<open>affine T\<close> \<open>open S\<close> affine_hull_affine_Int_open hull_same inf_commute)
    then show ?thesis
      using \<open>C = S \<inter> T\<close> \<open>open S\<close> openin_subtopology by fastforce
  qed
qed

lemma hyperplane_cell_relative_interior:
   "\<lbrakk>finite A; hyperplane_cell A C\<rbrakk> \<Longrightarrow> rel_interior C = C"
  by (simp add: hyperplane_cell_relatively_open rel_interior_openin)

lemma hyperplane_cell_convex:
  assumes "hyperplane_cell A C"
  shows "convex C"
proof -
  obtain c where c: "C = {y. hyperplane_equiv A c y}"
    by (meson assms hyperplane_cell)
  have "convex (\<Inter>h\<in>A. {y. hyperplane_side h c = hyperplane_side h y})"
  proof (rule convex_INT)
    fix h :: "'a \<times> real"
    assume "h \<in> A"
    obtain a b where heq: "h = (a,b)"
      by fastforce
    have [simp]: "{y. \<not> a \<bullet> c < a \<bullet> y \<and> a \<bullet> y = a \<bullet> c} = {y. a \<bullet> y = a \<bullet> c}"
                 "{y. \<not> b < a \<bullet> y \<and> a \<bullet> y \<noteq> b} = {y. b > a \<bullet> y}"
      by auto
    then show "convex {y. hyperplane_side h c = hyperplane_side h y}"
      by (fastforce simp: heq hyperplane_side_def sgn_if convex_halfspace_gt convex_halfspace_lt convex_hyperplane cong: conj_cong)
  qed
  with c show ?thesis
    by (simp add: hyperplane_equiv_def INTER_eq)
qed

lemma hyperplane_cell_Inter:
  assumes "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C"
    and "\<C> \<noteq> {}" and INT: "\<Inter>\<C> \<noteq> {}"
  shows "hyperplane_cell A (\<Inter>\<C>)"
proof -
  have "\<Inter>\<C> = {y. hyperplane_equiv A z y}" 
    if "z \<in> \<Inter>\<C>" for z
      using assms that by (force simp: hyperplane_cell hyperplane_equiv_def)
  with INT hyperplane_cell show ?thesis
    by fastforce
qed


lemma hyperplane_cell_Int:
   "\<lbrakk>hyperplane_cell A S; hyperplane_cell A T; S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow> hyperplane_cell A (S \<inter> T)"
  by (metis hyperplane_cell_Un sup.idem)

subsection\<open> A cell complex is considered to be a union of such cells\<close>

definition hyperplane_cellcomplex 
  where "hyperplane_cellcomplex A S \<equiv>
        \<exists>\<T>. (\<forall>C \<in> \<T>. hyperplane_cell A C) \<and> S = \<Union>\<T>"

lemma hyperplane_cellcomplex_empty [simp]: "hyperplane_cellcomplex A {}"
  using hyperplane_cellcomplex_def by auto

lemma hyperplane_cell_cellcomplex:
   "hyperplane_cell A C \<Longrightarrow> hyperplane_cellcomplex A C"
  by (auto simp: hyperplane_cellcomplex_def)

lemma hyperplane_cellcomplex_Union:
  assumes "\<And>S. S \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (\<Union> \<C>)"
proof -
  obtain \<F> where \<F>: "\<And>S. S \<in> \<C> \<Longrightarrow> (\<forall>C \<in> \<F> S. hyperplane_cell A C) \<and> S = \<Union>(\<F> S)"
    by (metis assms hyperplane_cellcomplex_def)
  show ?thesis
    unfolding hyperplane_cellcomplex_def
    using \<F> by (fastforce intro: exI [where x="\<Union> (\<F> ` \<C>)"])
qed

lemma hyperplane_cellcomplex_Un:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S \<union> T)"
  by (smt (verit) Un_iff Union_Un_distrib hyperplane_cellcomplex_def)

lemma hyperplane_cellcomplex_UNIV [simp]: "hyperplane_cellcomplex A UNIV"
  by (metis Union_hyperplane_cells hyperplane_cellcomplex_def mem_Collect_eq)

lemma hyperplane_cellcomplex_Inter:
  assumes "\<And>S. S \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (\<Inter>\<C>)"
proof (cases "\<C> = {}")
  case True
  then show ?thesis
    by simp
next
  case False
  obtain \<F> where \<F>: "\<And>S. S \<in> \<C> \<Longrightarrow> (\<forall>C \<in> \<F> S. hyperplane_cell A C) \<and> S = \<Union>(\<F> S)"
    by (metis assms hyperplane_cellcomplex_def)
  have *: "\<C> = (\<lambda>S. \<Union>(\<F> S)) ` \<C>"
    using \<F> by force
  define U where "U \<equiv> \<Union> {T \<in> {\<Inter>(g ` \<C>) |g. \<forall>S\<in>\<C>. g S \<in> \<F> S}. T \<noteq> {}}"
  have "\<Inter>\<C> = \<Union>{\<Inter>(g ` \<C>) |g. \<forall>S\<in>\<C>. g S \<in> \<F> S}"
    using False \<F> unfolding Inter_over_Union [symmetric]
    by blast
  also have "\<dots> = U"
    unfolding U_def
    by blast
  finally have "\<Inter>\<C> = U" .
  have "hyperplane_cellcomplex A U"
    using False \<F> unfolding U_def
    apply (intro hyperplane_cellcomplex_Union hyperplane_cell_cellcomplex)
    by (auto intro!: hyperplane_cell_Inter)
  then show ?thesis
     by (simp add: \<open>\<Inter>\<C> = U\<close>)
qed

lemma hyperplane_cellcomplex_Int:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S \<inter> T)"
  using hyperplane_cellcomplex_Inter [of "{S,T}"] by force

lemma hyperplane_cellcomplex_Compl:
  assumes "hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (- S)"
proof -
  obtain \<C> where \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C" and "S = \<Union>\<C>"
    by (meson assms hyperplane_cellcomplex_def)
  have "hyperplane_cellcomplex A (\<Inter>T \<in> \<C>. -T)"
  proof (intro hyperplane_cellcomplex_Inter)
    fix C0
    assume "C0 \<in> uminus ` \<C>"
    then obtain C where C: "C0 = -C" "C \<in> \<C>"
      by auto
    have *: "-C = \<Union> {D. hyperplane_cell A D \<and> D \<noteq> C}"  (is "_ = ?rhs")
    proof
      show "- C \<subseteq> ?rhs"
        using hyperplane_cell by blast
      show "?rhs \<subseteq> - C"
        by clarify (meson \<open>C \<in> \<C>\<close> \<C> disjnt_iff disjoint_hyperplane_cells)
    qed
    then show "hyperplane_cellcomplex A C0"
      by (metis (no_types, lifting) C(1) hyperplane_cell_cellcomplex hyperplane_cellcomplex_Union mem_Collect_eq)
  qed
  then show ?thesis
    by (simp add: \<open>S = \<Union> \<C>\<close> uminus_Sup)
qed

lemma hyperplane_cellcomplex_diff:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S - T)"
  using hyperplane_cellcomplex_Inter [of "{S,-T}"] 
  by (force simp: Diff_eq hyperplane_cellcomplex_Compl)

lemma hyperplane_cellcomplex_mono:
  assumes "hyperplane_cellcomplex A S" "A \<subseteq> B"
  shows "hyperplane_cellcomplex B S"
proof -
  obtain \<C> where \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C" and eq: "S = \<Union>\<C>"
    by (meson assms hyperplane_cellcomplex_def)
  show ?thesis
    unfolding eq
  proof (intro hyperplane_cellcomplex_Union)
    fix C
    assume "C \<in> \<C>"
    have "\<And>x. x \<in> C \<Longrightarrow> \<exists>D'. (\<exists>D. D' = D \<inter> C \<and> hyperplane_cell (B - A) D \<and> D \<inter> C \<noteq> {}) \<and> x \<in> D'"
      unfolding hyperplane_cell_def by blast
    then
    have "hyperplane_cellcomplex (A \<union> (B - A)) C"
      unfolding hyperplane_cellcomplex_def hyperplane_cell_Un
      using \<C> \<open>C \<in> \<C>\<close> by (fastforce intro!: exI [where x=" {D \<inter> C |D. hyperplane_cell (B - A) D \<and> D \<inter> C \<noteq> {}}"])
    moreover have "B = A \<union> (B - A)"
      using \<open>A \<subseteq> B\<close> by auto
    ultimately show "hyperplane_cellcomplex B C" by simp
  qed
qed

lemma finite_hyperplane_cellcomplexes:
  assumes "finite A"
  shows "finite {C. hyperplane_cellcomplex A C}"
proof -
  have "{C. hyperplane_cellcomplex A C} \<subseteq> image \<Union> {T. T \<subseteq> {C. hyperplane_cell A C}}"
    by (force simp: hyperplane_cellcomplex_def subset_eq)
  with finite_hyperplane_cells show ?thesis
    by (metis assms finite_Collect_subsets finite_surj)
qed

lemma finite_restrict_hyperplane_cellcomplexes:
   "finite A \<Longrightarrow> finite {C. hyperplane_cellcomplex A C \<and> P C}"
  by (simp add: finite_hyperplane_cellcomplexes)

lemma finite_set_of_hyperplane_cellcomplex:
  assumes "finite A" "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A C"
  shows "finite \<C>"
  by (metis assms finite_hyperplane_cellcomplexes mem_Collect_eq rev_finite_subset subsetI)

lemma cell_subset_cellcomplex:
   "\<lbrakk>hyperplane_cell A C; hyperplane_cellcomplex A S\<rbrakk> \<Longrightarrow> C \<subseteq> S \<longleftrightarrow> ~ disjnt C S"
  by (smt (verit) Union_iff disjnt_iff disjnt_subset1 disjoint_hyperplane_cells_eq hyperplane_cellcomplex_def subsetI)


subsection \<open>Euler characteristic\<close>


definition Euler_characteristic :: "('a::euclidean_space \<times> real) set \<Rightarrow> 'a set \<Rightarrow> int"
  where "Euler_characteristic A S \<equiv>
        (\<Sum>C | hyperplane_cell A C \<and> C \<subseteq> S. (-1) ^ nat (aff_dim C))"

lemma Euler_characteristic_empty [simp]: "Euler_characteristic A {} = 0"
  by (simp add: sum.neutral Euler_characteristic_def)

lemma Euler_characteristic_cell_Union:
  assumes "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C"
  shows "Euler_characteristic A (\<Union> \<C>) = (\<Sum>C\<in>\<C>. (- 1) ^ nat (aff_dim C))"
proof -
  have "\<And>x. \<lbrakk>hyperplane_cell A x; x \<subseteq> \<Union> \<C>\<rbrakk> \<Longrightarrow> x \<in> \<C>"
    by (metis assms disjnt_Union1 disjnt_subset1 disjoint_hyperplane_cells_eq)
  then have "{C. hyperplane_cell A C \<and> C \<subseteq> \<Union> \<C>} = \<C>"
    by (auto simp: assms)
  then show ?thesis
    by (auto simp: Euler_characteristic_def)
qed

lemma Euler_characteristic_cell:
   "hyperplane_cell A C \<Longrightarrow> Euler_characteristic A C = (-1) ^ (nat(aff_dim C))"
  using Euler_characteristic_cell_Union [of "{C}"] by force

lemma Euler_characteristic_cellcomplex_Un:
  assumes "finite A" "hyperplane_cellcomplex A S" 
    and AT: "hyperplane_cellcomplex A T" and "disjnt S T"
  shows "Euler_characteristic A (S \<union> T) =
         Euler_characteristic A S + Euler_characteristic A T"
proof -
  have *: "{C. hyperplane_cell A C \<and> C \<subseteq> S \<union> T} =
        {C. hyperplane_cell A C \<and> C \<subseteq> S} \<union> {C. hyperplane_cell A C \<and> C \<subseteq> T}"
    using cell_subset_cellcomplex [OF _ AT] by (auto simp: disjnt_iff)
  have **: "{C. hyperplane_cell A C \<and> C \<subseteq> S} \<inter> {C. hyperplane_cell A C \<and> C \<subseteq> T} = {}"
    using assms cell_subset_cellcomplex disjnt_subset1 by fastforce
  show ?thesis
  unfolding Euler_characteristic_def
    by (simp add: finite_restrict_hyperplane_cells assms * ** flip: sum.union_disjoint)
qed

lemma Euler_characteristic_cellcomplex_Union:
  assumes "finite A" 
    and \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A C" "pairwise disjnt \<C>"
  shows "Euler_characteristic A (\<Union> \<C>) = sum (Euler_characteristic A) \<C>"
proof -
  have "finite \<C>"
    using assms finite_set_of_hyperplane_cellcomplex by blast
  then show ?thesis
    using \<C>
  proof (induction rule: finite_induct)
    case empty
    then show ?case
      by auto
  next
    case (insert C \<C>)
    then obtain "disjoint \<C>" "disjnt C (\<Union> \<C>)"
      by (metis disjnt_Union2 pairwise_insert)
    with insert show ?case
      by (simp add: Euler_characteristic_cellcomplex_Un hyperplane_cellcomplex_Union \<open>finite A\<close>)
  qed
qed

lemma Euler_characteristic:
  fixes A :: "('n::euclidean_space * real) set"
  assumes "finite A"
  shows "Euler_characteristic A S =
        (\<Sum>d = 0..DIM('n). (-1) ^ d * int (card {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}))"
        (is "_ = ?rhs")
proof -
  have "\<And>T. \<lbrakk>hyperplane_cell A T; T \<subseteq> S\<rbrakk> \<Longrightarrow> aff_dim T \<in> {0..DIM('n)}"
    by (metis atLeastAtMost_iff nle_le order.strict_iff_not aff_dim_negative_iff 
        nonempty_hyperplane_cell aff_dim_le_DIM)
  then have *: "aff_dim ` {C. hyperplane_cell A C \<and> C \<subseteq> S} \<subseteq> int ` {0..DIM('n)}"
    by (auto simp: image_int_atLeastAtMost)
  have "Euler_characteristic A  S = (\<Sum>y\<in>int ` {0..DIM('n)}.
       \<Sum>C\<in>{x. hyperplane_cell A x \<and> x \<subseteq> S \<and> aff_dim x = y}. (- 1) ^ nat y) "
    using sum.group [of "{C. hyperplane_cell A C \<and> C \<subseteq> S}" "int ` {0..DIM('n)}" aff_dim "\<lambda>C. (-1::int) ^ nat(aff_dim C)", symmetric]
    by (simp add: assms Euler_characteristic_def finite_restrict_hyperplane_cells *)
  also have "\<dots> = ?rhs"
    by (simp add: sum.reindex mult_of_nat_commute)
  finally show ?thesis .
qed

subsection \<open>Show that the characteristic is invariant w.r.t. hyperplane arrangement.\<close>

lemma hyperplane_cells_distinct_lemma:
   "{x. a \<bullet> x = b} \<inter> {x. a \<bullet> x < b} = {} \<and>
         {x. a \<bullet> x = b} \<inter> {x. a \<bullet> x > b} = {} \<and>
         {x. a \<bullet> x < b} \<inter> {x. a \<bullet> x = b} = {} \<and>
         {x. a \<bullet> x < b} \<inter> {x. a \<bullet> x > b} = {} \<and>
         {x. a \<bullet> x > b} \<inter> {x. a \<bullet> x = b} = {} \<and>
         {x. a \<bullet> x > b} \<inter> {x. a \<bullet> x < b} = {}"
  by auto

proposition Euler_characterstic_lemma:
  assumes "finite A" and "hyperplane_cellcomplex A S"
  shows "Euler_characteristic (insert h A) S = Euler_characteristic A S"
proof -
  obtain \<C> where \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C" and "S = \<Union>\<C>"
              and "pairwise disjnt \<C>"
    by (meson assms hyperplane_cellcomplex_def pairwise_disjoint_hyperplane_cells)
  obtain a b where "h = (a,b)"
    by fastforce
  have "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A C \<and> hyperplane_cellcomplex (insert (a,b) A) C"
    by (meson \<C> hyperplane_cell_cellcomplex hyperplane_cellcomplex_mono subset_insertI)
  moreover
  have "sum (Euler_characteristic (insert (a,b) A)) \<C> = sum (Euler_characteristic A) \<C>"
  proof (rule sum.cong [OF refl])
    fix C
    assume "C \<in> \<C>"
    have "Euler_characteristic (insert (a, b) A) C = (-1) ^ nat(aff_dim C)"
    proof (cases "hyperplane_cell (insert (a,b) A) C")
      case True
      then show ?thesis
        using Euler_characteristic_cell by blast
    next
      case False
      with \<C>[OF \<open>C \<in> \<C>\<close>] have "a \<noteq> 0"
        by (smt (verit, ccfv_threshold) hyperplane_cell_Un hyperplane_cell_empty hyperplane_cell_singleton insert_is_Un sup_bot_left)
      have "convex C"
        using \<open>hyperplane_cell A C\<close> hyperplane_cell_convex by blast
      define r where "r \<equiv> (\<Sum>D\<in>{C' \<inter> C |C'. hyperplane_cell {(a, b)} C' \<and> C' \<inter> C \<noteq> {}}. (-1::int) ^ nat (aff_dim D))"
      have "Euler_characteristic (insert (a, b) A) C 
           = (\<Sum>D | (D \<noteq> {} \<and>
                     (\<exists>C1 C2. hyperplane_cell {(a, b)} C1 \<and> hyperplane_cell A C2 \<and> D = C1 \<inter> C2)) \<and> D \<subseteq> C.
              (- 1) ^ nat (aff_dim D))"
        unfolding r_def Euler_characteristic_def insert_is_Un [of _ A] hyperplane_cell_Un ..
      also have "\<dots> = r"
        unfolding r_def
        apply (rule sum.cong [OF _ refl])
        using \<open>hyperplane_cell A C\<close> disjoint_hyperplane_cells disjnt_iff
        by (smt (verit, ccfv_SIG) Collect_cong Int_iff disjoint_iff subsetD subsetI)
      also have "\<dots> = (-1) ^ nat(aff_dim C)"
      proof -
        have "C \<noteq> {}"
          using \<open>hyperplane_cell A C\<close> by auto
        show ?thesis
        proof (cases "C \<subseteq> {x. a \<bullet> x < b} \<or> C \<subseteq> {x. a \<bullet> x > b} \<or> C \<subseteq> {x. a \<bullet> x = b}")
          case Csub: True
          with \<open>C \<noteq> {}\<close> have "r = sum (\<lambda>c. (-1) ^ nat (aff_dim c)) {C}"
            unfolding r_def
            apply (intro sum.cong [OF _ refl])
            by (auto simp: \<open>a \<noteq> 0\<close> hyperplane_cell_singleton)
          also have "\<dots> = (-1) ^ nat(aff_dim C)"
            by simp
          finally show ?thesis .
        next
          case False
          then obtain u v where uv: "u \<in> C" "\<not> a \<bullet> u < b" "v \<in> C" "\<not> a \<bullet> v > b"
            by blast
          have CInt_ne: "C \<inter> {x. a \<bullet> x = b} \<noteq> {}"
          proof (cases "a \<bullet> u = b \<or> a \<bullet> v = b")
            case True
            with uv show ?thesis
              by blast
          next
            case False
            have "a \<bullet> v < a \<bullet> u"
              using False uv by auto
            define w where "w \<equiv> v + ((b - a \<bullet> v) / (a \<bullet> u - a \<bullet> v)) *\<^sub>R (u - v)"
            have **: "v + a *\<^sub>R (u - v) = (1 - a) *\<^sub>R v + a *\<^sub>R u" for a
              by (simp add: algebra_simps)
            have "w \<in> C"
              unfolding w_def **
            proof (intro convexD_alt)
            qed (use \<open>a \<bullet> v < a \<bullet> u\<close> \<open>convex C\<close> uv in auto)
            moreover have "w \<in> {x. a \<bullet> x = b}"
              using \<open>a \<bullet> v < a \<bullet> u\<close> by (simp add: w_def inner_add_right inner_diff_right)
            ultimately show ?thesis
              by blast
          qed
          have Cab: "C \<inter> {x. a \<bullet> x < b} \<noteq> {} \<and> C \<inter> {x. b < a \<bullet> x} \<noteq> {}"
          proof -
            obtain u v where "u \<in> C" "a \<bullet> u = b" "v \<in> C" "a \<bullet> v \<noteq> b" "u\<noteq>v"
              using False \<open>C \<inter> {x. a \<bullet> x = b} \<noteq> {}\<close> by blast
            have "openin (subtopology euclidean (affine hull C)) C"
              using \<open>hyperplane_cell A C\<close> \<open>finite A\<close> hyperplane_cell_relatively_open by blast
            then obtain \<epsilon> where "0 < \<epsilon>"
                  and \<epsilon>: "\<And>x'. \<lbrakk>x' \<in> affine hull C; dist x' u < \<epsilon>\<rbrakk> \<Longrightarrow> x' \<in> C"
              by (meson \<open>u \<in> C\<close> openin_euclidean_subtopology_iff)
            define \<xi> where "\<xi> \<equiv> u - (\<epsilon> / 2 / norm (v - u)) *\<^sub>R (v - u)"
            have "\<xi> \<in> C"
            proof (rule \<epsilon>)
              show "\<xi> \<in> affine hull C"
                by (simp add: \<xi>_def \<open>u \<in> C\<close> \<open>v \<in> C\<close> hull_inc mem_affine_3_minus2)
            qed (use \<xi>_def \<open>0 < \<epsilon>\<close> in force)
            consider "a \<bullet> v < b" | "a \<bullet> v > b"
              using \<open>a \<bullet> v \<noteq> b\<close> by linarith
            then show ?thesis
            proof cases
              case 1
              moreover have "\<xi> \<in> {x. b < a \<bullet> x}"
                using "1" \<open>0 < \<epsilon>\<close> \<open>a \<bullet> u = b\<close> divide_less_cancel 
                by (fastforce simp: \<xi>_def algebra_simps)
              ultimately show ?thesis
                using \<open>v \<in> C\<close> \<open>\<xi> \<in> C\<close> by blast
            next
              case 2
              moreover have "\<xi> \<in> {x. b > a \<bullet> x}"
                using "2" \<open>0 < \<epsilon>\<close> \<open>a \<bullet> u = b\<close> divide_less_cancel 
                by (fastforce simp: \<xi>_def algebra_simps)
              ultimately show ?thesis
                using \<open>v \<in> C\<close> \<open>\<xi> \<in> C\<close> by blast
            qed
          qed
          have "r = (\<Sum>C\<in>{{x. a \<bullet> x = b} \<inter> C, {x. b < a \<bullet> x} \<inter> C, {x. a \<bullet> x < b} \<inter> C}.
                     (- 1) ^ nat (aff_dim C))"
            unfolding r_def 
          proof (intro sum.cong [OF _ refl] equalityI)
            show "{{x. a \<bullet> x = b} \<inter> C, {x. b < a \<bullet> x} \<inter> C, {x. a \<bullet> x < b} \<inter> C}
               \<subseteq> {C' \<inter> C |C'. hyperplane_cell {(a, b)} C' \<and> C' \<inter> C \<noteq> {}}"
              apply clarsimp
              using Cab Int_commute \<open>C \<inter> {x. a \<bullet> x = b} \<noteq> {}\<close> hyperplane_cell_singleton \<open>a \<noteq> 0\<close>
              by metis
          qed (auto simp: \<open>a \<noteq> 0\<close> hyperplane_cell_singleton)
          also have "\<dots> = (-1) ^ nat (aff_dim (C \<inter> {x. a \<bullet> x = b})) 
                        + (-1) ^ nat (aff_dim (C \<inter> {x. b < a \<bullet> x})) 
                        + (-1) ^ nat (aff_dim (C \<inter> {x. a \<bullet> x < b}))"
            using hyperplane_cells_distinct_lemma [of a b] Cab
            by (auto simp: sum.insert_if Int_commute Int_left_commute)
          also have "\<dots> = (- 1) ^ nat (aff_dim C)"
          proof -
            have *: "aff_dim (C \<inter> {x. a \<bullet> x < b}) = aff_dim C \<and> aff_dim (C \<inter> {x. a \<bullet> x > b}) = aff_dim C"
              by (metis Cab open_halfspace_lt open_halfspace_gt aff_dim_affine_hull 
                        affine_hull_convex_Int_open[OF \<open>convex C\<close>])
            obtain S T where "open S" "affine T" and Ceq: "C = S \<inter> T"
              by (meson \<open>hyperplane_cell A C\<close> \<open>finite A\<close> hyperplane_cell_Int_open_affine)
            have "affine hull C = affine hull T"
              by (metis Ceq \<open>C \<noteq> {}\<close> \<open>affine T\<close> \<open>open S\<close> affine_hull_affine_Int_open inf_commute)
            moreover
            have "T \<inter> ({x. a \<bullet> x = b} \<inter> S) \<noteq> {}"
              using Ceq \<open>C \<inter> {x. a \<bullet> x = b} \<noteq> {}\<close> by blast
            then have "affine hull (C \<inter> {x. a \<bullet> x = b}) = affine hull (T \<inter> {x. a \<bullet> x = b})"
              using affine_hull_affine_Int_open[of "T \<inter> {x. a \<bullet> x = b}" S] 
              by (simp add: Ceq Int_ac \<open>affine T\<close> \<open>open S\<close> affine_Int affine_hyperplane)
            ultimately have "aff_dim (affine hull C) = aff_dim(affine hull (C \<inter> {x. a \<bullet> x = b})) + 1"
              using CInt_ne False Ceq
              by (auto simp: aff_dim_affine_Int_hyperplane \<open>affine T\<close>)
            moreover have "0 \<le> aff_dim (C \<inter> {x. a \<bullet> x = b})"
              by (metis CInt_ne aff_dim_negative_iff linorder_not_le)
            ultimately show ?thesis
              by (simp add: * nat_add_distrib)
          qed
          finally show ?thesis .
        qed
      qed
      finally show "Euler_characteristic (insert (a, b) A) C = (-1) ^ nat(aff_dim C)" .
    qed
    then show "Euler_characteristic (insert (a, b) A) C = (Euler_characteristic A C)"
      by (simp add: Euler_characteristic_cell \<C> \<open>C \<in> \<C>\<close>)
  qed
  ultimately show ?thesis
    by (simp add: Euler_characteristic_cellcomplex_Union \<open>S = \<Union> \<C>\<close> \<open>disjoint \<C>\<close> \<open>h = (a, b)\<close> assms(1))
qed


lemma Euler_characterstic_invariant_aux:
  assumes "finite B" "finite A" "hyperplane_cellcomplex A S" 
  shows "Euler_characteristic (A \<union> B) S = Euler_characteristic A S"
  using assms
  by (induction rule: finite_induct) (auto simp: Euler_characterstic_lemma hyperplane_cellcomplex_mono)

lemma Euler_characterstic_invariant:
  assumes "finite A" "finite B" "hyperplane_cellcomplex A S" "hyperplane_cellcomplex B S"
  shows "Euler_characteristic A S = Euler_characteristic B S"
  by (metis Euler_characterstic_invariant_aux assms sup_commute)

lemma Euler_characteristic_inclusion_exclusion:
  assumes "finite A" "finite \<S>" "\<And>K. K \<in> \<S> \<Longrightarrow> hyperplane_cellcomplex A K"
  shows "Euler_characteristic A (\<Union> \<S>) = (\<Sum>\<T> | \<T> \<subseteq> \<S> \<and> \<T> \<noteq> {}. (- 1) ^ (card \<T> + 1) * Euler_characteristic A (\<Inter>\<T>))"
proof -
  interpret Incl_Excl "hyperplane_cellcomplex A" "Euler_characteristic A"
    proof
  show "Euler_characteristic A (S \<union> T) = Euler_characteristic A S + Euler_characteristic A T"
    if "hyperplane_cellcomplex A S" and "hyperplane_cellcomplex A T" and "disjnt S T" for S T
    using that Euler_characteristic_cellcomplex_Un assms(1) by blast 
  qed (use hyperplane_cellcomplex_Int hyperplane_cellcomplex_Un hyperplane_cellcomplex_diff in auto)
  show ?thesis
    using restricted assms by blast
qed



subsection \<open>Euler-type relation for full-dimensional proper polyhedral cones\<close>

lemma Euler_polyhedral_cone:
  fixes S :: "'n::euclidean_space set"
  assumes "polyhedron S" "conic S" and intS: "interior S \<noteq> {}" and "S \<noteq> UNIV"
  shows "(\<Sum>d = 0..DIM('n). (- 1) ^ d * int (card {f. f face_of S \<and> aff_dim f = int d})) = 0"  (is "?lhs = 0")
proof -
  have [simp]: "affine hull S = UNIV"
    by (simp add: affine_hull_nonempty_interior intS)
  with \<open>polyhedron S\<close>
  obtain H where "finite H"
    and Seq: "S = \<Inter>H"
    and Hex: "\<And>h. h\<in>H \<Longrightarrow> \<exists>a b. a\<noteq>0 \<and> h = {x. a \<bullet> x \<le> b}"
    and Hsub: "\<And>\<G>. \<G> \<subset> H \<Longrightarrow> S \<subset> \<Inter>\<G>"
    by (fastforce simp: polyhedron_Int_affine_minimal)
  have "0 \<in> S"
    using assms(2) conic_contains_0 intS interior_empty by blast
  have *: "\<exists>a. a\<noteq>0 \<and> h = {x. a \<bullet> x \<le> 0}" if "h \<in> H" for h
  proof -
    obtain a b where "a\<noteq>0" and ab: "h = {x. a \<bullet> x \<le> b}"
      using Hex [OF \<open>h \<in> H\<close>] by blast
    have "0 \<in> \<Inter>H"
      using Seq \<open>0 \<in> S\<close> by force
    then have "0 \<in> h"
      using that by blast
    consider "b=0" | "b < 0" | "b > 0"
      by linarith
    then
    show ?thesis
    proof cases
      case 1
      then show ?thesis
        using \<open>a \<noteq> 0\<close> ab by blast
    next
      case 2
      then show ?thesis
        using \<open>0 \<in> h\<close> ab by auto
    next
      case 3
      have "S \<subset> \<Inter>(H - {h})"
        using Hsub [of "H - {h}"] that by auto
      then obtain x where x: "x \<in> \<Inter>(H - {h})" and "x \<notin> S"
        by auto
      define \<epsilon> where "\<epsilon> \<equiv> min (1/2) (b / (a \<bullet> x))"
      have "b < a \<bullet> x"
        using \<open>x \<notin> S\<close> ab x by (fastforce simp: \<open>S = \<Inter>H\<close>)
      with 3 have "0 < a \<bullet> x"
        by auto
      with 3 have "0 < \<epsilon>"
        by (simp add: \<epsilon>_def)
      have "\<epsilon> < 1"
        using \<epsilon>_def by linarith
      have "\<epsilon> * (a \<bullet> x) \<le> b"
        unfolding \<epsilon>_def using \<open>0 < a \<bullet> x\<close> pos_le_divide_eq by fastforce
      have "x = inverse \<epsilon> *\<^sub>R \<epsilon> *\<^sub>R x"
        using \<open>0 < \<epsilon>\<close> by force
      moreover 
      have "\<epsilon> *\<^sub>R x \<in> S"
      proof -
        have  "\<epsilon> *\<^sub>R x \<in> h"
          by (simp add: \<open>\<epsilon> * (a \<bullet> x) \<le> b\<close> ab)
        moreover have "\<epsilon> *\<^sub>R x \<in> \<Inter>(H - {h})"
        proof -
          have "\<epsilon> *\<^sub>R x \<in> k" if "x \<in> k" "k \<in> H" "k \<noteq> h" for k
          proof -
            obtain a' b' where "a'\<noteq>0" "k = {x. a' \<bullet> x \<le> b'}"
              using Hex \<open>k \<in> H\<close> by blast
            have "(0 \<le> a' \<bullet> x \<Longrightarrow> a' \<bullet> \<epsilon> *\<^sub>R x \<le> a' \<bullet> x)"
              by (metis \<open>\<epsilon> < 1\<close> inner_scaleR_right order_less_le pth_1 real_scaleR_def scaleR_right_mono)
            moreover have "(0 \<le> -(a' \<bullet> x) \<Longrightarrow> 0 \<le> -(a' \<bullet> \<epsilon> *\<^sub>R x)) "
              using \<open>0 < \<epsilon>\<close> mult_le_0_iff order_less_imp_le by auto
            ultimately
            have "a' \<bullet> x \<le> b' \<Longrightarrow> a' \<bullet> \<epsilon> *\<^sub>R x \<le> b'"
              by (smt (verit) InterD \<open>0 \<in> \<Inter>H\<close> \<open>k = {x. a' \<bullet> x \<le> b'}\<close> inner_zero_right mem_Collect_eq that(2))
            then show ?thesis
              using \<open>k = {x. a' \<bullet> x \<le> b'}\<close> \<open>x \<in> k\<close> by fastforce
          qed
          with x show ?thesis
            by blast
        qed
        ultimately show ?thesis
          using Seq by blast
      qed
      with \<open>conic S\<close> have "inverse \<epsilon> *\<^sub>R \<epsilon> *\<^sub>R x \<in> S"
        by (meson \<open>0 < \<epsilon>\<close> conic_def inverse_nonnegative_iff_nonnegative order_less_le)
      ultimately show ?thesis
        using \<open>x \<notin> S\<close> by presburger
    qed
  qed
  then obtain fa where fa: "\<And>h. h \<in> H \<Longrightarrow> fa h \<noteq> 0 \<and> h = {x. fa h \<bullet> x \<le> 0}"
    by metis
  define fa_le_0 where "fa_le_0 \<equiv> \<lambda>h. {x. fa h \<bullet> x \<le> 0}"
  have fa': "\<And>h. h \<in> H \<Longrightarrow> fa_le_0 h = h"
    using fa fa_le_0_def by blast
  define A where "A \<equiv> (\<lambda>h. (fa h,0::real)) ` H"
  have "finite A"
    using \<open>finite H\<close> by (simp add: A_def)
  then have "?lhs = Euler_characteristic A S"
  proof -
    have [simp]: "card {f. f face_of S \<and> aff_dim f = int d} = card {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}"
      if "finite A" and "d \<le> card (Basis::'n set)"
      for d :: nat
    proof (rule bij_betw_same_card)
      have hyper1: "hyperplane_cell A (rel_interior f) \<and> rel_interior f \<subseteq> S
          \<and> aff_dim (rel_interior f) = d \<and> closure (rel_interior f) = f" 
        if "f face_of S" "aff_dim f = d" for f
      proof -
        have 1: "closure(rel_interior f) = f" 
        proof -
          have "closure(rel_interior f) = closure f"
            by (meson convex_closure_rel_interior face_of_imp_convex that(1))
          also have "\<dots> = f"
            by (meson assms(1) closure_closed face_of_polyhedron_polyhedron polyhedron_imp_closed that(1))
          finally show ?thesis .
        qed
        then have 2: "aff_dim (rel_interior f) = d"
          by (metis closure_aff_dim that(2))
        have "f \<noteq> {}"
          using aff_dim_negative_iff [of f] by (simp add: that(2))
        obtain J0 where "J0 \<subseteq> H" and J0: "f = \<Inter> (fa_le_0 ` H) \<inter> (\<Inter>h \<in> J0. {x. fa h \<bullet> x = 0})"
        proof (cases "f = S")
          case True
          have "S = \<Inter> (fa_le_0 ` H)"
            using Seq fa by (auto simp: fa_le_0_def)
          then show ?thesis
            using True that by blast
        next
          case False
          have fexp: "f = \<Inter>{S \<inter> {x. fa h \<bullet> x = 0} | h. h \<in> H \<and> f \<subseteq> S \<inter> {x. fa h \<bullet> x = 0}}"
            proof (rule face_of_polyhedron_explicit)
              show "S = affine hull S \<inter> \<Inter> H"
                by (simp add: Seq hull_subset inf.absorb2)
            qed (auto simp: False \<open>f \<noteq> {}\<close> \<open>f face_of S\<close> \<open>finite H\<close> Hsub fa)
          show ?thesis
          proof
            have *: "\<And>x h. \<lbrakk>x \<in> f; h \<in> H\<rbrakk> \<Longrightarrow> fa h \<bullet> x \<le> 0"
              using Seq fa face_of_imp_subset \<open>f face_of S\<close> by fastforce
            show "f = \<Inter> (fa_le_0 ` H) \<inter> (\<Inter>h \<in> {h \<in> H.  f \<subseteq> S \<inter> {x. fa h \<bullet> x = 0}}. {x. fa h \<bullet> x = 0})"
                 (is "f = ?I")
            proof
              show "f \<subseteq> ?I"
                using \<open>f face_of S\<close> fa face_of_imp_subset by (force simp: * fa_le_0_def)
              show "?I \<subseteq> f"
              apply (subst (2) fexp)
              apply (clarsimp simp: * fa_le_0_def)
                by (metis Inter_iff Seq fa mem_Collect_eq)
            qed
          qed blast
        qed 
        define H' where "H' = (\<lambda>h. {x. -(fa h) \<bullet> x \<le> 0}) ` H"
        have "\<exists>J. finite J \<and> J \<subseteq> H \<union> H' \<and> f = affine hull f \<inter> \<Inter>J"
        proof (intro exI conjI)
          let ?J = "H \<union> image (\<lambda>h. {x. -(fa h) \<bullet> x \<le> 0}) J0"
          show "finite (?J::'n set set)"
            using \<open>J0 \<subseteq> H\<close> \<open>finite H\<close> finite_subset by fastforce
          show "?J \<subseteq> H \<union> H'"
            using \<open>J0 \<subseteq> H\<close> by (auto simp: H'_def)
          have "f = \<Inter>?J"
          proof
            show "f \<subseteq> \<Inter>?J"
              unfolding J0 by (auto simp: fa')
            have "\<And>x j. \<lbrakk>j \<in> J0; \<forall>h\<in>H. x \<in> h; \<forall>j\<in>J0. 0 \<le> fa j \<bullet> x\<rbrakk> \<Longrightarrow> fa j \<bullet> x = 0"
              by (metis \<open>J0 \<subseteq> H\<close> fa in_mono inf.absorb2 inf.orderE mem_Collect_eq)
            then show "\<Inter>?J \<subseteq> f"
              unfolding J0 by (auto simp: fa')
          qed
          then show "f = affine hull f \<inter> \<Inter>?J"
            by (simp add: Int_absorb1 hull_subset)
        qed 
        then have **: "\<exists>n J. finite J \<and> card J = n \<and> J \<subseteq> H \<union> H' \<and> f = affine hull f \<inter> \<Inter>J"
          by blast
        obtain J nJ where J: "finite J" "card J = nJ" "J \<subseteq> H \<union> H'" and feq: "f = affine hull f \<inter> \<Inter>J"
          and minJ:  "\<And>m J'. \<lbrakk>finite J'; m < nJ; card J' = m; J' \<subseteq> H \<union> H'\<rbrakk> \<Longrightarrow> f \<noteq> affine hull f \<inter> \<Inter>J'"
          using exists_least_iff [THEN iffD1, OF **] by metis
        have FF: "f \<subset> (affine hull f \<inter> \<Inter>J')" if "J' \<subset> J" for J'
        proof -
          have "f \<noteq> affine hull f \<inter> \<Inter>J'"
            using minJ
            by (metis J finite_subset psubset_card_mono psubset_imp_subset psubset_subset_trans that)
          then show ?thesis
            by (metis Int_subset_iff Inter_Un_distrib feq hull_subset inf_sup_ord(2) psubsetI sup.absorb4 that)
        qed
        have "\<exists>a. {x. a \<bullet> x \<le> 0} = h \<and> (h \<in> H \<and> a = fa h \<or> (\<exists>h'. h' \<in> H \<and> a = -(fa h')))" 
          if "h \<in> J" for h
        proof -
          have "h \<in> H \<union> H'"
            using \<open>J \<subseteq> H \<union> H'\<close> that by blast
          then show ?thesis
          proof
            show ?thesis if "h \<in> H"
              using that fa by blast
          next
            assume "h \<in> H'"
            then obtain h' where "h' \<in> H" "h = {x. 0 \<le> fa h' \<bullet> x}"
              by (auto simp: H'_def)
            then show ?thesis
              by (force simp: intro!: exI[where x="- (fa h')"])
          qed
        qed
        then obtain ga 
          where ga_h: "\<And>h. h \<in> J \<Longrightarrow> h = {x. ga h \<bullet> x \<le> 0}" 
            and ga_fa: "\<And>h. h \<in> J \<Longrightarrow> h \<in> H \<and> ga h = fa h \<or> (\<exists>h'. h' \<in> H \<and> ga h = -(fa h'))" 
          by metis
        have 3: "hyperplane_cell A (rel_interior f)"
        proof -
          have D: "rel_interior f = {x \<in> f. \<forall>h\<in>J. ga h \<bullet> x < 0}"
          proof (rule rel_interior_polyhedron_explicit [OF \<open>finite J\<close> feq])
            show "ga h \<noteq> 0 \<and> h = {x. ga h \<bullet> x \<le> 0}" if "h \<in> J" for h
              using that fa ga_fa ga_h by force
          qed (auto simp: FF)
          have H: "h \<in> H \<and> ga h = fa h" if "h \<in> J" for h
          proof -
            obtain z where z: "z \<in> rel_interior f"
              using "1" \<open>f \<noteq> {}\<close> by force
            then have "z \<in> f \<and> z \<in> S"
              using D \<open>f face_of S\<close> face_of_imp_subset by blast
            then show ?thesis
              using ga_fa [OF that]
              by (smt (verit, del_insts) D InterE Seq fa inner_minus_left mem_Collect_eq that z)
          qed
          then obtain K where "K \<subseteq> H" 
            and K: "f = \<Inter> (fa_le_0 ` H) \<inter> (\<Inter>h \<in> K. {x. fa h \<bullet> x = 0})"
            using J0 \<open>J0 \<subseteq> H\<close> by blast
          have E: "rel_interior f = {x. (\<forall>h \<in> H. fa h \<bullet> x \<le> 0) \<and> (\<forall>h \<in> K. fa h \<bullet> x = 0) \<and> (\<forall>h \<in> J. ga h \<bullet> x < 0)}"
            unfolding D by (simp add: K fa_le_0_def)
          have relif: "rel_interior f \<noteq> {}"
            using "1" \<open>f \<noteq> {}\<close> by force
          with E have "disjnt J K"
            using H disjnt_iff by fastforce
          define IFJK where "IFJK \<equiv> \<lambda>h. if h \<in> J then {x. fa h \<bullet> x < 0}
                         else if h \<in> K then {x. fa h \<bullet> x = 0}
                         else if rel_interior f \<subseteq> {x. fa h \<bullet> x = 0}
                         then {x. fa h \<bullet> x = 0}
                         else {x. fa h \<bullet> x < 0}"
          have relint_f: "rel_interior f = \<Inter>(IFJK ` H)" 
          proof
            have A: False 
              if x: "x \<in> rel_interior f" and y: "y \<in> rel_interior f" and less0: "fa h \<bullet> y < 0"
                and fa0:  "fa h \<bullet> x = 0" and "h \<in> H" "h \<notin> J" "h \<notin> K"  for x h y
            proof -
              obtain \<epsilon> where "x \<in> f" "\<epsilon>>0" 
                and \<epsilon>: "\<And>t. \<lbrakk>dist x t \<le> \<epsilon>; t \<in> affine hull f\<rbrakk> \<Longrightarrow> t \<in> f"
                using x by (force simp: mem_rel_interior_cball)
              then have "y \<noteq> x"
                using fa0 less0 by force
              define x' where "x' \<equiv> x + (\<epsilon> / norm(y - x)) *\<^sub>R (x - y)"
              have "x \<in> affine hull f \<and> y \<in> affine hull f"
                by (metis \<open>x \<in> f\<close> hull_inc mem_rel_interior_cball y)
              moreover have "dist x x' \<le> \<epsilon>"
                using \<open>0 < \<epsilon>\<close> \<open>y \<noteq> x\<close> by (simp add: x'_def divide_simps dist_norm norm_minus_commute)
              ultimately have "x' \<in> f"
                by (simp add: \<epsilon> mem_affine_3_minus x'_def)
              have "x' \<in> S"
                using \<open>f face_of S\<close> \<open>x' \<in> f\<close> face_of_imp_subset by auto
              then have "x' \<in> h"
                using Seq that(5) by blast
              then have "x' \<in> {x. fa h \<bullet> x \<le> 0}"
                using fa that(5) by blast
              moreover have "\<epsilon> / norm (y - x) * -(fa h \<bullet> y) > 0"
                using  \<open>0 < \<epsilon>\<close> \<open>y \<noteq> x\<close> less0 by (simp add: field_split_simps)
              ultimately show ?thesis
                by (simp add: x'_def fa0 inner_diff_right inner_right_distrib)
            qed
            show "rel_interior f \<subseteq> \<Inter>(IFJK ` H)"
              unfolding IFJK_def by (smt (verit, ccfv_SIG) A E H INT_I in_mono mem_Collect_eq subsetI)
            show "\<Inter>(IFJK ` H) \<subseteq> rel_interior f"
              using \<open>K \<subseteq> H\<close> \<open>disjnt J K\<close>
              apply (clarsimp simp add: ball_Un E H disjnt_iff IFJK_def)
              apply (smt (verit, del_insts) IntI Int_Collect subsetD)
              done
          qed
          obtain z where zrelf: "z \<in> rel_interior f"
            using relif by blast
          moreover
          have H: "z \<in> IFJK h \<Longrightarrow> (x \<in> IFJK h) = (hyperplane_side (fa h, 0) z = hyperplane_side (fa h, 0) x)" for h x
            using zrelf by (auto simp: IFJK_def hyperplane_side_def sgn_if split: if_split_asm)
          then have "z \<in> \<Inter>(IFJK ` H) \<Longrightarrow> (x \<in> \<Inter>(IFJK ` H)) = hyperplane_equiv A z x" for x
            unfolding A_def Inter_iff hyperplane_equiv_def ball_simps using H by blast
          then have "x \<in> rel_interior f \<longleftrightarrow> hyperplane_equiv A z x" for x
            using relint_f zrelf by presburger
          ultimately show ?thesis
            by (metis equalityI hyperplane_cell mem_Collect_eq subset_iff)
        qed
        have 4: "rel_interior f \<subseteq> S"
          by (meson face_of_imp_subset order_trans rel_interior_subset that(1))
        show ?thesis
          using "1" "2" "3" "4" by blast
      qed
      have hyper2: "(closure c face_of S \<and> aff_dim (closure c) = d) \<and> rel_interior (closure c) = c"
        if c: "hyperplane_cell A c" and "c \<subseteq> S" "aff_dim c = d" for c
      proof (intro conjI)
        obtain J where "J \<subseteq> H" and J: "c = (\<Inter>h \<in> J. {x. (fa h) \<bullet> x < 0}) \<inter> (\<Inter>h \<in> (H - J). {x. (fa h) \<bullet> x = 0})"
        proof -
          obtain z where z: "c = {y. \<forall>x \<in> H.  sgn (fa x \<bullet> y) = sgn (fa x \<bullet> z)}"
            using c by (force simp: hyperplane_cell A_def hyperplane_equiv_def hyperplane_side_def)
          show thesis
          proof
            let ?J = "{h \<in> H. sgn(fa h \<bullet> z) = -1}"
            have 1: "fa h \<bullet> x < 0"
              if "\<forall>h\<in>H. sgn (fa h \<bullet> x) = sgn (fa h \<bullet> z)" and "h \<in> H" and "sgn (fa h \<bullet> z) = - 1" for x h
              using that by (metis sgn_1_neg)
            have 2: "sgn (fa h \<bullet> z) = - 1"
              if "\<forall>h\<in>H. sgn (fa h \<bullet> x) = sgn (fa h \<bullet> z)" and "h \<in> H" and "fa h \<bullet> x \<noteq> 0" for x h
            proof -
              have "\<lbrakk>0 < fa h \<bullet> x; 0 < fa h \<bullet> z\<rbrakk> \<Longrightarrow> False"
                using that fa by (smt (verit, del_insts) Inter_iff Seq \<open>c \<subseteq> S\<close> mem_Collect_eq subset_iff z)
              then show ?thesis
                by (metis that sgn_if sgn_zero_iff)
            qed
            have 3: "sgn (fa h \<bullet> x) = sgn (fa h \<bullet> z)"
              if "h \<in> H" and "\<forall>h. h \<in> H \<and> sgn (fa h \<bullet> z) = - 1 \<longrightarrow> fa h \<bullet> x < 0"
                and "\<forall>h\<in>H - {h \<in> H. sgn (fa h \<bullet> z) = - 1}. fa h \<bullet> x = 0"
              for x h
              using that 2 by (metis (mono_tags, lifting) Diff_iff mem_Collect_eq sgn_neg)   
            show "c = (\<Inter>h \<in>?J. {x. fa h \<bullet> x < 0}) \<inter> (\<Inter>h\<in>H - ?J. {x. fa h \<bullet> x = 0})"
              unfolding z by (auto intro: 1 2 3)
          qed auto
        qed
        have "finite J"
          using \<open>J \<subseteq> H\<close> \<open>finite H\<close> finite_subset by blast
        show "closure c face_of S"
        proof -
          have cc: "closure c = closure (\<Inter>h\<in>J. {x. fa h \<bullet> x < 0}) \<inter> closure (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0})"
            unfolding J
          proof (rule closure_Int_convex)
            show "convex (\<Inter>h\<in>J. {x. fa h \<bullet> x < 0})"
              by (simp add: convex_INT convex_halfspace_lt)
            show "convex (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0})"
              by (simp add: convex_INT convex_hyperplane)
            have o1: "open (\<Inter>h\<in>J. {x. fa h \<bullet> x < 0})"
              by (metis open_INT[OF \<open>finite J\<close>] open_halfspace_lt)
            have o2: "openin (top_of_set (affine hull (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}))) (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0})"
            proof -
              have "affine (\<Inter>h\<in>H - J. {n. fa h \<bullet> n = 0})"
                using affine_hyperplane by auto
              then show ?thesis
                by (metis (no_types) affine_hull_eq openin_subtopology_self)
            qed
            show "rel_interior (\<Inter>h\<in>J. {x. fa h \<bullet> x < 0}) \<inter> rel_interior (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}) \<noteq> {}"
              by (metis nonempty_hyperplane_cell c rel_interior_open o1 rel_interior_openin o2 J)
          qed
          have clo_im_J: "closure ` ((\<lambda>h. {x. fa h \<bullet> x < 0}) ` J) = (\<lambda>h. {x. fa h \<bullet> x \<le> 0}) ` J"
            using \<open>J \<subseteq> H\<close> by (force simp: image_comp fa)
          have cleq: "closure (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}) = (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0})"
            by (intro closure_closed) (blast intro: closed_hyperplane)
          have **: "(\<Inter>h\<in>J. {x. fa h \<bullet> x \<le> 0}) \<inter> (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}) face_of S"
            if "(\<Inter>h\<in>J. {x. fa h \<bullet> x < 0}) \<noteq> {}"
          proof (cases "J=H")
            case True
            have [simp]: "(\<Inter>x\<in>H. {xa. fa x \<bullet> xa \<le> 0}) = \<Inter>H"
              using fa by auto
            show ?thesis
              using \<open>polyhedron S\<close> by (simp add: Seq True polyhedron_imp_convex face_of_refl)
          next
            case False
            have **: "(\<Inter>h\<in>J. {n. fa h \<bullet> n \<le> 0}) \<inter> (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}) =
                     (\<Inter>h\<in>H - J. S \<inter> {x. fa h \<bullet> x = 0})"  (is "?L = ?R")
            proof
              show "?L \<subseteq> ?R"
                by clarsimp (smt (verit) DiffI InterI Seq fa mem_Collect_eq)
              show "?R \<subseteq> ?L"
                using False Seq \<open>J \<subseteq> H\<close> fa by blast
            qed
            show ?thesis
              unfolding **
            proof (rule face_of_Inter)
              show "(\<lambda>h. S \<inter> {x. fa h \<bullet> x = 0}) ` (H - J) \<noteq> {}"
                using False \<open>J \<subseteq> H\<close> by blast
              show "T face_of S"
                if T: "T \<in> (\<lambda>h. S \<inter> {x. fa h \<bullet> x = 0}) ` (H - J)" for T
              proof -
                obtain h where h: "T = S \<inter> {x. fa h \<bullet> x = 0}" and "h \<in> H" "h \<notin> J"
                  using T by auto
                have "S \<inter> {x. fa h \<bullet> x = 0} face_of S"
                proof (rule face_of_Int_supporting_hyperplane_le)
                  show "convex S"
                    by (simp add: assms(1) polyhedron_imp_convex)
                  show "fa h \<bullet> x \<le> 0" if "x \<in> S" for x
                    using that Seq fa \<open>h \<in> H\<close> by auto
                qed
                then show ?thesis
                  using h by blast
              qed
            qed
          qed
          have *: "\<And>S. S \<in> (\<lambda>h. {x. fa h \<bullet> x < 0}) ` J \<Longrightarrow> convex S \<and> open S"
            using convex_halfspace_lt open_halfspace_lt by fastforce
          show ?thesis
            unfolding cc 
            apply (simp add: * closure_Inter_convex_open)
            by (metis "**" cleq clo_im_J image_image)
        qed
        show "aff_dim (closure c) = int d"
          by (simp add: that)
        show "rel_interior (closure c) = c"
          by (metis \<open>finite A\<close> c convex_rel_interior_closure hyperplane_cell_convex hyperplane_cell_relative_interior)
      qed
      have "rel_interior ` {f. f face_of S \<and> aff_dim f = int d} 
            = {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}"
        using hyper1 hyper2 by fastforce
      then show "bij_betw (rel_interior) {f. f face_of S \<and> aff_dim f = int d} {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}"
        unfolding bij_betw_def inj_on_def by (metis (mono_tags) hyper1 mem_Collect_eq) 
    qed
    show ?thesis
      by (simp add: Euler_characteristic \<open>finite A\<close>)
  qed
  also have "\<dots> = 0"
  proof -
    have A: "hyperplane_cellcomplex A (- h)" if "h \<in> H" for h
    proof (rule hyperplane_cellcomplex_mono [OF hyperplane_cell_cellcomplex])
      have "- h = {x. fa h \<bullet> x = 0} \<or> - h = {x. fa h \<bullet> x < 0} \<or> - h = {x. 0 < fa h \<bullet> x}"
        by (smt (verit, ccfv_SIG) Collect_cong Collect_neg_eq fa that)
      then show "hyperplane_cell {(fa h,0)} (- h)"
        by (simp add: hyperplane_cell_singleton fa that)
      show "{(fa h,0)} \<subseteq> A"
        by (simp add: A_def that)
    qed
    then have "\<And>h. h \<in> H \<Longrightarrow> hyperplane_cellcomplex A h"
      using hyperplane_cellcomplex_Compl by fastforce
    then have "hyperplane_cellcomplex A S"
      by (simp add: Seq hyperplane_cellcomplex_Inter)
    then have D: "Euler_characteristic A (UNIV::'n set) =
             Euler_characteristic A (\<Inter>H) + Euler_characteristic A (- \<Inter>H)"
      using Euler_characteristic_cellcomplex_Un 
      by (metis Compl_partition Diff_cancel Diff_eq Seq \<open>finite A\<close> disjnt_def hyperplane_cellcomplex_Compl)
    have "Euler_characteristic A UNIV = Euler_characteristic {} (UNIV::'n set)"
      by (simp add: Euler_characterstic_invariant \<open>finite A\<close>)
    then have E: "Euler_characteristic A UNIV = (-1) ^ (DIM('n))"
      by (simp add: Euler_characteristic_cell)
    have DD: "Euler_characteristic A (\<Inter> (uminus ` J)) = (- 1) ^ DIM('n)"
      if "J \<noteq> {}" "J \<subseteq> H" for J
    proof -
      define B where "B \<equiv> (\<lambda>h. (fa h,0::real)) ` J"
      then have "B \<subseteq> A"
        by (simp add: A_def image_mono that)
      have "\<exists>x. y = -x" if "y \<in> \<Inter> (uminus ` H)" for y::'n  \<comment> \<open>Weirdly, the assumption is not used\<close>
        by (metis add.inverse_inverse)
      moreover have "-x \<in> \<Inter> (uminus ` H) \<longleftrightarrow> x \<in> interior S" for x
      proof -
        have 1: "interior S = {x \<in> S. \<forall>h\<in>H. fa h \<bullet> x < 0}"
          using rel_interior_polyhedron_explicit [OF \<open>finite H\<close> _ fa]
          by (metis (no_types, lifting) inf_top_left  Hsub Seq \<open>affine hull S = UNIV\<close> rel_interior_interior)
        have 2: "\<And>x y. \<lbrakk>y \<in> H; \<forall>h\<in>H. fa h \<bullet> x < 0; - x \<in> y\<rbrakk> \<Longrightarrow> False" 
          by (smt (verit, best) fa inner_minus_right mem_Collect_eq)
        show ?thesis
          apply (simp add: 1)
          by (smt (verit) 2 * fa Inter_iff Seq inner_minus_right mem_Collect_eq)
      qed
      ultimately have INT_Compl_H: "\<Inter> (uminus ` H) = uminus ` interior S"
        by blast
      obtain z where z: "z \<in> \<Inter> (uminus ` J)" 
        using \<open>J \<subseteq> H\<close> \<open>\<Inter> (uminus ` H) = uminus ` interior S\<close> intS by fastforce
      have "\<Inter> (uminus ` J) = Collect (hyperplane_equiv B z)" (is "?L = ?R")
      proof
        show "?L \<subseteq> ?R"
          using fa \<open>J \<subseteq> H\<close> z 
          by (fastforce simp: hyperplane_equiv_def hyperplane_side_def B_def set_eq_iff )
        show "?R \<subseteq> ?L"
          using z \<open>J \<subseteq> H\<close> apply (clarsimp simp add: hyperplane_equiv_def hyperplane_side_def B_def)
          by (metis fa in_mono mem_Collect_eq sgn_le_0_iff)
      qed
      then have hyper_B: "hyperplane_cell B (\<Inter> (uminus ` J))"
        by (metis hyperplane_cell)
      have "Euler_characteristic A (\<Inter> (uminus ` J)) = Euler_characteristic B (\<Inter> (uminus ` J))"
      proof (rule Euler_characterstic_invariant [OF \<open>finite A\<close>])
        show "finite B"
          using \<open>B \<subseteq> A\<close> \<open>finite A\<close> finite_subset by blast
        show "hyperplane_cellcomplex A (\<Inter> (uminus ` J))"
          by (meson \<open>B \<subseteq> A\<close> hyper_B hyperplane_cell_cellcomplex hyperplane_cellcomplex_mono)
        show "hyperplane_cellcomplex B (\<Inter> (uminus ` J))"
          by (simp add: hyper_B hyperplane_cell_cellcomplex)
      qed
      also have "\<dots> = (- 1) ^ nat (aff_dim (\<Inter> (uminus ` J)))"
        using Euler_characteristic_cell hyper_B by blast
      also have "\<dots> = (- 1) ^ DIM('n)"
      proof -
        have "affine hull \<Inter> (uminus ` H) = UNIV"
          by (simp add: INT_Compl_H affine_hull_nonempty_interior intS interior_negations)
        then have "affine hull \<Inter> (uminus ` J) = UNIV"
          by (metis Inf_superset_mono hull_mono subset_UNIV subset_antisym subset_image_iff that(2))
        with aff_dim_eq_full show ?thesis
          by (metis nat_int)
      qed
      finally show ?thesis .
    qed
    have EE: "(\<Sum>\<T> | \<T> \<subseteq> uminus ` H \<and> \<T>\<noteq>{}. (-1) ^ (card \<T> + 1) * Euler_characteristic A (\<Inter>\<T>))
             = (\<Sum>\<T> | \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}. (-1) ^ (card \<T> + 1) * (- 1) ^ DIM('n))"
      by (intro sum.cong [OF refl]) (fastforce simp: subset_image_iff intro!: DD)
    also have "\<dots> = (-1) ^ DIM('n)"
    proof -
      have A: "(\<Sum>y = 1..card H. \<Sum>t\<in>{x \<in> {\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}}. card x = y}. (- 1) ^ (card t + 1)) 
          = (\<Sum>\<T>\<in>{\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}}. (- 1) ^ (card \<T> + 1))"
      proof (rule sum.group)
        have "\<And>C. \<lbrakk>C \<subseteq> uminus ` H; C \<noteq> {}\<rbrakk> \<Longrightarrow> Suc 0 \<le> card C \<and> card C \<le> card H"
          by (meson \<open>finite H\<close> card_eq_0_iff finite_surj le_zero_eq not_less_eq_eq surj_card_le)
        then show "card ` {\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}} \<subseteq> {1..card H}"
          by force
      qed (auto simp: \<open>finite H\<close>)

      have "(\<Sum>n = Suc 0..card H. - (int (card {x. x \<subseteq> uminus ` H \<and> x \<noteq> {} \<and> card x = n}) * (- 1) ^ n))
          = (\<Sum>n = Suc 0..card H. (-1) ^ (Suc n) * (card H choose n))"
      proof (rule sum.cong [OF refl])
        fix n
        assume "n \<in> {Suc 0..card H}"
        then have "{\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {} \<and> card \<T> = n} = {\<T>. \<T> \<subseteq> uminus ` H \<and> card \<T> = n}"
          by auto
        then have "card{\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {} \<and> card \<T> = n} = card (uminus ` H) choose n"
          by (simp add: \<open>finite H\<close> n_subsets)
        also have "\<dots> = card H choose n"
          by (metis card_image double_complement inj_on_inverseI)
        finally
        show "- (int (card {\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {} \<and> card \<T> = n}) * (- 1) ^ n) = (- 1) ^ Suc n * int (card H choose n)"
          by simp
      qed
      also have "\<dots> = - (\<Sum>k = Suc 0..card H. (-1) ^ k * (card H choose k))"
        by (simp add: sum_negf)
      also have "\<dots> = 1 - (\<Sum>k=0..card H. (-1) ^ k * (card H choose k))"
        using atLeastSucAtMost_greaterThanAtMost by (simp add: sum.head [of 0])
      also have "\<dots> = 1 - 0 ^ card H"
        using binomial_ring [of "-1" "1::int" "card H"] by (simp add: mult.commute atLeast0AtMost)
      also have "\<dots> = 1"
        using Seq \<open>finite H\<close> \<open>S \<noteq> UNIV\<close> card_0_eq by auto
      finally have C: "(\<Sum>n = Suc 0..card H. - (int (card {x. x \<subseteq> uminus ` H \<and> x \<noteq> {} \<and> card x = n}) * (- 1) ^ n)) = (1::int)" .

      have "(\<Sum>\<T> | \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}. (- 1) ^ (card \<T> + 1)) = (1::int)"
        unfolding A [symmetric] by (simp add: C)
      then show ?thesis
        by (simp flip: sum_distrib_right power_Suc)
    qed
    finally have "(\<Sum>\<T> | \<T> \<subseteq> uminus ` H \<and> \<T>\<noteq>{}. (-1) ^ (card \<T> + 1) * Euler_characteristic A (\<Inter>\<T>))
             = (-1) ^ DIM('n)" .
    then have  "Euler_characteristic A (\<Union> (uminus ` H)) = (-1) ^ (DIM('n))"
      using Euler_characteristic_inclusion_exclusion [OF \<open>finite A\<close>]
      by (smt (verit) A Collect_cong \<open>finite H\<close> finite_imageI image_iff sum.cong)
    then show ?thesis
      using D E by (simp add: uminus_Inf Seq)
  qed
  finally show ?thesis .
qed



subsection \<open>Euler-Poincare relation for special $(n-1)$-dimensional polytope\<close>

lemma Euler_Poincare_lemma:
  fixes p :: "'n::euclidean_space set"
  assumes "DIM('n) \<ge> 2" "polytope p" "i \<in> Basis" and affp: "affine hull p = {x. x \<bullet> i = 1}"
  shows "(\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * int (card {f. f face_of p \<and> aff_dim f = int d})) = 1"
proof -
  have "aff_dim p = aff_dim {x. i \<bullet> x = 1}"
    by (metis (no_types, lifting) Collect_cong aff_dim_affine_hull affp inner_commute)
  also have "... = int (DIM('n) - 1)"
    using aff_dim_hyperplane [of i 1] \<open>i \<in> Basis\<close> by fastforce
  finally have AP: "aff_dim p = int (DIM('n) - 1)" .
  show ?thesis
  proof (cases "p = {}")
    case True
    with AP show ?thesis by simp
  next
    case False
    define S where "S \<equiv> conic hull p"
    have 1: "(conic hull f) \<inter> {x. x \<bullet> i = 1} = f" if "f \<subseteq> {x. x \<bullet> i = 1}" for f
      using that
      by (smt (verit, ccfv_threshold) affp conic_hull_Int_affine_hull hull_hull inner_zero_left mem_Collect_eq)
    obtain K where "finite K" and K: "p = convex hull K"
      by (meson assms(2) polytope_def)
    then have "convex_cone hull K = conic hull (convex hull K)"
      using False convex_cone_hull_separate_nonempty by auto
    then have "polyhedron S"
      using polyhedron_convex_cone_hull
      by (simp add: S_def \<open>polytope p\<close> polyhedron_conic_hull_polytope)
    then have "convex S"
      by (simp add: polyhedron_imp_convex)
    then have "conic S"
      by (simp add: S_def conic_conic_hull)
    then have "0 \<in> S"
      by (simp add: False S_def)
    have "S \<noteq> UNIV"
    proof
      assume "S = UNIV"
      then have "conic hull p \<inter> {x. x\<bullet>i = 1} = p"
        by (metis "1" affp hull_subset)
      then have "bounded {x. x \<bullet> i = 1}"
        using S_def \<open>S = UNIV\<close> assms(2) polytope_imp_bounded by auto
      then obtain B where "B>0" and B: "\<And>x. x \<in> {x. x \<bullet> i = 1} \<Longrightarrow> norm x \<le> B"
        using bounded_normE by blast
      define x where "x \<equiv> (\<Sum>b\<in>Basis. (if b=i then 1 else B+1) *\<^sub>R b)"
      obtain j where j: "j \<in> Basis" "j\<noteq>i"
        using \<open>DIM('n) \<ge> 2\<close>
        by (metis DIM_complex DIM_ge_Suc0 card_2_iff' card_le_Suc0_iff_eq euclidean_space_class.finite_Basis le_antisym)
      have "B+1 \<le> \<bar>x \<bullet> j\<bar>"
        using j by (simp add: x_def)
      also have "\<dots> \<le> norm x"
        using Basis_le_norm j by blast
      finally have "norm x > B"
        by simp
      moreover have "x \<bullet> i = 1"
        by (simp add: x_def \<open>i \<in> Basis\<close>)
      ultimately show False
        using B by force
    qed
    have "S \<noteq> {}"
      by (metis False S_def empty_subsetI equalityI hull_subset)
    have "\<And>c x. \<lbrakk>0 < c; x \<in> p; x \<noteq> 0\<rbrakk> \<Longrightarrow> 0 < (c *\<^sub>R x) \<bullet> i"
      by (metis (mono_tags) Int_Collect Int_iff affp hull_inc inner_commute inner_scaleR_right mult.right_neutral)
    then have doti_gt0: "0 < x \<bullet> i" if S: "x \<in> S" and "x \<noteq> 0" for x
      using that by (auto simp: S_def conic_hull_explicit)
    have "\<And>a. {a} face_of S \<Longrightarrow> a = 0"
      using \<open>conic S\<close> conic_contains_0 face_of_conic by blast
    moreover have "{0} face_of S"
    proof -
      have "\<And>a b u. \<lbrakk>a \<in> S; b \<in> S; a \<noteq> b; u < 1; 0 < u; (1 - u) *\<^sub>R a + u *\<^sub>R b = 0\<rbrakk> \<Longrightarrow> False"
        using conic_def euclidean_all_zero_iff inner_left_distrib scaleR_eq_0_iff
        by (smt (verit, del_insts) doti_gt0 \<open>conic S\<close> \<open>i \<in> Basis\<close>)
      then show ?thesis
        by (auto simp: in_segment face_of_singleton extreme_point_of_def \<open>0 \<in> S\<close>)
    qed
    ultimately have face_0: "{f. f face_of S \<and> (\<exists>a. f = {a})} = {{0}}"
      by auto
    have "interior S \<noteq> {}"
    proof
      assume "interior S = {}"
      then obtain a b where "a \<noteq> 0" and ab: "S \<subseteq> {x. a \<bullet> x = b}"
        by (metis \<open>convex S\<close> empty_interior_subset_hyperplane)
      have "{x. x \<bullet> i = 1} \<subseteq> {x. a \<bullet> x = b}"
        by (metis S_def ab affine_hyperplane affp hull_inc subset_eq subset_hull)
      moreover have "\<not> {x. x \<bullet> i = 1} \<subset> {x. a \<bullet> x = b}"
        using aff_dim_hyperplane [of a b]
        by (metis AP \<open>a \<noteq> 0\<close> aff_dim_eq_full_gen affine_hyperplane affp hull_subset less_le_not_le subset_hull)
      ultimately have "S \<subseteq> {x. x \<bullet> i = 1}"
        using ab by auto
      with \<open>S \<noteq> {}\<close> show False
        using \<open>conic S\<close> conic_contains_0 by fastforce
    qed
    then have "(\<Sum>d = 0..DIM('n). (-1) ^ d * int (card {f. f face_of S \<and> aff_dim f = int d})) = 0"
      using Euler_polyhedral_cone \<open>S \<noteq> UNIV\<close> \<open>conic S\<close> \<open>polyhedron S\<close> by blast
    then have "1 + (\<Sum>d = 1..DIM('n). (-1) ^ d * (card {f. f face_of S \<and> aff_dim f = d})) = 0"
      by (simp add: sum.atLeast_Suc_atMost aff_dim_eq_0 face_0)
    moreover have "(\<Sum>d = 1..DIM('n). (-1) ^ d * (card {f. f face_of S \<and> aff_dim f = d}))
                 = - (\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * int (card {f. f face_of p \<and> aff_dim f = int d}))"
    proof -
      have "(\<Sum>d = 1..DIM('n). (-1) ^ d * (card {f. f face_of S \<and> aff_dim f = d}))
          = (\<Sum>d = Suc 0..Suc (DIM('n)-1). (-1) ^ d * (card {f. f face_of S \<and> aff_dim f = d}))"
        by auto
      also have "... = - (\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of S \<and> aff_dim f = 1 + int d})"
        unfolding sum.atLeast_Suc_atMost_Suc_shift by (simp add: sum_negf)
      also have "... = - (\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of p \<and> aff_dim f = int d})"
      proof -
        { fix d
          assume "d \<le> DIM('n) - Suc 0"
          have conic_face_p: "(conic hull f) face_of S" if "f face_of p" for f
          proof (cases "f={}")
            case False
            have "{c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> f} \<subseteq> {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> p}"
              using face_of_imp_subset that by blast
            moreover
            have "convex {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> f}"
              by (metis (no_types) cone_hull_expl convex_cone_hull face_of_imp_convex that)
            moreover
            have "(\<exists>c x. ca *\<^sub>R a = c *\<^sub>R x \<and> 0 \<le> c \<and> x \<in> f) \<and> (\<exists>c x. cb *\<^sub>R b = c *\<^sub>R x \<and> 0 \<le> c \<and> x \<in> f)"
              if "\<forall>a\<in>p. \<forall>b\<in>p. (\<exists>x\<in>f. x \<in> open_segment a b) \<longrightarrow> a \<in> f \<and> b \<in> f"
                and "0 \<le> ca" "a \<in> p" "0 \<le> cb" "b \<in> p"
                and "0 \<le> cx" "x \<in> f" and oseg: "cx *\<^sub>R x \<in> open_segment (ca *\<^sub>R a) (cb *\<^sub>R b)"
              for ca a cb b cx x
            proof -
              have ai: "a \<bullet> i = 1" and bi: "b \<bullet> i = 1"
                using affp hull_inc that(3,5) by fastforce+
              have xi: "x \<bullet> i = 1"
                using affp that \<open>f face_of p\<close> face_of_imp_subset hull_subset by fastforce
              show ?thesis
              proof (cases "cx *\<^sub>R x = 0")
                case True
                then show ?thesis
                  using \<open>{0} face_of S\<close> face_ofD \<open>conic S\<close> that
                  by (smt (verit, best) S_def conic_def hull_subset insertCI singletonD subsetD)
              next
                case False
                then have "cx \<noteq> 0" "x \<noteq> 0"
                  by auto
                obtain u where "0 < u" "u < 1" and u: "cx *\<^sub>R x = (1 - u) *\<^sub>R (ca *\<^sub>R a) + u *\<^sub>R (cb *\<^sub>R b)"
                  using oseg in_segment(2) by metis
                show ?thesis
                proof (cases "x = a")
                  case True
                  then have ua: "(cx - (1 - u) * ca) *\<^sub>R a = (u * cb) *\<^sub>R b"
                    using u by (simp add: algebra_simps)
                  then have "(cx - (1 - u) * ca) * 1 = u * cb * 1"
                    by (metis ai bi inner_scaleR_left)
                  then have "a=b \<or> cb = 0"
                    using ua \<open>0 < u\<close> by force
                  then show ?thesis
                    by (metis True scaleR_zero_left that(2) that(4) that(7))
                next
                  case False
                  show ?thesis
                  proof (cases "x = b")
                    case True
                    then have ub: "(cx - (u * cb)) *\<^sub>R b = ((1 - u) * ca) *\<^sub>R a"
                      using u by (simp add: algebra_simps)
                    then have "(cx - (u * cb)) * 1 = ((1 - u) * ca) * 1"
                      by (metis ai bi inner_scaleR_left)
                    then have "a=b \<or> ca = 0"
                      using \<open>u < 1\<close> ub by auto
                    then show ?thesis
                      using False True that(4) that(7) by auto
                  next
                    case False
                    have "cx > 0"
                      using \<open>cx \<noteq> 0\<close> \<open>0 \<le> cx\<close> by linarith
                    have False if "ca = 0"
                    proof -
                      have "cx = u * cb"
                        by (metis add_0 bi inner_real_def inner_scaleR_left real_inner_1_right scale_eq_0_iff that u xi)
                      then show False
                        using \<open>x \<noteq> b\<close> \<open>cx \<noteq> 0\<close> that u by force
                    qed
                    with \<open>0 \<le> ca\<close> have "ca > 0"
                      by force
                    have aff: "x \<in> affine hull p \<and> a \<in> affine hull p \<and> b \<in> affine hull p"
                      using affp xi ai bi by blast
                    show ?thesis
                    proof (cases "cb=0") 
                      case True
                      have u': "cx *\<^sub>R x = ((1 - u) * ca) *\<^sub>R a"
                        using u by (simp add: True)
                      then have "cx = ((1 - u) * ca)"
                        by (metis ai inner_scaleR_left mult.right_neutral xi)
                      then show ?thesis
                        using True u' \<open>cx \<noteq> 0\<close> \<open>ca \<ge> 0\<close> \<open>x \<in> f\<close> by auto
                    next
                      case False
                      with \<open>cb \<ge> 0\<close> have "cb > 0"
                        by linarith
                      { have False if "a=b"
                        proof -
                          have *: "cx *\<^sub>R x = ((1 - u) * ca + u * cb) *\<^sub>R b"
                            using u that by (simp add: algebra_simps)
                          then have "cx = ((1 - u) * ca + u * cb)"
                            by (metis xi bi inner_scaleR_left mult.right_neutral)
                          with \<open>x \<noteq> b\<close> \<open>cx \<noteq> 0\<close> * show False
                            by force
                        qed
                      }
                      moreover 
                      have "cx *\<^sub>R x /\<^sub>R cx = (((1 - u) * ca) *\<^sub>R a + (cb * u) *\<^sub>R b) /\<^sub>R cx"
                        using u by simp
                      then have xeq: "x = ((1-u) * ca / cx) *\<^sub>R a + (cb * u / cx) *\<^sub>R b"
                        by (simp add: \<open>cx \<noteq> 0\<close> divide_inverse_commute scaleR_right_distrib)
                      then have proj: "1 = ((1-u) * ca / cx) + (cb * u / cx)"
                        using ai bi xi by (simp add: inner_left_distrib)
                      then have eq: "cx + ca * u = ca + cb * u"
                        using \<open>cx > 0\<close> by (simp add: field_simps)
                      have "\<exists>u>0. u < 1 \<and> x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
                      proof (intro exI conjI)
                        show "0 < inverse cx * u * cb"
                          by (simp add: \<open>0 < cb\<close> \<open>0 < cx\<close> \<open>0 < u\<close>)
                        show "inverse cx * u * cb < 1"
                          using proj \<open>0 < ca\<close> \<open>0 < cx\<close> \<open>u < 1\<close> by (simp add: divide_simps)
                        show "x = (1 - inverse cx * u * cb) *\<^sub>R a + (inverse cx * u * cb) *\<^sub>R b"
                          using eq \<open>cx \<noteq> 0\<close> by (simp add: xeq field_simps)
                      qed
                      ultimately show ?thesis
                        using that by (metis in_segment(2))
                    qed
                  qed
                qed
              qed
            qed
            ultimately show ?thesis
              using that by (auto simp: S_def conic_hull_explicit face_of_def)
          qed auto
          moreover
          have conic_hyperplane_eq: "conic hull (f \<inter> {x. x \<bullet> i = 1}) = f"
            if "f face_of S" "0 < aff_dim f" for f
          proof
            show "conic hull (f \<inter> {x. x \<bullet> i = 1}) \<subseteq> f"
              by (metis \<open>conic S\<close> face_of_conic inf_le1 subset_hull that(1))
            have "\<exists>c x'. x = c *\<^sub>R x' \<and> 0 \<le> c \<and> x' \<in> f \<and> x' \<bullet> i = 1" if "x \<in> f" for x
            proof (cases "x=0")
              case True
              obtain y where "y \<in> f" "y \<noteq> 0"
                by (metis \<open>0 < aff_dim f\<close> aff_dim_sing aff_dim_subset insertCI linorder_not_le subset_iff)
              then have "y \<bullet> i > 0"
                using \<open>f face_of S\<close> doti_gt0 face_of_imp_subset by blast
              then have "y /\<^sub>R (y \<bullet> i) \<in> f \<and> (y /\<^sub>R (y \<bullet> i)) \<bullet> i = 1"
                using \<open>conic S\<close> \<open>f face_of S\<close> \<open>y \<in> f\<close> conic_def face_of_conic by fastforce
              then show ?thesis
                using True by fastforce
            next
              case False
              then have "x \<bullet> i > 0"
                using \<open>f face_of S\<close> doti_gt0 face_of_imp_subset that by blast
              then have "x /\<^sub>R (x \<bullet> i) \<in> f \<and> (x /\<^sub>R (x \<bullet> i)) \<bullet> i = 1"
                using \<open>conic S\<close> \<open>f face_of S\<close> \<open>x \<in> f\<close> conic_def face_of_conic by fastforce
              then show ?thesis
                by (metis \<open>0 < x \<bullet> i\<close> divideR_right eucl_less_le_not_le)
            qed
            then show "f \<subseteq> conic hull (f \<inter> {x. x \<bullet> i = 1})"
              by (auto simp: conic_hull_explicit)
          qed

          have conic_face_S: "conic hull f face_of S" 
            if "f face_of S" for f
            by (metis \<open>conic S\<close> face_of_conic hull_same that)

          have aff_1d: "aff_dim (conic hull f) = aff_dim f + 1" (is "?lhs = ?rhs")
            if "f face_of p" and "f \<noteq> {}" for f
          proof (rule order_antisym)
            have "?lhs \<le> aff_dim(affine hull (insert 0 (affine hull f)))"
            proof (intro aff_dim_subset hull_minimal)
              show "f \<subseteq> affine hull insert 0 (affine hull f)"
                by (metis hull_insert hull_subset insert_subset)
              show "conic (affine hull insert 0 (affine hull f))"
                by (metis affine_hull_span_0 conic_span hull_inc insertI1)
            qed
            also have "\<dots> \<le> ?rhs"
              by (simp add: aff_dim_insert)
            finally show "?lhs \<le> ?rhs" .
            have "aff_dim f < aff_dim (conic hull f)"
            proof (intro aff_dim_psubset psubsetI)
              show "affine hull f \<subseteq> affine hull (conic hull f)"
                by (simp add: hull_mono hull_subset)
              have "0 \<notin> affine hull f"
                using affp face_of_imp_subset hull_mono that(1) by fastforce
              moreover have "0 \<in> affine hull (conic hull f)"
                by (simp add: \<open>f \<noteq> {}\<close> hull_inc)
              ultimately show "affine hull f \<noteq> affine hull (conic hull f)"
                by auto
            qed
            then show "?rhs \<le> ?lhs"
              by simp
          qed 

          have face_S_imp_face_p: "\<And>f. f face_of S \<Longrightarrow>  f \<inter> {x. x \<bullet> i = 1} face_of p"
            by (metis "1" S_def affp convex_affine_hull face_of_slice hull_subset)

          have conic_eq_f: "conic hull f \<inter> {x. x \<bullet> i = 1} = f"
            if "f face_of p" for f
            by (metis "1" affp face_of_imp_subset hull_subset le_inf_iff that)

          have dim_f_hyperplane: "aff_dim (f \<inter> {x. x \<bullet> i = 1}) = int d"
            if "f face_of S" "aff_dim f = 1 + int d" for f
          proof -
            have "conic f"
              using \<open>conic S\<close> face_of_conic that(1) by blast
            then have "0 \<in> f"
              using conic_contains_0 that by force
            moreover have "\<not> f \<subseteq> {0}"
              using subset_singletonD that(2) by fastforce
            ultimately obtain y where y: "y \<in> f" "y \<noteq> 0"
              by blast
            then have "y \<bullet> i > 0"
              using doti_gt0 face_of_imp_subset that(1) by blast
            have "aff_dim (conic hull (f \<inter> {x. x \<bullet> i = 1})) = aff_dim (f \<inter> {x. x \<bullet> i = 1}) + 1"
            proof (rule aff_1d)
              show "f \<inter> {x. x \<bullet> i = 1} face_of p"
                by (simp add: face_S_imp_face_p that(1))
              have "inverse(y \<bullet> i) *\<^sub>R y \<in> f"
                using \<open>0 < y \<bullet> i\<close> \<open>conic S\<close> conic_mul face_of_conic that(1) y(1) by fastforce
              moreover have "inverse(y \<bullet> i) *\<^sub>R y \<in> {x. x \<bullet> i = 1}"
                using \<open>y \<bullet> i > 0\<close> by (simp add: field_simps)
              ultimately show "f \<inter> {x. x \<bullet> i = 1} \<noteq> {}"
                by blast
            qed
            then show ?thesis
              by (simp add: conic_hyperplane_eq that)
          qed
          have "card {f. f face_of S \<and> aff_dim f = 1 + int d}
             =  card {f. f face_of p \<and> aff_dim f = int d}"
          proof (intro bij_betw_same_card bij_betw_imageI)
            show "inj_on (\<lambda>f. f \<inter> {x. x \<bullet> i = 1}) {f. f face_of S \<and> aff_dim f = 1 + int d}"
              by (smt (verit) conic_hyperplane_eq inj_on_def mem_Collect_eq of_nat_less_0_iff)     
            show "(\<lambda>f. f \<inter> {x. x \<bullet> i = 1}) ` {f. f face_of S \<and> aff_dim f = 1 + int d} = {f. f face_of p \<and> aff_dim f = int d}"
              using aff_1d conic_eq_f conic_face_p
              by (fastforce simp: image_iff face_S_imp_face_p dim_f_hyperplane)
          qed
        }
        then show ?thesis
          by force
      qed
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by auto
  qed
qed


corollary Euler_poincare_special:
  fixes p :: "'n::euclidean_space set"
  assumes "2 \<le> DIM('n)" "polytope p" "i \<in> Basis" and affp: "affine hull p = {x. x \<bullet> i = 0}"
  shows "(\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of p \<and> aff_dim f = d}) = 1"
proof -
  { fix d
    have eq: "image((+) i) ` {f. f face_of p} \<inter> image((+) i) ` {f. aff_dim f = int d}
             = image((+) i) ` {f. f face_of p} \<inter> {f. aff_dim f = int d}"
      by (auto simp: aff_dim_translation_eq)
    have "card {f. f face_of p \<and> aff_dim f = int d} = card (image((+) i) ` {f. f face_of p \<and> aff_dim f = int d})"
      by (simp add: inj_on_image card_image)
    also have "\<dots>  = card (image((+) i) ` {f. f face_of p} \<inter> {f. aff_dim f = int d})"
      by (simp add: Collect_conj_eq image_Int inj_on_image eq)
    also have "\<dots> = card {f. f face_of (+) i ` p \<and> aff_dim f = int d}"
      by (simp add: Collect_conj_eq faces_of_translation)
    finally have "card {f. f face_of p \<and> aff_dim f = int d} = card {f. f face_of (+) i ` p \<and> aff_dim f = int d}" .
  } 
  then
  have "(\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of p \<and> aff_dim f = d})
      = (\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of (+) i ` p \<and> aff_dim f = int d})"
    by simp
  also have "\<dots> = 1"
  proof (rule Euler_Poincare_lemma)
    have "\<And>x. \<lbrakk>i \<in> Basis; x \<bullet> i = 1\<rbrakk> \<Longrightarrow> \<exists>y. y \<bullet> i = 0 \<and> x = y + i"
      by (metis add_cancel_left_left eq_diff_eq inner_diff_left inner_same_Basis)
    then show "affine hull (+) i ` p = {x. x \<bullet> i = 1}"
      using \<open>i \<in> Basis\<close> unfolding affine_hull_translation affp by (auto simp: algebra_simps)
  qed (use assms polytope_translation_eq in auto)
  finally show ?thesis .
qed


subsection \<open>Now Euler-Poincare for a general full-dimensional polytope\<close>

theorem Euler_Poincare_full:
  fixes p :: "'n::euclidean_space set"
  assumes "polytope p" "aff_dim p = DIM('n)"
  shows "(\<Sum>d = 0..DIM('n). (-1) ^ d * (card {f. f face_of p \<and> aff_dim f = d})) = 1"
proof -
  define augm:: "'n \<Rightarrow> 'n \<times> real" where "augm \<equiv> \<lambda>x. (x,0)"
  define S where "S \<equiv> augm ` p"
  obtain i::'n where i: "i \<in> Basis"
    by (meson SOME_Basis)
  have "bounded_linear augm"
    by (auto simp: augm_def bounded_linearI')
  then have "polytope S"
    unfolding S_def using polytope_linear_image \<open>polytope p\<close> bounded_linear.linear by blast
  have face_pS: "\<And>F. F face_of p \<longleftrightarrow> augm ` F face_of S"
    using S_def \<open>bounded_linear augm\<close> augm_def bounded_linear.linear face_of_linear_image inj_on_def by blast
  have aff_dim_eq[simp]: "aff_dim (augm ` F) = aff_dim F" for F
    using \<open>bounded_linear augm\<close> aff_dim_injective_linear_image bounded_linear.linear 
    unfolding augm_def inj_on_def by blast
  have *: "{F. F face_of S \<and> aff_dim F = int d} = (image augm) ` {F. F face_of p \<and> aff_dim F = int d}"
            (is "?lhs = ?rhs") for d
  proof
    have "\<And>G. \<lbrakk>G face_of S; aff_dim G = int d\<rbrakk>
         \<Longrightarrow> \<exists>F. F face_of p \<and> aff_dim F = int d \<and> G = augm ` F"
      by (metis face_pS S_def aff_dim_eq face_of_imp_subset subset_imageE)
    then show "?lhs \<subseteq> ?rhs"
      by (auto simp: image_iff)
  qed (auto simp: image_iff face_pS)
  have ceqc: "card {f. f face_of S \<and> aff_dim f = int d} = card {f. f face_of p \<and> aff_dim f = int d}" for d
    unfolding *
    by (rule card_image) (auto simp: inj_on_def augm_def)
  have "(\<Sum>d = 0..DIM('n \<times> real) - 1. (- 1) ^ d * int (card {f. f face_of S \<and> aff_dim f = int d})) = 1"
  proof (rule Euler_poincare_special)
    show "2 \<le> DIM('n \<times> real)"
      by auto
    have snd0: "(a, b) \<in> affine hull S \<Longrightarrow> b = 0" for a b
      using S_def \<open>bounded_linear augm\<close> affine_hull_linear_image augm_def by blast
    moreover have "\<And>a. (a, 0) \<in> affine hull S"
      using S_def \<open>bounded_linear augm\<close> aff_dim_eq_full affine_hull_linear_image assms(2) augm_def by blast
    ultimately show "affine hull S = {x. x \<bullet> (0::'n, 1::real) = 0}"
      by auto
  qed (auto simp: \<open>polytope S\<close> Basis_prod_def)
  then show ?thesis
    by (simp add: ceqc)
qed


text \<open>In particular, the Euler relation in 3 dimensions\<close>
corollary Euler_relation:
  fixes p :: "'n::euclidean_space set"
  assumes "polytope p" "aff_dim p = 3" "DIM('n) = 3"
  shows "(card {v. v face_of p \<and> aff_dim v = 0} + card {f. f face_of p \<and> aff_dim f = 2}) - card {e. e face_of p \<and> aff_dim e = 1} = 2"
proof -
  have "\<And>x. \<lbrakk>x face_of p; aff_dim x = 3\<rbrakk> \<Longrightarrow> x = p"
    using assms by (metis face_of_aff_dim_lt less_irrefl polytope_imp_convex)
  then have 3: "{f. f face_of p \<and> aff_dim f = 3} = {p}"
    using assms by (auto simp: face_of_refl polytope_imp_convex)
  have "(\<Sum>d = 0..3. (-1) ^ d * int (card {f. f face_of p \<and> aff_dim f = int d})) = 1"
    using Euler_Poincare_full [of p] assms by simp
  then show ?thesis
    by (simp add: sum.atLeast0_atMost_Suc_shift numeral_3_eq_3 3)
qed

end