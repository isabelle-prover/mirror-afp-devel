(*  Title:       BT_Prelim.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    Preliminaries shared across the Banach-Tarski formalization.

    This theory introduces conventions used throughout: type abbreviations
    for the unit sphere and unit ball, and a few small structural lemmas
    that recur.
*)

theory BT_Prelim
  imports
    "HOL-Analysis.Analysis"
    "Free-Groups.FreeGroups"
begin

section \<open>The unit sphere and unit ball in $\mathbb{R}^3$\<close>

text \<open>
  We work throughout with vectors in @{typ "real^3"} (the type
  @{typ "real^3"} from \<^theory>\<open>HOL-Analysis.Cartesian_Euclidean_Space\<close>).
  These abbreviations name the principal geometric objects of interest.
\<close>

definition sphere2 :: "(real^3) set" where
  "sphere2 = {x. norm x = 1}"

definition ball3 :: "(real^3) set" where
  "ball3 = {x. norm x \<le> 1}"

lemma sphere2_subset_ball3: "sphere2 \<subseteq> ball3"
  by (auto simp: sphere2_def ball3_def)

lemma zero_in_ball3: "0 \<in> ball3"
  by (simp add: ball3_def)

lemma zero_notin_sphere2: "(0::real^3) \<notin> sphere2"
  by (simp add: sphere2_def)


section \<open>Disjoint finite covers\<close>

text \<open>
  A \<^emph>\<open>partition\<close> of a set into a finite list of pairwise disjoint pieces
  is the basic combinatorial object underlying ``equidecomposability''.
\<close>

definition pairwise_disjoint :: "'a set list \<Rightarrow> bool" where
  "pairwise_disjoint Xs \<longleftrightarrow>
     (\<forall>i < length Xs. \<forall>j < length Xs. i \<noteq> j \<longrightarrow> Xs ! i \<inter> Xs ! j = {})"

lemma pairwise_disjoint_Nil [simp]: "pairwise_disjoint []"
  by (simp add: pairwise_disjoint_def)

lemma pairwise_disjoint_singleton [simp]: "pairwise_disjoint [X]"
  by (simp add: pairwise_disjoint_def)

lemma pairwise_disjoint_nthD:
  assumes "pairwise_disjoint Xs"
    and "i < length Xs" and "j < length Xs" and "i \<noteq> j"
  shows "Xs ! i \<inter> Xs ! j = {}"
  using assms bot_set_def pairwise_disjoint_def by auto

lemma indexed_union_set:
  fixes P :: "'a set list"
  shows "(\<Union>i<length P. P ! i) = \<Union>(set P)"
  by (auto simp add: set_conv_nth image_def)

lemma indexed_union_append:
  fixes P Q :: "'a set list"
  shows "(\<Union>i<length (P @ Q). (P @ Q) ! i) =
    (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i)"
  by (metis Union_Un_distrib indexed_union_set set_append)

lemma indexed_image_union_zip:
  fixes P :: "'a set list" and G :: "('a \<Rightarrow> 'b) list"
  assumes "length P = length G"
  shows "(\<Union>i<length P. G ! i ` (P ! i)) =
    (\<Union>(g, A)\<in>set (zip G P). g ` A)"
  using assms by (auto simp add: set_zip)

lemma indexed_image_union_append:
  fixes P Q :: "'a set list" and G H :: "('a \<Rightarrow> 'b) list"
  assumes lenP: "length P = length G" and lenQ: "length Q = length H"
  shows "(\<Union>i<length (P @ Q). (G @ H) ! i ` ((P @ Q) ! i)) =
    (\<Union>i<length P. G ! i ` (P ! i)) \<union>
    (\<Union>i<length Q. H ! i ` (Q ! i))"
proof -
  have len_append: "length (P @ Q) = length (G @ H)"
    using lenP lenQ by simp
  have "(\<Union>i<length (P @ Q). (G @ H) ! i ` ((P @ Q) ! i)) =
      (\<Union>(g, A)\<in>set (zip (G @ H) (P @ Q)). g ` A)"
    using indexed_image_union_zip[OF len_append] .
  also have "\<dots> =
      (\<Union>(g, A)\<in>set (zip G P). g ` A) \<union>
      (\<Union>(g, A)\<in>set (zip H Q). g ` A)"
    using lenP by simp
  also have "\<dots> =
      (\<Union>i<length P. G ! i ` (P ! i)) \<union>
      (\<Union>i<length Q. H ! i ` (Q ! i))"
    using indexed_image_union_zip[OF lenP] indexed_image_union_zip[OF lenQ] by simp
  finally show ?thesis .
qed

lemma indexed_union_map_fst:
  fixes xs :: "('a set \<times> 'b) list"
  shows "(\<Union>i<length (map fst xs). map fst xs ! i) =
    (\<Union>x\<in>set xs. fst x)"
  by (auto simp add: set_conv_nth)

lemma indexed_image_union_pairs:
  fixes xs :: "('a set \<times> ('a \<Rightarrow> 'b)) list"
  shows "(\<Union>i<length (map fst xs). map snd xs ! i ` (map fst xs ! i)) =
    (\<Union>x\<in>set xs. snd x ` fst x)"
  by (auto simp add: set_conv_nth)

lemma pairwise_disjoint_map_fstI:
  fixes xs :: "('a set \<times> 'b) list"
  assumes distinct: "distinct xs"
    and disj: "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set xs; x \<noteq> y\<rbrakk>
      \<Longrightarrow> fst x \<inter> fst y = {}"
  shows "pairwise_disjoint (map fst xs)"
  unfolding pairwise_disjoint_def
proof (intro allI impI)
  fix i j
  assume i: "i < length (map fst xs)" and j: "j < length (map fst xs)" and ij: "i \<noteq> j"
  have xi: "xs ! i \<in> set xs" and xj: "xs ! j \<in> set xs"
    using i j by auto
  have neq: "xs ! i \<noteq> xs ! j"
    using distinct i j ij by (simp add: nth_eq_iff_index_eq)
  show "map fst xs ! i \<inter> map fst xs ! j = {}"
    using disj[OF xi xj neq] i j by simp
qed

lemma pairwise_disjoint_appendI:
  assumes xs: "pairwise_disjoint xs"
    and ys: "pairwise_disjoint ys"
    and cross: "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set ys\<rbrakk> \<Longrightarrow> x \<inter> y = {}"
  shows "pairwise_disjoint (xs @ ys)"
  unfolding pairwise_disjoint_def
proof (intro allI impI)
  fix i j
  assume i: "i < length (xs @ ys)" and j: "j < length (xs @ ys)" and ij: "i \<noteq> j"
  show "(xs @ ys) ! i \<inter> (xs @ ys) ! j = {}"
  proof (cases "i < length xs")
    case True
    show ?thesis
    proof (cases "j < length xs")
      case True
      have "xs ! i \<inter> xs ! j = {}"
        by (rule pairwise_disjoint_nthD[OF xs \<open>i < length xs\<close> True ij])
      with \<open>i < length xs\<close> True show ?thesis
        by (simp add: nth_append)
    next
      case False
      hence "(xs @ ys) ! j \<in> set ys"
        using j by (simp add: nth_append)
      moreover have "(xs @ ys) ! i \<in> set xs"
        by (simp add: True nth_append_left)
      ultimately show ?thesis
        using cross by simp
    qed
  next
    case False
    show ?thesis
    proof (cases "j < length xs")
      case True
      hence "(xs @ ys) ! j \<in> set xs"
      proof -
        have "(xs @ ys) ! j = xs ! j"
          using True by (simp add: nth_append)
        moreover have "xs ! j \<in> set xs"
          by (rule nth_mem[OF True])
        ultimately show ?thesis
          by simp
      qed
      moreover have "(xs @ ys) ! i \<in> set ys"
        using False i by (simp add: nth_append)
      ultimately have "(xs @ ys) ! j \<inter> (xs @ ys) ! i = {}"
        using cross by blast
      thus ?thesis
        by (simp add: Int_commute)
    next
      case False
      have "ys ! (i - length xs) \<inter> ys ! (j - length xs) = {}"
        by (rule pairwise_disjoint_nthD[OF ys]) (use False \<open>\<not> i < length xs\<close> i j ij in auto)
      with False \<open>\<not> i < length xs\<close> i j show ?thesis
        by (simp add: nth_append)
    qed
  qed
qed

lemma pairwise_disjoint_appendD1:
  assumes "pairwise_disjoint (xs @ ys)"
  shows "pairwise_disjoint xs"
  unfolding pairwise_disjoint_def
proof (intro allI impI)
  fix i j
  assume i: "i < length xs" and j: "j < length xs" and ij: "i \<noteq> j"
  have "(xs @ ys) ! i \<inter> (xs @ ys) ! j = {}"
    by (rule pairwise_disjoint_nthD[OF assms]) (use i j ij in simp_all)
  thus "xs ! i \<inter> xs ! j = {}"
    using i j by (simp add: nth_append)
qed

lemma pairwise_disjoint_appendD2:
  assumes "pairwise_disjoint (xs @ ys)"
  shows "pairwise_disjoint ys"
  unfolding pairwise_disjoint_def
proof (intro allI impI)
  fix i j
  assume i: "i < length ys" and j: "j < length ys" and ij: "i \<noteq> j"
  have "length xs + i < length (xs @ ys)" and "length xs + j < length (xs @ ys)"
    using i j by simp_all
  moreover have "length xs + i \<noteq> length xs + j"
    using ij by simp
  ultimately have "(xs @ ys) ! (length xs + i) \<inter> (xs @ ys) ! (length xs + j) = {}"
    by (rule pairwise_disjoint_nthD[OF assms])
  thus "ys ! i \<inter> ys ! j = {}"
    using i j by simp
qed

lemma pairwise_disjoint_append_crossD:
  assumes "pairwise_disjoint (xs @ ys)"
    and "i < length xs" and "j < length ys"
  shows "xs ! i \<inter> ys ! j = {}"
proof -
  have "i < length (xs @ ys)" and "length xs + j < length (xs @ ys)"
    using assms by simp_all
  moreover have "i \<noteq> length xs + j"
    using assms(2) by simp
  ultimately have "(xs @ ys) ! i \<inter> (xs @ ys) ! (length xs + j) = {}"
    by (rule pairwise_disjoint_nthD[OF assms(1)])
  moreover have "(xs @ ys) ! i = xs ! i"
    using assms(2) by (simp add: nth_append)
  moreover have "(xs @ ys) ! (length xs + j) = ys ! j"
    using assms(3) by (simp add: nth_append)
  ultimately show ?thesis
    by simp
qed

lemma pairwise_disjoint_pair_imagesI:
  fixes xs :: "('a set \<times> ('a \<Rightarrow> 'b)) list"
  assumes distinct: "distinct xs"
    and disj: "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set xs; x \<noteq> y\<rbrakk>
      \<Longrightarrow> snd x ` fst x \<inter> snd y ` fst y = {}"
  shows "pairwise_disjoint (map2 (\<lambda>g A. g ` A) (map snd xs) (map fst xs))"
proof -
  have map_eq: "map2 (\<lambda>g A. g ` A) (map snd xs) (map fst xs) =
      map (\<lambda>x. snd x ` fst x) xs"
    by (induction xs) simp_all
  show ?thesis
    unfolding map_eq pairwise_disjoint_def
  proof (intro allI impI)
    fix i j
    assume i: "i < length (map (\<lambda>x. snd x ` fst x) xs)"
      and j: "j < length (map (\<lambda>x. snd x ` fst x) xs)" and ij: "i \<noteq> j"
    have xi: "xs ! i \<in> set xs" and xj: "xs ! j \<in> set xs"
      using i j by auto
    have neq: "xs ! i \<noteq> xs ! j"
      using distinct i j ij by (simp add: nth_eq_iff_index_eq)
    show "map (\<lambda>x. snd x ` fst x) xs ! i \<inter>
        map (\<lambda>x. snd x ` fst x) xs ! j = {}"
      using disj[OF xi xj neq] i j by simp
  qed
qed


section \<open>Transporting finite partitions\<close>

definition transfer_piece ::
  "'a set list \<Rightarrow> ('a \<Rightarrow> 'a) list \<Rightarrow> 'a set list \<Rightarrow>
    ('a \<Rightarrow> 'a) list \<Rightarrow> 'a set list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a set"
where
  "transfer_piece A e P g B k i l =
    {x \<in> A ! k. (e ! k) x \<in> P ! i \<and> (g ! i) ((e ! k) x) \<in> B ! l}"

definition transfer_map ::
  "('a \<Rightarrow> 'a) list \<Rightarrow> ('a \<Rightarrow> 'a) list \<Rightarrow>
    ('a \<Rightarrow> 'a) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)"
where
  "transfer_map t g e k i l = (t ! l) \<circ> (g ! i) \<circ> (e ! k)"

definition transfer_pairs ::
  "'a set list \<Rightarrow> ('a \<Rightarrow> 'a) list \<Rightarrow> 'a set list \<Rightarrow>
    ('a \<Rightarrow> 'a) list \<Rightarrow> 'a set list \<Rightarrow> ('a \<Rightarrow> 'a) list \<Rightarrow>
    ('a set \<times> ('a \<Rightarrow> 'a)) set"
where
  "transfer_pairs A e P g B t =
    {(transfer_piece A e P g B k i l, transfer_map t g e k i l) |
       k i l. k < length A \<and> i < length P \<and> l < length B}"

lemma finite_transfer_pairs [simp]: "finite (transfer_pairs A e P g B t)"
proof -
  have "transfer_pairs A e P g B t \<subseteq>
      (\<lambda>((k, i), l). (transfer_piece A e P g B k i l, transfer_map t g e k i l)) `
        (({..<length A} \<times> {..<length P}) \<times> {..<length B})"
  proof
    fix p
    assume "p \<in> transfer_pairs A e P g B t"
    then obtain k i l where k: "k < length A" and i: "i < length P" and l: "l < length B"
      and p_eq: "p = (transfer_piece A e P g B k i l, transfer_map t g e k i l)"
      unfolding transfer_pairs_def by blast
    have tril_in: "((k, i), l) \<in> ({..<length A} \<times> {..<length P}) \<times> {..<length B}"
      using k i l by simp
    show "p \<in>
      (\<lambda>((k, i), l). (transfer_piece A e P g B k i l, transfer_map t g e k i l)) `
        (({..<length A} \<times> {..<length P}) \<times> {..<length B})"
      using p_eq tril_in by force
  qed
  thus ?thesis
    by (rule finite_subset) simp
qed

lemma transfer_source_cover:
  assumes A_cover: "Y = (\<Union>k<length A. A ! k)"
    and B_cover: "X = (\<Union>k<length B. B ! k)"
    and e_into_B: "\<And>k x. \<lbrakk>k < length A; x \<in> A ! k\<rbrakk> \<Longrightarrow> (e ! k) x \<in> B ! k"
    and len_AB: "length A = length B"
    and source_cover: "X = (\<Union>i<length P. P ! i) \<union> (\<Union>j<length Q. Q ! j)"
    and imageP_cover: "X = (\<Union>i<length P. gP ! i ` (P ! i))"
    and imageQ_cover: "X = (\<Union>j<length Q. gQ ! j ` (Q ! j))"
  shows "Y =
    (\<Union>p\<in>transfer_pairs A e P gP B t. fst p) \<union>
    (\<Union>q\<in>transfer_pairs A e Q gQ B t. fst q)"
proof
  show "Y \<subseteq>
      (\<Union>p\<in>transfer_pairs A e P gP B t. fst p) \<union>
      (\<Union>q\<in>transfer_pairs A e Q gQ B t. fst q)"
  proof
    fix x
    assume xY: "x \<in> Y"
    then obtain k where k: "k < length A" and xA: "x \<in> A ! k"
      using A_cover by blast
    have ex: "(e ! k) x \<in> X"
      using B_cover e_into_B k len_AB xA by auto
    from source_cover ex have ex_cases:
      "(e ! k) x \<in> (\<Union>i<length P. P ! i) \<or>
       (e ! k) x \<in> (\<Union>j<length Q. Q ! j)"
      by blast
    thus "x \<in>
        (\<Union>p\<in>transfer_pairs A e P gP B t. fst p) \<union>
        (\<Union>q\<in>transfer_pairs A e Q gQ B t. fst q)"
    proof
      assume "(e ! k) x \<in> (\<Union>i<length P. P ! i)"
      then obtain i where i: "i < length P" and xP: "(e ! k) x \<in> P ! i"
        by blast
      have gxX: "(gP ! i) ((e ! k) x) \<in> X"
        using imageP_cover i xP by blast
      then obtain l where l: "l < length B" and gxB: "(gP ! i) ((e ! k) x) \<in> B ! l"
        using B_cover by blast
      have pair_in: "(transfer_piece A e P gP B k i l, transfer_map t gP e k i l)
          \<in> transfer_pairs A e P gP B t"
        using k i l unfolding transfer_pairs_def by blast
      have x_piece: "x \<in> transfer_piece A e P gP B k i l"
        using xA xP gxB by (simp add: transfer_piece_def)
      have set_in: "fst (transfer_piece A e P gP B k i l, transfer_map t gP e k i l) \<in>
          ((\<lambda>p. fst p) ` transfer_pairs A e P gP B t)"
        by (rule imageI[OF pair_in])
      have x_fst: "x \<in> fst (transfer_piece A e P gP B k i l, transfer_map t gP e k i l)"
        using x_piece by simp
      have "x \<in> \<Union> ((\<lambda>p. fst p) ` transfer_pairs A e P gP B t)"
        using set_in x_fst by (rule UnionI)
      thus ?thesis
        by simp
    next
      assume "(e ! k) x \<in> (\<Union>j<length Q. Q ! j)"
      then obtain j where j: "j < length Q" and xQ: "(e ! k) x \<in> Q ! j"
        by blast
      have gxX: "(gQ ! j) ((e ! k) x) \<in> X"
        using imageQ_cover j xQ by blast
      then obtain l where l: "l < length B" and gxB: "(gQ ! j) ((e ! k) x) \<in> B ! l"
        using B_cover by blast
      have pair_in: "(transfer_piece A e Q gQ B k j l, transfer_map t gQ e k j l)
          \<in> transfer_pairs A e Q gQ B t"
        using k j l unfolding transfer_pairs_def by blast
      have x_piece: "x \<in> transfer_piece A e Q gQ B k j l"
        using xA xQ gxB by (simp add: transfer_piece_def)
      have set_in: "fst (transfer_piece A e Q gQ B k j l, transfer_map t gQ e k j l) \<in>
          ((\<lambda>q. fst q) ` transfer_pairs A e Q gQ B t)"
        by (rule imageI[OF pair_in])
      have x_fst: "x \<in> fst (transfer_piece A e Q gQ B k j l, transfer_map t gQ e k j l)"
        using x_piece by simp
      have "x \<in> \<Union> ((\<lambda>q. fst q) ` transfer_pairs A e Q gQ B t)"
        using set_in x_fst by (rule UnionI)
      thus ?thesis
        by simp
    qed
  qed
  show "(\<Union>p\<in>transfer_pairs A e P gP B t. fst p) \<union>
      (\<Union>q\<in>transfer_pairs A e Q gQ B t. fst q) \<subseteq> Y"
    using A_cover unfolding transfer_pairs_def transfer_piece_def by auto
qed

lemma transfer_image_cover:
  assumes A_cover: "Y = (\<Union>k<length A. A ! k)"
    and B_cover: "X = (\<Union>k<length B. B ! k)"
    and len_AB: "length A = length B"
    and e_left: "\<And>k x. \<lbrakk>k < length A; x \<in> A ! k\<rbrakk>
      \<Longrightarrow> (e ! k) x \<in> B ! k \<and> (t ! k) ((e ! k) x) = x"
    and t_left: "\<And>k y. \<lbrakk>k < length B; y \<in> B ! k\<rbrakk>
      \<Longrightarrow> (t ! k) y \<in> A ! k \<and> (e ! k) ((t ! k) y) = y"
    and P_sub: "\<And>i. i < length P \<Longrightarrow> P ! i \<subseteq> X"
    and image_cover: "X = (\<Union>i<length P. g ! i ` (P ! i))"
  shows "Y = (\<Union>p\<in>transfer_pairs A e P g B t. snd p ` fst p)"
proof
  show "Y \<subseteq> (\<Union>p\<in>transfer_pairs A e P g B t. snd p ` fst p)"
  proof
    fix y
    assume yY: "y \<in> Y"
    then obtain l where l: "l < length A" and yA: "y \<in> A ! l"
      using A_cover by blast
    have eyB: "(e ! l) y \<in> B ! l" and tey: "(t ! l) ((e ! l) y) = y"
      using e_left[OF l yA] by auto
    have eyX: "(e ! l) y \<in> X"
      using B_cover eyB l len_AB by auto
    then obtain i x where i: "i < length P" and xP: "x \<in> P ! i"
      and ey_eq: "(e ! l) y = (g ! i) x"
      using image_cover by blast
    have lB: "l < length B"
      using l len_AB by simp
    have xX: "x \<in> X"
      using P_sub[OF i] xP by (rule subsetD)
    then obtain k where k: "k < length B" and xB: "x \<in> B ! k"
      using B_cover by blast
    have txA: "(t ! k) x \<in> A ! k" and etx: "(e ! k) ((t ! k) x) = x"
      using t_left[OF k xB] by auto
    have kA: "k < length A"
      using k len_AB by simp
    have piece_in: "(t ! k) x \<in> transfer_piece A e P g B k i l"
      using txA etx xP eyB ey_eq by (simp add: transfer_piece_def)
    have pair_in: "(transfer_piece A e P g B k i l, transfer_map t g e k i l)
        \<in> transfer_pairs A e P g B t"
      using kA i lB unfolding transfer_pairs_def by blast
    have "transfer_map t g e k i l ((t ! k) x) = y"
      using etx ey_eq tey by (simp add: transfer_map_def)
    thus "y \<in> (\<Union>p\<in>transfer_pairs A e P g B t. snd p ` fst p)"
      using pair_in piece_in by force
  qed
  show "(\<Union>p\<in>transfer_pairs A e P g B t. snd p ` fst p) \<subseteq> Y"
  proof
    fix y
    assume "y \<in> (\<Union>p\<in>transfer_pairs A e P g B t. snd p ` fst p)"
    then obtain k i l x where k: "k < length A" and i: "i < length P"
      and l: "l < length B" and x_piece: "x \<in> transfer_piece A e P g B k i l"
      and y_eq: "y = transfer_map t g e k i l x"
      unfolding transfer_pairs_def by auto
    have gxB: "(g ! i) ((e ! k) x) \<in> B ! l"
      using x_piece by (simp add: transfer_piece_def)
    have tyA: "(t ! l) ((g ! i) ((e ! k) x)) \<in> A ! l"
      using t_left[OF l gxB] by auto
    hence "y \<in> A ! l"
      using y_eq by (simp add: transfer_map_def)
    moreover have "A ! l \<subseteq> Y"
      using A_cover l len_AB by auto
    ultimately show "y \<in> Y"
      by blast
  qed
qed

lemma transfer_source_disjoint_same:
  assumes A_disj: "pairwise_disjoint A"
    and P_disj: "pairwise_disjoint P"
    and B_disj: "pairwise_disjoint B"
    and x_in: "x \<in> transfer_pairs A e P g B t"
    and y_in: "y \<in> transfer_pairs A e P g B t"
    and xy: "x \<noteq> y"
  shows "fst x \<inter> fst y = {}"
proof (rule ccontr)
  assume nonempty: "fst x \<inter> fst y \<noteq> {}"
  obtain k i l where k: "k < length A" and i: "i < length P" and l: "l < length B"
    and x_eq: "x = (transfer_piece A e P g B k i l, transfer_map t g e k i l)"
    using x_in unfolding transfer_pairs_def by blast
  obtain k' i' l' where k': "k' < length A" and i': "i' < length P" and l': "l' < length B"
    and y_eq: "y = (transfer_piece A e P g B k' i' l', transfer_map t g e k' i' l')"
    using y_in unfolding transfer_pairs_def by blast
  from nonempty obtain z where zx: "z \<in> fst x" and zy: "z \<in> fst y"
    by blast
  have zA: "z \<in> A ! k" and zeP: "(e ! k) z \<in> P ! i"
    and zgB: "(g ! i) ((e ! k) z) \<in> B ! l"
    using zx x_eq by (auto simp: transfer_piece_def)
  have zA': "z \<in> A ! k'" and zeP': "(e ! k') z \<in> P ! i'"
    and zgB': "(g ! i') ((e ! k') z) \<in> B ! l'"
    using zy y_eq by (auto simp: transfer_piece_def)
  show False
  proof (cases "k = k'")
    case False
    have "A ! k \<inter> A ! k' = {}"
      by (rule pairwise_disjoint_nthD[OF A_disj k k' False])
    with zA zA' show False
      by blast
  next
    case k_eq: True
    show False
    proof (cases "i = i'")
      case False
      have "P ! i \<inter> P ! i' = {}"
        by (rule pairwise_disjoint_nthD[OF P_disj i i' False])
      moreover have "(e ! k) z \<in> P ! i'"
        using zeP' k_eq by simp
      ultimately show False
        using zeP by blast
    next
      case i_eq: True
      show False
      proof (cases "l = l'")
        case False
        have "B ! l \<inter> B ! l' = {}"
          by (rule pairwise_disjoint_nthD[OF B_disj l l' False])
        moreover have "(g ! i) ((e ! k) z) \<in> B ! l'"
          using zgB' k_eq i_eq by simp
        ultimately show False
          using zgB by blast
      next
        case l_eq: True
        have "x = y"
          using x_eq y_eq k_eq i_eq l_eq by simp
        with xy show False
          by contradiction
      qed
    qed
  qed
qed

lemma transfer_source_disjoint_cross:
  assumes A_disj: "pairwise_disjoint A"
    and PQ_cross: "\<And>i j. \<lbrakk>i < length P; j < length Q\<rbrakk> \<Longrightarrow> P ! i \<inter> Q ! j = {}"
    and B_disj: "pairwise_disjoint B"
    and x_in: "x \<in> transfer_pairs A e P gP B t"
    and y_in: "y \<in> transfer_pairs A e Q gQ B t"
  shows "fst x \<inter> fst y = {}"
proof (rule ccontr)
  assume nonempty: "fst x \<inter> fst y \<noteq> {}"
  obtain k i l where k: "k < length A" and i: "i < length P" and l: "l < length B"
    and x_eq: "x = (transfer_piece A e P gP B k i l, transfer_map t gP e k i l)"
    using x_in unfolding transfer_pairs_def by blast
  obtain k' j l' where k': "k' < length A" and j: "j < length Q" and l': "l' < length B"
    and y_eq: "y = (transfer_piece A e Q gQ B k' j l', transfer_map t gQ e k' j l')"
    using y_in unfolding transfer_pairs_def by blast
  from nonempty obtain z where zx: "z \<in> fst x" and zy: "z \<in> fst y"
    by blast
  have zA: "z \<in> A ! k" and zeP: "(e ! k) z \<in> P ! i"
    using zx x_eq by (auto simp: transfer_piece_def)
  have zA': "z \<in> A ! k'" and zeQ: "(e ! k') z \<in> Q ! j"
    using zy y_eq by (auto simp: transfer_piece_def)
  show False
  proof (cases "k = k'")
    case False
    have "A ! k \<inter> A ! k' = {}"
      by (rule pairwise_disjoint_nthD[OF A_disj k k' False])
    with zA zA' show False
      by blast
  next
    case k_eq: True
    have "P ! i \<inter> Q ! j = {}"
      by (rule PQ_cross[OF i j])
    moreover have "(e ! k) z \<in> Q ! j"
      using zeQ k_eq by simp
    ultimately show False
      using zeP by blast
  qed
qed

lemma transfer_image_disjoint_same:
  assumes len_AB: "length A = length B"
    and A_disj: "pairwise_disjoint A"
    and B_disj: "pairwise_disjoint B"
    and image_disj: "pairwise_disjoint (map2 (\<lambda>h C. h ` C) g P)"
    and len: "length P = length g"
    and g_inj: "\<And>i. i < length P \<Longrightarrow> inj (g ! i)"
    and e_into_B: "\<And>k x. \<lbrakk>k < length A; x \<in> A ! k\<rbrakk> \<Longrightarrow> (e ! k) x \<in> B ! k"
    and t_left: "\<And>l y. \<lbrakk>l < length B; y \<in> B ! l\<rbrakk>
      \<Longrightarrow> (t ! l) y \<in> A ! l \<and> (e ! l) ((t ! l) y) = y"
    and x_in: "x \<in> transfer_pairs A e P g B t"
    and y_in: "y \<in> transfer_pairs A e P g B t"
    and xy: "x \<noteq> y"
  shows "snd x ` fst x \<inter> snd y ` fst y = {}"
proof (rule ccontr)
  assume nonempty: "snd x ` fst x \<inter> snd y ` fst y \<noteq> {}"
  obtain k i l where k: "k < length A" and i: "i < length P" and l: "l < length B"
    and x_eq: "x = (transfer_piece A e P g B k i l, transfer_map t g e k i l)"
    using x_in unfolding transfer_pairs_def by blast
  obtain k' i' l' where k': "k' < length A" and i': "i' < length P" and l': "l' < length B"
    and y_eq: "y = (transfer_piece A e P g B k' i' l', transfer_map t g e k' i' l')"
    using y_in unfolding transfer_pairs_def by blast
  from nonempty obtain z where zx: "z \<in> snd x ` fst x" and zy: "z \<in> snd y ` fst y"
    by blast
  then obtain a b where
      a_piece: "a \<in> transfer_piece A e P g B k i l"
    and z_a: "z = transfer_map t g e k i l a"
    and b_piece: "b \<in> transfer_piece A e P g B k' i' l'"
    and z_b: "z = transfer_map t g e k' i' l' b"
    using x_eq y_eq by auto
  have aA: "a \<in> A ! k" and aeP: "(e ! k) a \<in> P ! i"
    and gaB: "(g ! i) ((e ! k) a) \<in> B ! l"
    using a_piece by (auto simp: transfer_piece_def)
  have bA: "b \<in> A ! k'" and beP: "(e ! k') b \<in> P ! i'"
    and gbB: "(g ! i') ((e ! k') b) \<in> B ! l'"
    using b_piece by (auto simp: transfer_piece_def)
  have lA: "l < length A" and lA': "l' < length A"
    using l l' len_AB by simp_all
  have zA_l: "z \<in> A ! l"
    using t_left[OF l gaB] z_a by (simp add: transfer_map_def)
  have zA_l': "z \<in> A ! l'"
    using t_left[OF l' gbB] z_b by (simp add: transfer_map_def)
  show False
  proof (cases "l = l'")
    case False
    have "A ! l \<inter> A ! l' = {}"
      by (rule pairwise_disjoint_nthD[OF A_disj lA lA' False])
    with zA_l zA_l' show False
      by blast
  next
    case l_eq: True
    have ez_a: "(e ! l) z = (g ! i) ((e ! k) a)"
      using t_left[OF l gaB] z_a by (simp add: transfer_map_def)
    have ez_b: "(e ! l) z = (g ! i') ((e ! k') b)"
      using t_left[OF l' gbB] z_b l_eq by (simp add: transfer_map_def)
    have g_eq: "(g ! i) ((e ! k) a) = (g ! i') ((e ! k') b)"
      using ez_a ez_b by simp
    show False
    proof (cases "i = i'")
      case False then 
      have img_i: "(g ! i) ((e ! k) a) \<in> map2 (\<lambda>h C. h ` C) g P ! i"
        using aeP i len by simp
      have img_i': "(g ! i') ((e ! k') b) \<in> map2 (\<lambda>h C. h ` C) g P ! i'"
        using beP i' len by simp
      have "map2 (\<lambda>h C. h ` C) g P ! i \<inter>
          map2 (\<lambda>h C. h ` C) g P ! i' = {}"
        by (rule pairwise_disjoint_nthD[OF image_disj]) (use i i' False len in simp_all)
      moreover have "(g ! i) ((e ! k) a) \<in> map2 (\<lambda>h C. h ` C) g P ! i'"
        using img_i' g_eq by simp
      ultimately show False
        using img_i by auto
    next
      case i_eq: True
      have e_eq: "(e ! k) a = (e ! k') b"
        using g_eq i_eq g_inj[OF i] by (auto dest: injD)
      show False
      proof (cases "k = k'")
        case False
        have kB: "k < length B" and kB': "k' < length B"
          using k k' len_AB by simp_all
        have eaB: "(e ! k) a \<in> B ! k"
          by (rule e_into_B[OF k aA])
        have ebB: "(e ! k') b \<in> B ! k'"
          by (rule e_into_B[OF k' bA])
        have "B ! k \<inter> B ! k' = {}"
          by (rule pairwise_disjoint_nthD[OF B_disj kB kB' False])
        moreover have "(e ! k) a \<in> B ! k'"
          using ebB e_eq by simp
        ultimately show False
          using eaB by auto
      next
        case k_eq: True
        have "x = y"
          using x_eq y_eq k_eq i_eq l_eq by simp
        with xy show False
          by contradiction
      qed
    qed
  qed
qed

lemma transfer_partitioned_paradox:
  assumes len_AB: "length A = length B"
    and A_cover: "Y = (\<Union>k<length A. A ! k)"
    and A_disj: "pairwise_disjoint A"
    and B_cover: "X = (\<Union>k<length B. B ! k)"
    and B_disj: "pairwise_disjoint B"
    and e_left: "\<And>k x. \<lbrakk>k < length A; x \<in> A ! k\<rbrakk>
      \<Longrightarrow> (e ! k) x \<in> B ! k \<and> (t ! k) ((e ! k) x) = x"
    and t_left: "\<And>k y. \<lbrakk>k < length B; y \<in> B ! k\<rbrakk>
      \<Longrightarrow> (t ! k) y \<in> A ! k \<and> (e ! k) ((t ! k) y) = y"
    and lenP: "length P = length gP"
    and lenQ: "length Q = length gQ"
    and source_disj: "pairwise_disjoint (P @ Q)"
    and source_cover: "X = (\<Union>i<length P. P ! i) \<union> (\<Union>j<length Q. Q ! j)"
    and imageP_disj: "pairwise_disjoint (map2 (\<lambda>h C. h ` C) gP P)"
    and imageQ_disj: "pairwise_disjoint (map2 (\<lambda>h C. h ` C) gQ Q)"
    and imageP_cover: "X = (\<Union>i<length P. gP ! i ` (P ! i))"
    and imageQ_cover: "X = (\<Union>j<length Q. gQ ! j ` (Q ! j))"
    and gP_inj: "\<And>i. i < length P \<Longrightarrow> inj (gP ! i)"
    and gQ_inj: "\<And>j. j < length Q \<Longrightarrow> inj (gQ ! j)"
    and mapsP: "\<And>k i l. \<lbrakk>k < length A; i < length P; l < length B\<rbrakk>
      \<Longrightarrow> transfer_map t gP e k i l \<in> M"
    and mapsQ: "\<And>k j l. \<lbrakk>k < length A; j < length Q; l < length B\<rbrakk>
      \<Longrightarrow> transfer_map t gQ e k j l \<in> M"
  shows "\<exists>P' Q' :: 'a set list. \<exists>gP' gQ' :: ('a \<Rightarrow> 'a) list.
      length P' = length gP' \<and> length Q' = length gQ' \<and>
      set gP' \<subseteq> M \<and> set gQ' \<subseteq> M \<and>
      pairwise_disjoint (P' @ Q') \<and>
      pairwise_disjoint (map2 (\<lambda>h C. h ` C) gP' P') \<and>
      pairwise_disjoint (map2 (\<lambda>h C. h ` C) gQ' Q') \<and>
      Y = (\<Union>i<length P'. P' ! i) \<union> (\<Union>j<length Q'. Q' ! j) \<and>
      Y = (\<Union>i<length P'. gP' ! i ` (P' ! i)) \<and>
      Y = (\<Union>j<length Q'. gQ' ! j ` (Q' ! j))"
proof -
  let ?CP = "transfer_pairs A e P gP B t"
  let ?CQ = "transfer_pairs A e Q gQ B t"
  have finite_CP: "finite ?CP"
    by simp
  have finite_CQ: "finite ?CQ"
    by simp
  obtain pairsP where setP: "set pairsP = ?CP" and distinctP: "distinct pairsP"
    using finite_distinct_list[OF finite_CP] by blast
  obtain pairsQ where setQ: "set pairsQ = ?CQ" and distinctQ: "distinct pairsQ"
    using finite_distinct_list[OF finite_CQ] by blast
  let ?P' = "map fst pairsP"
  let ?Q' = "map fst pairsQ"
  let ?gP' = "map snd pairsP"
  let ?gQ' = "map snd pairsQ"

  have P_disj: "pairwise_disjoint P"
    by (rule pairwise_disjoint_appendD1[OF source_disj])
  have Q_disj: "pairwise_disjoint Q"
    by (rule pairwise_disjoint_appendD2[OF source_disj])
  have PQ_cross: "\<And>i j. \<lbrakk>i < length P; j < length Q\<rbrakk> \<Longrightarrow> P ! i \<inter> Q ! j = {}"
    by (rule pairwise_disjoint_append_crossD[OF source_disj])

  have P'_disj: "pairwise_disjoint ?P'"
  proof (rule pairwise_disjoint_map_fstI[OF distinctP])
    fix x y
    assume "x \<in> set pairsP" "y \<in> set pairsP" "x \<noteq> y"
    thus "fst x \<inter> fst y = {}"
      using setP transfer_source_disjoint_same[OF A_disj P_disj B_disj] by blast
  qed
  have Q'_disj: "pairwise_disjoint ?Q'"
    by (metis A_disj B_disj Q_disj distinctQ pairwise_disjoint_map_fstI setQ transfer_source_disjoint_same)
  have cross_disj: "\<And>x y. \<lbrakk>x \<in> set ?P'; y \<in> set ?Q'\<rbrakk> \<Longrightarrow> x \<inter> y = {}"
  proof -
    fix x y
    assume x: "x \<in> set ?P'" and y: "y \<in> set ?Q'"
    then obtain px qy where px: "px \<in> set pairsP" and qy: "qy \<in> set pairsQ"
      and x_eq: "x = fst px" and y_eq: "y = fst qy"
      by auto
    show "x \<inter> y = {}"
      using transfer_source_disjoint_cross[OF A_disj PQ_cross B_disj]
        setP setQ px qy x_eq y_eq by blast
  qed
  have source_disj': "pairwise_disjoint (?P' @ ?Q')"
    by (rule pairwise_disjoint_appendI[OF P'_disj Q'_disj cross_disj])

  have imageP_disj': "pairwise_disjoint (map2 (\<lambda>h C. h ` C) ?gP' ?P')"
  proof (rule pairwise_disjoint_pair_imagesI[OF distinctP])
    fix x y
    assume "x \<in> set pairsP" "y \<in> set pairsP" "x \<noteq> y"
    thus "snd x ` fst x \<inter> snd y ` fst y = {}"
      using setP transfer_image_disjoint_same[
        OF len_AB A_disj B_disj imageP_disj lenP gP_inj _ t_left]
        e_left by blast
  qed
  have imageQ_disj': "pairwise_disjoint (map2 (\<lambda>h C. h ` C) ?gQ' ?Q')"
  proof (rule pairwise_disjoint_pair_imagesI[OF distinctQ])
    fix x y
    assume "x \<in> set pairsQ" "y \<in> set pairsQ" "x \<noteq> y"
    thus "snd x ` fst x \<inter> snd y ` fst y = {}"
      using setQ transfer_image_disjoint_same[
        OF len_AB A_disj B_disj imageQ_disj lenQ gQ_inj _ t_left]
        e_left by blast
  qed

  have P_sub: "\<And>i. i < length P \<Longrightarrow> P ! i \<subseteq> X"
    using source_cover by blast
  have Q_sub: "\<And>j. j < length Q \<Longrightarrow> Q ! j \<subseteq> X"
    using source_cover by blast

  have source_cover': "Y = (\<Union>i<length ?P'. ?P' ! i) \<union> (\<Union>j<length ?Q'. ?Q' ! j)"
  proof -
    have "Y = (\<Union>p\<in>?CP. fst p) \<union> (\<Union>q\<in>?CQ. fst q)"
      by (rule transfer_source_cover[OF A_cover B_cover _ len_AB source_cover imageP_cover imageQ_cover])
        (use e_left in auto)
    also have "\<dots> = (\<Union>i<length ?P'. ?P' ! i) \<union> (\<Union>j<length ?Q'. ?Q' ! j)"
      using setP setQ indexed_union_map_fst[of pairsP] indexed_union_map_fst[of pairsQ]
      by simp
    finally show ?thesis .
  qed
  have imageP_cover': "Y = (\<Union>i<length ?P'. ?gP' ! i ` (?P' ! i))"
  proof -
    have "Y = (\<Union>p\<in>?CP. snd p ` fst p)"
      by (rule transfer_image_cover[OF A_cover B_cover len_AB e_left t_left P_sub imageP_cover])
    also have "\<dots> = (\<Union>i<length ?P'. ?gP' ! i ` (?P' ! i))"
      using setP indexed_image_union_pairs[of pairsP] by simp
    finally show ?thesis .
  qed
  have imageQ_cover': "Y = (\<Union>j<length ?Q'. ?gQ' ! j ` (?Q' ! j))"
  proof -
    have "Y = (\<Union>q\<in>?CQ. snd q ` fst q)"
      by (rule transfer_image_cover[OF A_cover B_cover len_AB e_left t_left Q_sub imageQ_cover])
    also have "\<dots> = (\<Union>j<length ?Q'. ?gQ' ! j ` (?Q' ! j))"
      using setQ indexed_image_union_pairs[of pairsQ] by simp
    finally show ?thesis .
  qed

  have mapsP': "set ?gP' \<subseteq> M"
    using setP mapsP unfolding transfer_pairs_def by auto
  have mapsQ': "set ?gQ' \<subseteq> M"
    using setQ mapsQ unfolding transfer_pairs_def by auto

  show ?thesis
  proof (intro exI conjI)
    show "length ?P' = length ?gP'"
      by simp
    show "length ?Q' = length ?gQ'"
      by simp
    show "set ?gP' \<subseteq> M"
      by (rule mapsP')
    show "set ?gQ' \<subseteq> M"
      by (rule mapsQ')
    show "pairwise_disjoint (?P' @ ?Q')"
      by (rule source_disj')
    show "pairwise_disjoint (map2 (\<lambda>h C. h ` C) ?gP' ?P')"
      by (rule imageP_disj')
    show "pairwise_disjoint (map2 (\<lambda>h C. h ` C) ?gQ' ?Q')"
      by (rule imageQ_disj')
    show "Y = (\<Union>i<length ?P'. ?P' ! i) \<union> (\<Union>j<length ?Q'. ?Q' ! j)"
      by (rule source_cover')
    show "Y = (\<Union>i<length ?P'. ?gP' ! i ` (?P' ! i))"
      by (rule imageP_cover')
    show "Y = (\<Union>j<length ?Q'. ?gQ' ! j ` (?Q' ! j))"
      by (rule imageQ_cover')
  qed
qed

end
