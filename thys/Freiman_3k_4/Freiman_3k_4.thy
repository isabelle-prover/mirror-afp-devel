theory Freiman_3k_4
  imports
    Freiman_Sumset_Basics
    "HOL-Computational_Algebra.Group_Closure"
    Kneser_Cauchy_Davenport.Kneser_Cauchy_Davenport_main_proofs
begin

section \<open>Freiman's @{text "3k - 4"} theorem for integer sumsets\<close>

text \<open>
  This theory develops the integer-side infrastructure for Freiman's
  @{text "3k - 4"} theorem. The final theorem is most naturally stated after
  normalizing a finite integer set by translation and dilation; the lemmas
  below record the affine invariance and interval containment facts used by
  that reduction.
\<close>

subsection \<open>Integer arithmetic progressions\<close>

definition int_ap_segment :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set" where
  "int_ap_segment a d n = (\<lambda>i. a + int i * d) ` {..<n}"

definition int_arithmetic_progression :: "int set \<Rightarrow> bool" where
  "int_arithmetic_progression A \<longleftrightarrow> (\<exists>a d n. A = int_ap_segment a d n)"

lemma int_arithmetic_progressionI:
  "A = int_ap_segment a d n \<Longrightarrow> int_arithmetic_progression A"
  unfolding int_arithmetic_progression_def by blast

lemma int_arithmetic_progressionE:
  assumes "int_arithmetic_progression A"
  obtains a d n where "A = int_ap_segment a d n"
  using assms unfolding int_arithmetic_progression_def by blast

lemma finite_int_ap_segment [simp]:
  "finite (int_ap_segment a d n)"
  by (simp add: int_ap_segment_def)

lemma int_ap_segment_empty [simp]:
  "int_ap_segment a d 0 = {}"
  by (simp add: int_ap_segment_def)

lemma inj_on_int_ap_segment_index:
  assumes "d \<noteq> 0"
  shows "inj_on (\<lambda>i. a + int i * d) {..<n}"
proof (rule inj_onI)
  fix i j
  assume i: "i \<in> {..<n}" and j: "j \<in> {..<n}"
  assume eq: "a + int i * d = a + int j * d"
  from eq have "int i * d = int j * d"
    by simp
  with assms have "int i = int j"
    by simp
  then show "i = j"
    by simp
qed

lemma card_int_ap_segment:
  assumes "d \<noteq> 0"
  shows "card (int_ap_segment a d n) = n"
  using assms
  by (simp add: int_ap_segment_def card_image inj_on_int_ap_segment_index)

lemma int_ap_segment_one_eq_atLeastAtMost:
  assumes "a \<le> b"
  shows "int_ap_segment a 1 (nat (b - a + 1)) = {a..b}"
proof
  show "int_ap_segment a 1 (nat (b - a + 1)) \<subseteq> {a..b}"
  proof
    fix x
    assume "x \<in> int_ap_segment a 1 (nat (b - a + 1))"
    then obtain i where i_lt: "i < nat (b - a + 1)" and x: "x = a + int i"
      by (auto simp: int_ap_segment_def)
    from assms have "0 < b - a + 1"
      by linarith
    with i_lt have "int i < b - a + 1"
      by linarith
    with x show "x \<in> {a..b}"
      by auto
  qed
next
  show "{a..b} \<subseteq> int_ap_segment a 1 (nat (b - a + 1))"
  proof
    fix x
    assume x_in: "x \<in> {a..b}"
    then have ax_nonneg: "0 \<le> x - a"
      by simp
    define i where "i = nat (x - a)"
    from ax_nonneg have int_i: "int i = x - a"
      by (simp add: i_def)
    from x_in have "x - a < b - a + 1"
      by simp
    with int_i have "i < nat (b - a + 1)"
      by linarith
    moreover have "x = a + int i"
      using int_i by simp
    ultimately show "x \<in> int_ap_segment a 1 (nat (b - a + 1))"
      by (auto simp: int_ap_segment_def)
  qed
qed

lemma finite_int_set_subset_min_max_ap:
  assumes fin: "finite A" and nonempty: "A \<noteq> {}"
  shows "A \<subseteq> int_ap_segment (Min A) 1 (nat (Max A - Min A + 1))"
proof -
  have "Min A \<le> Max A"
    using assms by simp
  then have interval_eq: "int_ap_segment (Min A) 1 (nat (Max A - Min A + 1)) = {Min A..Max A}"
    by (rule int_ap_segment_one_eq_atLeastAtMost)
  have "A \<subseteq> {Min A..Max A}"
    using assms by auto
  then show ?thesis
    using interval_eq by simp
qed

subsection \<open>Affine images and sumsets\<close>

definition affine_image_int :: "int \<Rightarrow> int \<Rightarrow> int set \<Rightarrow> int set" where
  "affine_image_int c d A = (\<lambda>x. c + d * x) ` A"

lemma affine_image_int_iff:
  "x \<in> affine_image_int c d A \<longleftrightarrow> (\<exists>a\<in>A. x = c + d * a)"
  by (auto simp: affine_image_int_def)

lemma finite_affine_image_int [intro]:
  assumes "finite A"
  shows "finite (affine_image_int c d A)"
  using assms by (simp add: affine_image_int_def)

lemma inj_on_affine_image_int:
  fixes c d :: int
  assumes "d \<noteq> 0"
  shows "inj_on (\<lambda>x. c + d * x) A"
proof (rule inj_onI)
  fix x y
  assume "x \<in> A" and "y \<in> A"
  assume eq: "c + d * x = c + d * y"
  have "(c + d * x) - c = (c + d * y) - c"
    using eq by simp
  then have "d * x = d * y"
    by simp
  with assms show "x = y"
    by simp
qed

lemma card_affine_image_int:
  assumes fin: "finite A" and d_nonzero: "d \<noteq> 0"
  shows "card (affine_image_int c d A) = card A"
  using fin inj_on_affine_image_int[OF d_nonzero, of c A]
  by (simp add: affine_image_int_def card_image)

lemma affine_image_int_sumset:
  "sumset (affine_image_int c d A) (affine_image_int e d B) =
    affine_image_int (c + e) d (sumset A B)"
proof
  show "sumset (affine_image_int c d A) (affine_image_int e d B) \<subseteq>
      affine_image_int (c + e) d (sumset A B)"
  proof
    fix x
    assume "x \<in> sumset (affine_image_int c d A) (affine_image_int e d B)"
    then obtain y z where
        y: "y \<in> affine_image_int c d A"
      and z: "z \<in> affine_image_int e d B"
      and x: "x = y + z"
      by (rule sumsetE)
    from y obtain a where a: "a \<in> A" and y_eq: "y = c + d * a"
      by (auto simp: affine_image_int_def)
    from z obtain b where b: "b \<in> B" and z_eq: "z = e + d * b"
      by (auto simp: affine_image_int_def)
    have "a + b \<in> sumset A B"
      using a b by (rule sumsetI)
    moreover have "x = (c + e) + d * (a + b)"
      using x y_eq z_eq by (simp add: algebra_simps)
    ultimately show "x \<in> affine_image_int (c + e) d (sumset A B)"
      by (auto simp: affine_image_int_def)
  qed
next
  show "affine_image_int (c + e) d (sumset A B) \<subseteq>
      sumset (affine_image_int c d A) (affine_image_int e d B)"
  proof
    fix x
    assume "x \<in> affine_image_int (c + e) d (sumset A B)"
    then obtain s where s: "s \<in> sumset A B" and x: "x = (c + e) + d * s"
      by (auto simp: affine_image_int_def)
    from s obtain a b where a: "a \<in> A" and b: "b \<in> B" and s_eq: "s = a + b"
      by (rule sumsetE)
    have "c + d * a \<in> affine_image_int c d A"
      using a by (auto simp: affine_image_int_def)
    moreover have "e + d * b \<in> affine_image_int e d B"
      using b by (auto simp: affine_image_int_def)
    moreover have "x = (c + d * a) + (e + d * b)"
      using x s_eq by (simp add: algebra_simps)
    ultimately show "x \<in> sumset (affine_image_int c d A) (affine_image_int e d B)"
      by (metis sumsetI)
  qed
qed

lemma affine_image_int_sumset_self:
  "sumset (affine_image_int c d A) (affine_image_int c d A) =
    affine_image_int (2 * c) d (sumset A A)"
proof -
  have "sumset (affine_image_int c d A) (affine_image_int c d A) =
      affine_image_int (c + c) d (sumset A A)"
    by (rule affine_image_int_sumset)
  also have "\<dots> = affine_image_int (2 * c) d (sumset A A)"
    by simp
  finally show ?thesis .
qed

lemma card_sumset_affine_image_int:
  assumes finA: "finite A" and finB: "finite B" and d_nonzero: "d \<noteq> 0"
  shows "card (sumset (affine_image_int c d A) (affine_image_int e d B)) =
    card (sumset A B)"
proof -
  have "card (sumset (affine_image_int c d A) (affine_image_int e d B)) =
      card (affine_image_int (c + e) d (sumset A B))"
    by (simp add: affine_image_int_sumset)
  also have "\<dots> = card (sumset A B)"
    by (rule card_affine_image_int[OF finite_sumset[OF finA finB] d_nonzero])
  finally show ?thesis .
qed

lemma card_sumset_affine_image_int_self:
  assumes fin: "finite A" and d_nonzero: "d \<noteq> 0"
  shows "card (sumset (affine_image_int c d A) (affine_image_int c d A)) =
    card (sumset A A)"
  by (rule card_sumset_affine_image_int[OF fin fin d_nonzero])

lemma affine_image_int_zero_one [simp]:
  "affine_image_int 0 1 A = A"
  by (auto simp: affine_image_int_def)

subsection \<open>Endpoint lower bound for two-fold sumsets\<close>

lemma endpoint_affine_images_inter:
  fixes A :: "int set"
  assumes fin: "finite A" and nonempty: "A \<noteq> {}"
  shows "affine_image_int (Min A) 1 A \<inter> affine_image_int (Max A) 1 A =
    {Min A + Max A}"
proof
  show "affine_image_int (Min A) 1 A \<inter> affine_image_int (Max A) 1 A \<subseteq>
      {Min A + Max A}"
  proof
    fix x
    assume x_in: "x \<in> affine_image_int (Min A) 1 A \<inter> affine_image_int (Max A) 1 A"
    then obtain a where a_in: "a \<in> A" and x_left: "x = Min A + a"
      by (auto simp: affine_image_int_def)
    from x_in obtain b where b_in: "b \<in> A" and x_right: "x = Max A + b"
      by (auto simp: affine_image_int_def)
    have a_le: "a \<le> Max A"
      using fin a_in by simp
    have min_le_b: "Min A \<le> b"
      using fin b_in by simp
    have "x \<le> Min A + Max A"
      using x_left a_le by simp
    moreover have "Min A + Max A \<le> x"
      using x_right min_le_b by simp
    ultimately have "x = Min A + Max A"
      by simp
    then show "x \<in> {Min A + Max A}"
      by simp
  qed
next
  have min_in: "Min A \<in> A"
    using fin nonempty by simp
  have max_in: "Max A \<in> A"
    using fin nonempty by simp
  show "{Min A + Max A} \<subseteq>
      affine_image_int (Min A) 1 A \<inter> affine_image_int (Max A) 1 A"
    using min_in max_in by (auto simp: affine_image_int_def add.commute)
qed

lemma endpoint_affine_union_card:
  fixes A :: "int set"
  assumes fin: "finite A" and nonempty: "A \<noteq> {}"
  shows "card (affine_image_int (Min A) 1 A \<union> affine_image_int (Max A) 1 A) =
    2 * card A - 1"
proof -
  let ?L = "affine_image_int (Min A) 1 A"
  let ?R = "affine_image_int (Max A) 1 A"
  have finL: "finite ?L"
    by (rule finite_affine_image_int[OF fin])
  have finR: "finite ?R"
    by (rule finite_affine_image_int[OF fin])
  have cardL: "card ?L = card A"
    by (rule card_affine_image_int[OF fin]) simp
  have cardR: "card ?R = card A"
    by (rule card_affine_image_int[OF fin]) simp
  have inter: "?L \<inter> ?R = {Min A + Max A}"
    by (rule endpoint_affine_images_inter[OF fin nonempty])
  have "card ?L + card ?R = card (?L \<union> ?R) + card (?L \<inter> ?R)"
    by (rule card_Un_Int[OF finL finR])
  then have "card A + card A = card (?L \<union> ?R) + 1"
    using cardL cardR inter by simp
  moreover have "0 < card A"
    using fin nonempty by (simp add: card_gt_0_iff)
  ultimately show ?thesis
    by simp
qed

lemma endpoint_affine_images_inter_two_sets:
  fixes A B :: "int set"
  assumes finA: "finite A" and nonemptyA: "A \<noteq> {}"
  assumes finB: "finite B" and nonemptyB: "B \<noteq> {}"
  shows "affine_image_int (Min A) 1 B \<inter> affine_image_int (Max B) 1 A =
    {Min A + Max B}"
proof
  show "affine_image_int (Min A) 1 B \<inter> affine_image_int (Max B) 1 A \<subseteq>
      {Min A + Max B}"
  proof
    fix x
    assume x_in: "x \<in> affine_image_int (Min A) 1 B \<inter> affine_image_int (Max B) 1 A"
    then obtain b where b_in: "b \<in> B" and x_left: "x = Min A + b"
      by (auto simp: affine_image_int_def)
    from x_in obtain a where a_in: "a \<in> A" and x_right: "x = Max B + a"
      by (auto simp: affine_image_int_def)
    have b_le: "b \<le> Max B"
      using finB b_in by simp
    have min_le_a: "Min A \<le> a"
      using finA a_in by simp
    have "x \<le> Min A + Max B"
      using x_left b_le by simp
    moreover have "Min A + Max B \<le> x"
      using x_right min_le_a by simp
    ultimately have "x = Min A + Max B"
      by simp
    then show "x \<in> {Min A + Max B}"
      by simp
  qed
next
  have min_in: "Min A \<in> A"
    using finA nonemptyA by simp
  have max_in: "Max B \<in> B"
    using finB nonemptyB by simp
  show "{Min A + Max B} \<subseteq>
      affine_image_int (Min A) 1 B \<inter> affine_image_int (Max B) 1 A"
    using min_in max_in by (auto simp: affine_image_int_def add.commute)
qed

lemma card_sumset_ge_card_add_card_minus_one:
  fixes A B :: "int set"
  assumes finA: "finite A" and finB: "finite B"
  assumes nonemptyA: "A \<noteq> {}" and nonemptyB: "B \<noteq> {}"
  shows "card A + card B - 1 \<le> card (sumset A B)"
proof -
  let ?L = "affine_image_int (Min A) 1 B"
  let ?R = "affine_image_int (Max B) 1 A"
  have min_in: "Min A \<in> A"
    using finA nonemptyA by simp
  have max_in: "Max B \<in> B"
    using finB nonemptyB by simp
  have finL: "finite ?L"
    by (rule finite_affine_image_int[OF finB])
  have finR: "finite ?R"
    by (rule finite_affine_image_int[OF finA])
  have cardL: "card ?L = card B"
    by (rule card_affine_image_int[OF finB]) simp
  have cardR: "card ?R = card A"
    by (rule card_affine_image_int[OF finA]) simp
  have inter: "?L \<inter> ?R = {Min A + Max B}"
    by (rule endpoint_affine_images_inter_two_sets[OF finA nonemptyA finB nonemptyB])
  have "card ?L + card ?R = card (?L \<union> ?R) + card (?L \<inter> ?R)"
    by (rule card_Un_Int[OF finL finR])
  then have card_union: "card (?L \<union> ?R) = card A + card B - 1"
    using cardL cardR inter finA nonemptyA by simp
  have union_subset: "?L \<union> ?R \<subseteq> sumset A B"
  proof
    fix x
    assume x_in: "x \<in> ?L \<union> ?R"
    then show "x \<in> sumset A B"
    proof
      assume "x \<in> ?L"
      then obtain b where b_in: "b \<in> B" and x_eq: "x = Min A + b"
        by (auto simp: affine_image_int_def)
      then show ?thesis
        using min_in by (auto intro: sumsetI)
    next
      assume "x \<in> ?R"
      then obtain a where a_in: "a \<in> A" and x_eq: "x = Max B + a"
        by (auto simp: affine_image_int_def)
      have "a + Max B \<in> sumset A B"
        using a_in max_in by (rule sumsetI)
      then show ?thesis
        using x_eq by (simp add: add.commute)
    qed
  qed
  have "card (?L \<union> ?R) \<le> card (sumset A B)"
    by (rule card_mono[OF finite_sumset[OF finA finB] union_subset])
  with card_union show ?thesis
    by simp
qed

lemma card_sumset_self_ge_two_card_minus_one:
  fixes A :: "int set"
  assumes fin: "finite A" and nonempty: "A \<noteq> {}"
  shows "2 * card A - 1 \<le> card (sumset A A)"
proof -
  let ?L = "affine_image_int (Min A) 1 A"
  let ?R = "affine_image_int (Max A) 1 A"
  have min_in: "Min A \<in> A"
    using fin nonempty by simp
  have max_in: "Max A \<in> A"
    using fin nonempty by simp
  have finL: "finite ?L"
    by (rule finite_affine_image_int[OF fin])
  have finR: "finite ?R"
    by (rule finite_affine_image_int[OF fin])
  have card_union: "card (?L \<union> ?R) = 2 * card A - 1"
    by (rule endpoint_affine_union_card[OF fin nonempty])
  have union_subset: "?L \<union> ?R \<subseteq> sumset A A"
  proof
    fix x
    assume x_in: "x \<in> ?L \<union> ?R"
    then show "x \<in> sumset A A"
    proof
      assume "x \<in> ?L"
      then obtain a where a_in: "a \<in> A" and x_eq: "x = Min A + a"
        by (auto simp: affine_image_int_def)
      then show ?thesis
        using min_in by (auto intro: sumsetI)
    next
      assume "x \<in> ?R"
      then obtain a where a_in: "a \<in> A" and x_eq: "x = Max A + a"
        by (auto simp: affine_image_int_def)
      then show ?thesis
        using max_in by (auto intro: sumsetI)
    qed
  qed
  have "card (?L \<union> ?R) \<le> card (sumset A A)"
    by (rule card_mono[OF finite_sumset[OF fin fin] union_subset])
  with card_union show ?thesis
    by simp
qed

subsection \<open>Holes in the normalized interval\<close>

definition interval_holes :: "int set \<Rightarrow> int set" where
  "interval_holes A = {x. 0 \<le> x \<and> x \<le> Max A \<and> x \<notin> A}"

definition lower_sum_holes :: "int set \<Rightarrow> int set" where
  "lower_sum_holes A = {x \<in> interval_holes A. x \<in> sumset A A}"

definition upper_sum_holes :: "int set \<Rightarrow> int set" where
  "upper_sum_holes A = {x \<in> interval_holes A. Max A + x \<in> sumset A A}"

definition stable_sum_holes :: "int set \<Rightarrow> int set" where
  "stable_sum_holes A =
    interval_holes A - (lower_sum_holes A \<union> upper_sum_holes A)"

definition left_stable_sum_holes :: "int set \<Rightarrow> int set" where
  "left_stable_sum_holes A = interval_holes A - lower_sum_holes A"

definition right_stable_sum_holes :: "int set \<Rightarrow> int set" where
  "right_stable_sum_holes A = interval_holes A - upper_sum_holes A"

lemma finite_interval_holes [simp]:
  "finite (interval_holes A)"
proof -
  have "interval_holes A \<subseteq> {0..Max A}"
    by (auto simp: interval_holes_def)
  then show ?thesis
    by (rule finite_subset) simp
qed

lemma finite_lower_sum_holes [simp]:
  "finite (lower_sum_holes A)"
  unfolding lower_sum_holes_def by simp

lemma finite_upper_sum_holes [simp]:
  "finite (upper_sum_holes A)"
  unfolding upper_sum_holes_def by simp

lemma finite_stable_sum_holes [simp]:
  "finite (stable_sum_holes A)"
  unfolding stable_sum_holes_def by simp

lemma finite_left_stable_sum_holes [simp]:
  "finite (left_stable_sum_holes A)"
  unfolding left_stable_sum_holes_def by simp

lemma finite_right_stable_sum_holes [simp]:
  "finite (right_stable_sum_holes A)"
  unfolding right_stable_sum_holes_def by simp

lemma stable_sum_holes_eq_left_right_inter:
  "stable_sum_holes A =
    left_stable_sum_holes A \<inter> right_stable_sum_holes A"
  by (auto simp: stable_sum_holes_def left_stable_sum_holes_def right_stable_sum_holes_def)

lemma left_stable_sum_hole_notin_sumset:
  assumes x_left: "x \<in> left_stable_sum_holes A"
  shows "x \<in> interval_holes A" "x \<notin> sumset A A"
proof -
  show x_hole: "x \<in> interval_holes A"
    using x_left by (simp add: left_stable_sum_holes_def)
  show "x \<notin> sumset A A"
  proof
    assume "x \<in> sumset A A"
    with x_hole have "x \<in> lower_sum_holes A"
      by (simp add: lower_sum_holes_def)
    with x_left show False
      by (simp add: left_stable_sum_holes_def)
  qed
qed

lemma right_stable_sum_hole_notin_sumset:
  assumes x_right: "x \<in> right_stable_sum_holes A"
  shows "x \<in> interval_holes A" "Max A + x \<notin> sumset A A"
proof -
  show x_hole: "x \<in> interval_holes A"
    using x_right by (simp add: right_stable_sum_holes_def)
  show "Max A + x \<notin> sumset A A"
  proof
    assume "Max A + x \<in> sumset A A"
    with x_hole have "x \<in> upper_sum_holes A"
      by (simp add: upper_sum_holes_def)
    with x_right show False
      by (simp add: right_stable_sum_holes_def)
  qed
qed

lemma left_stable_hole_prefix_card_le_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes x_left: "x \<in> left_stable_sum_holes A"
  shows "card (A \<inter> {0..x}) \<le> card ({0..x} - A)"
proof -
  let ?P = "A \<inter> {0..x}"
  let ?Q = "{0..x} - A"
  let ?f = "\<lambda>a. x - a"
  have x_not_sum: "x \<notin> sumset A A"
    by (rule left_stable_sum_hole_notin_sumset(2)[OF x_left])
  have image_sub: "?f ` ?P \<subseteq> ?Q"
  proof
    fix y
    assume "y \<in> ?f ` ?P"
    then obtain a where a_in: "a \<in> A" and a_bounds: "0 \<le> a" "a \<le> x" and y_eq: "y = x - a"
      by auto
    have y_bounds: "0 \<le> y" "y \<le> x"
      using a_bounds y_eq by auto
    have "y \<notin> A"
    proof
      assume y_in: "y \<in> A"
      have "a + y \<in> sumset A A"
        using a_in y_in by (rule sumsetI)
      moreover have "a + y = x"
        using y_eq by simp
      ultimately show False
        using x_not_sum by simp
    qed
    with y_bounds show "y \<in> ?Q"
      by simp
  qed
  have inj: "inj_on ?f ?P"
    by (rule inj_onI) simp
  have finP: "finite ?P"
    using fin by simp
  have "card ?P = card (?f ` ?P)"
    by (simp add: card_image finP inj)
  also have "\<dots> \<le> card ?Q"
    by (rule card_mono[OF _ image_sub]) simp
  finally show ?thesis .
qed

lemma left_stable_hole_prefix_twice_card_le:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes x_left: "x \<in> left_stable_sum_holes A"
  shows "2 * card (A \<inter> {0..x}) \<le> nat (x + 1)"
proof -
  let ?P = "A \<inter> {0..x}"
  let ?Q = "{0..x} - A"
  have x_hole: "x \<in> interval_holes A"
    by (rule left_stable_sum_hole_notin_sumset(1)[OF x_left])
  then have x_nonneg: "0 \<le> x"
    by (simp add: interval_holes_def)
  have P_sub: "?P \<subseteq> {0..x}"
    by simp
  have Q_eq: "?Q = {0..x} - ?P"
    by auto
  have cardQ: "card ?Q = card {0..x} - card ?P"
    by (simp add: Q_eq card_Diff_subset[OF _ P_sub])
  have prefix_le: "card ?P \<le> card ?Q"
    by (rule left_stable_hole_prefix_card_le_holes[OF fin x_left])
  have P_card_le: "card ?P \<le> card {0..x}"
    by (rule card_mono[OF _ P_sub]) simp
  have "2 * card ?P \<le> card {0..x}"
    using prefix_le cardQ P_card_le by linarith
  also have "\<dots> = nat (x + 1)"
    using x_nonneg by simp
  finally show ?thesis .
qed

lemma right_stable_hole_suffix_card_le_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes x_right: "x \<in> right_stable_sum_holes A"
  shows "card (A \<inter> {x..Max A}) \<le> card ({x..Max A} - A)"
proof -
  let ?n = "Max A"
  let ?P = "A \<inter> {x..?n}"
  let ?Q = "{x..?n} - A"
  let ?f = "\<lambda>a. ?n + x - a"
  have nx_not_sum: "?n + x \<notin> sumset A A"
    by (rule right_stable_sum_hole_notin_sumset(2)[OF x_right])
  have image_sub: "?f ` ?P \<subseteq> ?Q"
  proof
    fix y
    assume "y \<in> ?f ` ?P"
    then obtain a where a_in: "a \<in> A" and a_bounds: "x \<le> a" "a \<le> ?n"
      and y_eq: "y = ?n + x - a"
      by auto
    have y_bounds: "x \<le> y" "y \<le> ?n"
      using a_bounds y_eq by auto
    have "y \<notin> A"
    proof
      assume y_in: "y \<in> A"
      have "a + y \<in> sumset A A"
        using a_in y_in by (rule sumsetI)
      moreover have "a + y = ?n + x"
        using y_eq by simp
      ultimately show False
        using nx_not_sum by simp
    qed
    with y_bounds show "y \<in> ?Q"
      by simp
  qed
  have inj: "inj_on ?f ?P"
    by (rule inj_onI) simp
  have finP: "finite ?P"
    using fin by simp
  have "card ?P = card (?f ` ?P)"
    by (simp add: card_image finP inj)
  also have "\<dots> \<le> card ?Q"
    by (rule card_mono[OF _ image_sub]) simp
  finally show ?thesis .
qed

lemma right_stable_hole_suffix_twice_card_le:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes x_right: "x \<in> right_stable_sum_holes A"
  shows "2 * card (A \<inter> {x..Max A}) \<le> nat (Max A - x + 1)"
proof -
  let ?n = "Max A"
  let ?P = "A \<inter> {x..?n}"
  let ?Q = "{x..?n} - A"
  have x_hole: "x \<in> interval_holes A"
    by (rule right_stable_sum_hole_notin_sumset(1)[OF x_right])
  then have x_le: "x \<le> ?n"
    by (simp add: interval_holes_def)
  have P_sub: "?P \<subseteq> {x..?n}"
    by simp
  have Q_eq: "?Q = {x..?n} - ?P"
    by auto
  have cardQ: "card ?Q = card {x..?n} - card ?P"
    by (simp add: Q_eq card_Diff_subset[OF _ P_sub])
  have suffix_le: "card ?P \<le> card ?Q"
    by (rule right_stable_hole_suffix_card_le_holes[OF fin x_right])
  have P_card_le: "card ?P \<le> card {x..?n}"
    by (rule card_mono[OF _ P_sub]) simp
  have "2 * card ?P \<le> card {x..?n}"
    using suffix_le cardQ P_card_le by linarith
  also have "\<dots> = nat (?n - x + 1)"
    using x_le by simp
  finally show ?thesis .
qed

lemma hole_cover_of_no_stable_sum_holes:
  assumes stable_empty: "stable_sum_holes A = {}"
  shows "card (interval_holes A) \<le> card (lower_sum_holes A) + card (upper_sum_holes A)"
proof -
  have subset: "interval_holes A \<subseteq> lower_sum_holes A \<union> upper_sum_holes A"
    using stable_empty by (auto simp: stable_sum_holes_def)
  have "card (interval_holes A) \<le> card (lower_sum_holes A \<union> upper_sum_holes A)"
    by (rule card_mono[OF finite_UnI[OF finite_lower_sum_holes finite_upper_sum_holes] subset])
  also have "\<dots> \<le> card (lower_sum_holes A) + card (upper_sum_holes A)"
    by (rule card_Un_le)
  finally show ?thesis .
qed

lemma interval_holes_eq_interval_diff:
  assumes subset: "A \<subseteq> {0..Max A}"
  shows "interval_holes A = {0..Max A} - A"
  using subset by (auto simp: interval_holes_def)

lemma normalized_subset_interval:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "A \<subseteq> {0..Max A}"
proof
  fix x
  assume x_in: "x \<in> A"
  have "0 \<le> x"
    by (rule nonneg[OF x_in])
  moreover have "x \<le> Max A"
    using fin x_in by simp
  ultimately show "x \<in> {0..Max A}"
    by simp
qed

lemma card_interval_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "card (interval_holes A) = nat (Max A + 1) - card A"
proof -
  have subset: "A \<subseteq> {0..Max A}"
    by (rule normalized_subset_interval[OF fin zero nonneg])
  have max_nonneg: "0 \<le> Max A"
    using fin zero by simp
  have "card (interval_holes A) = card ({0..Max A} - A)"
    by (simp add: interval_holes_eq_interval_diff[OF subset])
  also have "\<dots> = card {0..Max A} - card A"
    by (rule card_Diff_subset[OF fin subset])
  also have "\<dots> = nat (Max A + 1) - card A"
    using max_nonneg by simp
  finally show ?thesis .
qed

lemma Min_eq_zero_of_zero_mem_nonneg:
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "Min A = 0"
proof (rule antisym)
  show "Min A \<le> 0"
    using fin zero by simp
next
  have "A \<noteq> {}"
    using zero by auto
  then have "Min A \<in> A"
    using fin by simp
  then show "0 \<le> Min A"
    by (rule nonneg)
qed

lemma normalized_endpoint_union_card:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "card (A \<union> affine_image_int (Max A) 1 A) = 2 * card A - 1"
proof -
  have nonempty: "A \<noteq> {}"
    using zero by auto
  have min0: "Min A = 0"
    by (rule Min_eq_zero_of_zero_mem_nonneg[OF fin zero nonneg])
  have "card (affine_image_int (Min A) 1 A \<union> affine_image_int (Max A) 1 A) =
      2 * card A - 1"
    by (rule endpoint_affine_union_card[OF fin nonempty])
  then show ?thesis
    by (simp add: min0)
qed

lemma lower_sum_holes_disjoint_endpoint_union:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "(A \<union> affine_image_int (Max A) 1 A) \<inter> lower_sum_holes A = {}"
proof
  show "(A \<union> affine_image_int (Max A) 1 A) \<inter> lower_sum_holes A \<subseteq> {}"
  proof
    fix x
    assume x_in: "x \<in> (A \<union> affine_image_int (Max A) 1 A) \<inter> lower_sum_holes A"
    then have x_hole: "x \<in> interval_holes A"
      by (simp add: lower_sum_holes_def)
    then have x_notin_A: "x \<notin> A" and x_le: "x \<le> Max A"
      by (auto simp: interval_holes_def)
    from x_in have x_base: "x \<in> A \<union> affine_image_int (Max A) 1 A"
      by simp
    then show "x \<in> {}"
    proof
      assume "x \<in> A"
      with x_notin_A show ?thesis
        by simp
    next
      assume "x \<in> affine_image_int (Max A) 1 A"
      then obtain a where a_in: "a \<in> A" and x_eq: "x = Max A + a"
        by (auto simp: affine_image_int_def)
      have "0 \<le> a"
        by (rule nonneg[OF a_in])
      with x_eq x_le have a0: "a = 0"
        by simp
      have "Max A \<in> A"
        using fin zero Max_in by fastforce
      with x_notin_A x_eq a0 show ?thesis
        by simp
    qed
  qed
qed simp

lemma upper_sum_holes_image_disjoint_endpoint_union:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "(A \<union> affine_image_int (Max A) 1 A) \<inter>
    affine_image_int (Max A) 1 (upper_sum_holes A) = {}"
proof
  show "(A \<union> affine_image_int (Max A) 1 A) \<inter>
      affine_image_int (Max A) 1 (upper_sum_holes A) \<subseteq> {}"
  proof
    fix y
    assume y_in: "y \<in> (A \<union> affine_image_int (Max A) 1 A) \<inter>
        affine_image_int (Max A) 1 (upper_sum_holes A)"
    then obtain x where x_upper: "x \<in> upper_sum_holes A" and y_eq: "y = Max A + x"
      by (auto simp: affine_image_int_def)
    then have x_hole: "x \<in> interval_holes A"
      by (simp add: upper_sum_holes_def)
    then have x_nonneg: "0 \<le> x" and x_notin_A: "x \<notin> A"
      by (auto simp: interval_holes_def)
    from y_in have y_base: "y \<in> A \<union> affine_image_int (Max A) 1 A"
      by simp
    then show "y \<in> {}"
    proof
      assume yA: "y \<in> A"
      have y_le: "y \<le> Max A"
        using fin yA by simp
      with y_eq x_nonneg have x0: "x = 0"
        by simp
      with zero x_notin_A show ?thesis
        by simp
    next
      assume "y \<in> affine_image_int (Max A) 1 A"
      then obtain a where a_in: "a \<in> A" and ya: "y = Max A + a"
        by (auto simp: affine_image_int_def)
      from y_eq ya have "x = a"
        by simp
      with x_notin_A a_in show ?thesis
        by simp
    qed
  qed
qed simp

lemma lower_sum_holes_disjoint_upper_sum_holes_image:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "lower_sum_holes A \<inter> affine_image_int (Max A) 1 (upper_sum_holes A) = {}"
proof
  show "lower_sum_holes A \<inter> affine_image_int (Max A) 1 (upper_sum_holes A) \<subseteq> {}"
  proof
    fix y
    assume y_in: "y \<in> lower_sum_holes A \<inter> affine_image_int (Max A) 1 (upper_sum_holes A)"
    then have y_hole: "y \<in> interval_holes A"
      by (simp add: lower_sum_holes_def)
    then have y_le: "y \<le> Max A" and y_notin_A: "y \<notin> A"
      by (auto simp: interval_holes_def)
    from y_in obtain x where x_upper: "x \<in> upper_sum_holes A" and y_eq: "y = Max A + x"
      by (auto simp: affine_image_int_def)
    then have x_hole: "x \<in> interval_holes A"
      by (simp add: upper_sum_holes_def)
    then have x_nonneg: "0 \<le> x" and x_notin_A: "x \<notin> A"
      by (auto simp: interval_holes_def)
    with y_eq y_le have x0: "x = 0"
      by simp
    with zero x_notin_A show "y \<in> {}"
      by simp
  qed
qed simp

lemma normalized_sumset_lower_bound_with_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "2 * card A - 1 + card (lower_sum_holes A) + card (upper_sum_holes A)
    \<le> card (sumset A A)"
proof -
  let ?B = "A \<union> affine_image_int (Max A) 1 A"
  let ?L = "lower_sum_holes A"
  let ?U = "affine_image_int (Max A) 1 (upper_sum_holes A)"
  let ?S = "?B \<union> ?L \<union> ?U"
  have nonempty: "A \<noteq> {}"
    using zero by auto
  have max_in: "Max A \<in> A"
    using fin nonempty by simp
  have finB: "finite ?B"
    by (rule finite_UnI[OF fin finite_affine_image_int[OF fin]])
  have finL: "finite ?L"
    by simp
  have finU: "finite ?U"
    by (rule finite_affine_image_int) simp
  have cardB: "card ?B = 2 * card A - 1"
    by (rule normalized_endpoint_union_card[OF fin zero nonneg])
  have cardU: "card ?U = card (upper_sum_holes A)"
    by (rule card_affine_image_int) simp_all
  have BL_disj: "?B \<inter> ?L = {}"
    by (rule lower_sum_holes_disjoint_endpoint_union[OF fin zero nonneg])
  have BU_disj: "?B \<inter> ?U = {}"
    by (rule upper_sum_holes_image_disjoint_endpoint_union[OF fin zero nonneg])
  have LU_disj: "?L \<inter> ?U = {}"
    by (rule lower_sum_holes_disjoint_upper_sum_holes_image[OF fin zero nonneg])
  have BL_card: "card (?B \<union> ?L) = card ?B + card ?L"
    by (rule card_Un_disjoint[OF finB finL BL_disj])
  have BL_U_disj: "(?B \<union> ?L) \<inter> ?U = {}"
    using BU_disj LU_disj by auto
  have cardS: "card ?S = 2 * card A - 1 + card ?L + card (upper_sum_holes A)"
  proof -
    have "card ?S = card (?B \<union> ?L) + card ?U"
      by (rule card_Un_disjoint[OF finite_UnI[OF finB finL] finU BL_U_disj])
    also have "\<dots> = card ?B + card ?L + card ?U"
      using BL_card by simp
    also have "\<dots> = 2 * card A - 1 + card ?L + card (upper_sum_holes A)"
      using cardB cardU by simp
    finally show ?thesis .
  qed
  have S_subset: "?S \<subseteq> sumset A A"
  proof
    fix y
    assume y_in: "y \<in> ?S"
    then show "y \<in> sumset A A"
    proof
      assume yBL: "y \<in> ?B \<union> ?L"
      then show ?thesis
      proof
        assume yB: "y \<in> ?B"
        then show ?thesis
        proof
          assume yA: "y \<in> A"
          have "0 + y \<in> sumset A A"
          proof (rule sumsetI)
            show "0 \<in> A"
              by (rule zero)
            show "y \<in> A"
              by (rule yA)
          qed
          then show ?thesis
            by simp
        next
          assume "y \<in> affine_image_int (Max A) 1 A"
          then obtain a where a_in: "a \<in> A" and y_eq: "y = Max A + a"
            by (auto simp: affine_image_int_def)
          have "Max A + a \<in> sumset A A"
            using max_in a_in by (rule sumsetI)
          then show ?thesis
            using y_eq by simp
        qed
      next
        assume "y \<in> ?L"
        then show ?thesis
          by (simp add: lower_sum_holes_def)
      qed
    next
      assume "y \<in> ?U"
      then obtain x where x_in: "x \<in> upper_sum_holes A" and y_eq: "y = Max A + x"
        by (auto simp: affine_image_int_def)
      then have "Max A + x \<in> sumset A A"
        by (simp add: upper_sum_holes_def)
      then show ?thesis
        using y_eq by simp
    qed
  qed
  have "card ?S \<le> card (sumset A A)"
    by (rule card_mono[OF finite_sumset[OF fin fin] S_subset])
  with cardS show ?thesis
    by simp
qed

lemma normalized_sumset_eq_endpoint_union_with_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "sumset A A =
    A \<union> affine_image_int (Max A) 1 A \<union>
    lower_sum_holes A \<union>
    affine_image_int (Max A) 1 (upper_sum_holes A)"
proof
  let ?n = "Max A"
  have nonempty: "A \<noteq> {}"
    using zero by auto
  have top: "?n \<in> A"
    using fin nonempty by simp
  have subset: "A \<subseteq> {0..?n}"
    by (rule normalized_subset_interval[OF fin zero nonneg])
  show "sumset A A \<subseteq>
      A \<union> affine_image_int ?n 1 A \<union>
      lower_sum_holes A \<union>
      affine_image_int ?n 1 (upper_sum_holes A)"
  proof
    fix y
    assume y_in: "y \<in> sumset A A"
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> A" and y_eq: "y = a + b"
      by (rule sumsetE)
    have a_bounds: "0 \<le> a" "a \<le> ?n"
      using subset a_in by auto
    have b_bounds: "0 \<le> b" "b \<le> ?n"
      using subset b_in by auto
    show "y \<in>
        A \<union> affine_image_int ?n 1 A \<union>
        lower_sum_holes A \<union>
        affine_image_int ?n 1 (upper_sum_holes A)"
    proof (cases "y \<le> ?n")
      case True
      show ?thesis
      proof (cases "y \<in> A")
        case True
        then show ?thesis
          by simp
      next
        case False
        have "y \<in> interval_holes A"
          using y_eq a_bounds b_bounds True False by (auto simp: interval_holes_def)
        then have "y \<in> lower_sum_holes A"
          using y_in by (simp add: lower_sum_holes_def)
        then show ?thesis
          by simp
      qed
    next
      case False
      let ?x = "y - ?n"
      have y_split: "y = ?n + ?x"
        by simp
      have x_pos: "0 < ?x"
        using False by simp
      have x_le: "?x \<le> ?n"
        using y_eq a_bounds b_bounds by linarith
      show ?thesis
      proof (cases "?x \<in> A")
        case True
        have "y \<in> affine_image_int ?n 1 A"
          unfolding affine_image_int_def
        proof (rule image_eqI[where x = "?x"])
          show "y = ?n + 1 * ?x"
            using y_split by simp
          show "?x \<in> A"
            by (rule True)
        qed
        then show ?thesis
          by simp
      next
        case False
        have x_hole: "?x \<in> interval_holes A"
          using x_pos x_le False by (auto simp: interval_holes_def)
        have x_upper: "?x \<in> upper_sum_holes A"
          using x_hole y_in by (simp add: upper_sum_holes_def)
        have "y \<in> affine_image_int ?n 1 (upper_sum_holes A)"
          unfolding affine_image_int_def
        proof (rule image_eqI[where x = "?x"])
          show "y = ?n + 1 * ?x"
            using y_split by simp
          show "?x \<in> upper_sum_holes A"
            by (rule x_upper)
        qed
        then show ?thesis
          by simp
      qed
    qed
  qed
  show "A \<union> affine_image_int ?n 1 A \<union>
      lower_sum_holes A \<union>
      affine_image_int ?n 1 (upper_sum_holes A) \<subseteq> sumset A A"
  proof
    fix y
    assume y_in: "y \<in> A \<union> affine_image_int ?n 1 A \<union>
        lower_sum_holes A \<union>
        affine_image_int ?n 1 (upper_sum_holes A)"
    then show "y \<in> sumset A A"
    proof
      assume y_base_or_lower:
        "y \<in> A \<union> affine_image_int ?n 1 A \<union> lower_sum_holes A"
      then show ?thesis
      proof
        assume y_base: "y \<in> A \<union> affine_image_int ?n 1 A"
        then show ?thesis
        proof
          assume yA: "y \<in> A"
          have "0 + y \<in> sumset A A"
            using zero yA by (rule sumsetI)
          then show ?thesis
            by simp
        next
          assume "y \<in> affine_image_int ?n 1 A"
          then obtain a where a_in: "a \<in> A" and y_eq: "y = ?n + a"
            by (auto simp: affine_image_int_def)
          have "?n + a \<in> sumset A A"
            using top a_in by (rule sumsetI)
          then show ?thesis
            using y_eq by simp
        qed
      next
        assume "y \<in> lower_sum_holes A"
        then show ?thesis
          by (simp add: lower_sum_holes_def)
      qed
    next
      assume "y \<in> affine_image_int ?n 1 (upper_sum_holes A)"
      then obtain x where x_upper: "x \<in> upper_sum_holes A" and y_eq: "y = ?n + x"
        by (auto simp: affine_image_int_def)
      then have "?n + x \<in> sumset A A"
        by (simp add: upper_sum_holes_def)
      then show ?thesis
        using y_eq by simp
    qed
  qed
qed

lemma normalized_sumset_card_eq_with_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "card (sumset A A) =
    2 * card A - 1 + card (lower_sum_holes A) + card (upper_sum_holes A)"
proof -
  let ?B = "A \<union> affine_image_int (Max A) 1 A"
  let ?L = "lower_sum_holes A"
  let ?U = "affine_image_int (Max A) 1 (upper_sum_holes A)"
  let ?S = "?B \<union> ?L \<union> ?U"
  have finB: "finite ?B"
    by (rule finite_UnI[OF fin finite_affine_image_int[OF fin]])
  have finL: "finite ?L"
    by simp
  have finU: "finite ?U"
    by (rule finite_affine_image_int) simp
  have cardB: "card ?B = 2 * card A - 1"
    by (rule normalized_endpoint_union_card[OF fin zero nonneg])
  have cardU: "card ?U = card (upper_sum_holes A)"
    by (rule card_affine_image_int) simp_all
  have BL_disj: "?B \<inter> ?L = {}"
    by (rule lower_sum_holes_disjoint_endpoint_union[OF fin zero nonneg])
  have BU_disj: "?B \<inter> ?U = {}"
    by (rule upper_sum_holes_image_disjoint_endpoint_union[OF fin zero nonneg])
  have LU_disj: "?L \<inter> ?U = {}"
    by (rule lower_sum_holes_disjoint_upper_sum_holes_image[OF fin zero nonneg])
  have BL_card: "card (?B \<union> ?L) = card ?B + card ?L"
    by (rule card_Un_disjoint[OF finB finL BL_disj])
  have BL_U_disj: "(?B \<union> ?L) \<inter> ?U = {}"
    using BU_disj LU_disj by auto
  have "card (sumset A A) = card ?S"
    by (simp add: normalized_sumset_eq_endpoint_union_with_holes[OF fin zero nonneg])
  also have "\<dots> = card (?B \<union> ?L) + card ?U"
    by (rule card_Un_disjoint[OF finite_UnI[OF finB finL] finU BL_U_disj])
  also have "\<dots> = card ?B + card ?L + card ?U"
    using BL_card by simp
  also have "\<dots> =
      2 * card A - 1 + card (lower_sum_holes A) + card (upper_sum_holes A)"
    using cardB cardU by simp
  finally show ?thesis .
qed

lemma normalized_small_doubling_hole_contribution_upper:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  shows "card (lower_sum_holes A) + card (upper_sum_holes A) \<le> card A - 3"
proof -
  have card_eq:
    "card (sumset A A) =
      2 * card A - 1 + card (lower_sum_holes A) + card (upper_sum_holes A)"
    by (rule normalized_sumset_card_eq_with_holes[OF fin zero nonneg])
  show ?thesis
    using card_eq small_doubling card_ge by linarith
qed

lemma normalized_max_bound_from_hole_contribution:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes hole_cover:
    "card (interval_holes A) \<le> card (lower_sum_holes A) + card (upper_sum_holes A)"
  shows "nat (Max A + 1) \<le> card (sumset A A) - card A + 1"
proof -
  let ?k = "card A"
  let ?s = "card (sumset A A)"
  let ?n = "nat (Max A + 1)"
  let ?h = "card (interval_holes A)"
  let ?l = "card (lower_sum_holes A)"
  let ?u = "card (upper_sum_holes A)"
  have lower: "2 * ?k - 1 + ?l + ?u \<le> ?s"
    by (rule normalized_sumset_lower_bound_with_holes[OF fin zero nonneg])
  have h_bound: "2 * ?k - 1 + ?h \<le> ?s"
    using lower hole_cover by linarith
  have subset: "A \<subseteq> {0..Max A}"
    by (rule normalized_subset_interval[OF fin zero nonneg])
  have max_nonneg: "0 \<le> Max A"
    using fin zero by simp
  have k_le_n: "?k \<le> ?n"
  proof -
    have "?k \<le> card {0..Max A}"
      by (rule card_mono[OF _ subset]) simp
    also have "\<dots> = ?n"
      using max_nonneg by simp
    finally show ?thesis .
  qed
  have h_eq: "?h = ?n - ?k"
    by (rule card_interval_holes[OF fin zero nonneg])
  have k_pos: "0 < ?k"
    using fin zero by (simp add: card_gt_0_iff, blast)
  have n_eq: "?n = ?h + ?k"
    using h_eq k_le_n by linarith
  have n_plus: "?n + ?k - 1 = 2 * ?k - 1 + ?h"
    using n_eq k_pos by linarith
  have "?n + ?k - 1 \<le> ?s"
    using h_bound n_plus by simp
  moreover note k_pos
  ultimately show ?thesis
    by linarith
qed

subsection \<open>Modular shadows of integer sumsets\<close>

definition mod_image_int :: "int \<Rightarrow> int set \<Rightarrow> int set" where
  "mod_image_int n A = (\<lambda>x. x mod n) ` A"

definition mod_sumset_int :: "int \<Rightarrow> int set \<Rightarrow> int set \<Rightarrow> int set" where
  "mod_sumset_int n A B = mod_image_int n (sumset A B)"

definition mod_translate_int :: "int \<Rightarrow> int \<Rightarrow> int set \<Rightarrow> int set" where
  "mod_translate_int n a H = (\<lambda>h. (a + h) mod n) ` H"

definition mod_fiber_int :: "int \<Rightarrow> int set \<Rightarrow> int \<Rightarrow> int set" where
  "mod_fiber_int n S r = {s \<in> S. s mod n = r}"

lemma mod_image_int_iff:
  "r \<in> mod_image_int n A \<longleftrightarrow> (\<exists>a\<in>A. r = a mod n)"
  by (auto simp: mod_image_int_def)

lemma finite_mod_image_int [intro]:
  assumes "finite A"
  shows "finite (mod_image_int n A)"
  using assms by (simp add: mod_image_int_def)

lemma mod_sumset_int_iff:
  "r \<in> mod_sumset_int n A B \<longleftrightarrow> (\<exists>a\<in>A. \<exists>b\<in>B. r = (a + b) mod n)"
  by (auto simp: mod_sumset_int_def mod_image_int_def sumset_def)

lemma finite_mod_sumset_int [intro]:
  assumes "finite A" "finite B"
  shows "finite (mod_sumset_int n A B)"
  unfolding mod_sumset_int_def
  by (rule finite_mod_image_int) (rule finite_sumset[OF assms])

lemma mod_translate_int_iff:
  "r \<in> mod_translate_int n a H \<longleftrightarrow> (\<exists>h\<in>H. r = (a + h) mod n)"
  by (auto simp: mod_translate_int_def)

lemma finite_mod_translate_int [intro]:
  assumes "finite H"
  shows "finite (mod_translate_int n a H)"
  using assms by (simp add: mod_translate_int_def)

lemma mod_translate_int_subset_residues:
  assumes n_pos: "0 < n"
  shows "mod_translate_int n a H \<subseteq> {0..n - 1}"
  using n_pos by (auto simp: mod_translate_int_def pos_mod_bound)

lemma mod_add_translate_inj_on_residues:
  fixes a n :: int
  assumes n_pos: "0 < n"
  shows "inj_on (\<lambda>h. (a + h) mod n) {0..n - 1}"
proof (rule inj_onI)
  fix x y
  assume x_in: "x \<in> {0..n - 1}"
  assume y_in: "y \<in> {0..n - 1}"
  assume eq: "(a + x) mod n = (a + y) mod n"
  have x_bounds: "0 \<le> x" "x < n"
    using x_in by auto
  have y_bounds: "0 \<le> y" "y < n"
    using y_in by auto
  have dvd_xy: "n dvd x - y"
    using eq by (simp add: mod_eq_dvd_iff algebra_simps)
  then obtain q where q_eq: "x - y = n * q"
    by (auto elim: dvdE)
  have diff_lower: "- n < x - y"
    using x_bounds y_bounds by linarith
  have diff_upper: "x - y < n"
    using x_bounds y_bounds by linarith
  have "q = 0"
  proof (rule ccontr)
    assume "q \<noteq> 0"
    then consider "1 \<le> q" | "q \<le> -1"
      by linarith
    then show False
    proof cases
      case 1
      then have "n \<le> n * q"
      proof -
        have "1 * n \<le> q * n"
          using 1 n_pos by (intro mult_right_mono) simp_all
        then show ?thesis
          by (simp add: mult.commute)
      qed
      then show False
        using q_eq diff_upper by linarith
    next
      case 2
      then have "n * q \<le> - n"
      proof -
        have "q * n \<le> (-1) * n"
          using 2 n_pos by (intro mult_right_mono) simp_all
        then show ?thesis
          by (simp add: mult.commute)
      qed
      then show False
        using q_eq diff_lower by linarith
    qed
  qed
  then show "x = y"
    using q_eq by simp
qed

lemma card_mod_translate_int_eq:
  fixes H :: "int set"
  assumes n_pos: "0 < n"
  assumes H_sub: "H \<subseteq> {0..n - 1}"
  shows "card (mod_translate_int n a H) = card H"
proof -
  have finH: "finite H"
    using H_sub by (rule finite_subset) simp
  have inj_res: "inj_on (\<lambda>h. (a + h) mod n) {0..n - 1}"
    by (rule mod_add_translate_inj_on_residues[OF n_pos])
  have inj_H: "inj_on (\<lambda>h. (a + h) mod n) H"
    by (rule inj_on_subset[OF inj_res H_sub])
  show ?thesis
    by (simp add: mod_translate_int_def card_image finH inj_H)
qed

lemma sum_coset_lower_upper_inter_card:
  fixes A H :: "int set"
  assumes n_pos: "0 < n"
  assumes finA: "finite A"
  assumes max_eq: "Max A = n"
  assumes H_sub: "H \<subseteq> {0..n - 1}"
  assumes zero_H: "0 \<in> H"
  assumes add_closed: "\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> (x + y) mod n \<in> H"
  assumes b_in: "b \<in> A" and b_bounds: "0 \<le> b" "b < n"
  assumes c_in: "c \<in> A" and c_bounds: "0 \<le> c" "c < n"
  defines "R \<equiv> mod_translate_int n b H"
  defines "S \<equiv> mod_translate_int n c H"
  defines "K \<equiv> mod_translate_int n ((b + c) mod n) H"
  assumes K_disj: "K \<inter> A = {}"
  shows "card H \<le>
    1 + card ((lower_sum_holes A \<inter> upper_sum_holes A) \<inter> K) +
      card (R - A) + card (S - A)"
proof -
  let ?X = "A \<inter> R"
  let ?Y = "A \<inter> S"
  let ?T = "sumset ?X ?Y"
  let ?Low = "?T \<inter> {0..n - 1}"
  let ?High = "?T \<inter> {n..2 * n - 1}"
  let ?Up = "(\<lambda>t. t - n) ` ?High"
  let ?I = "(lower_sum_holes A \<inter> upper_sum_holes A) \<inter> K"
  have finH: "finite H"
    using H_sub by (rule finite_subset) simp
  have R_sub: "R \<subseteq> {0..n - 1}"
    unfolding R_def by (rule mod_translate_int_subset_residues[OF n_pos])
  have S_sub: "S \<subseteq> {0..n - 1}"
    unfolding S_def by (rule mod_translate_int_subset_residues[OF n_pos])
  have K_sub: "K \<subseteq> {0..n - 1}"
    unfolding K_def by (rule mod_translate_int_subset_residues[OF n_pos])
  have finR: "finite R"
    using R_sub by (rule finite_subset) simp
  have finS: "finite S"
    using S_sub by (rule finite_subset) simp
  have finK: "finite K"
    using K_sub by (rule finite_subset) simp
  have cardR: "card R = card H"
    unfolding R_def by (rule card_mod_translate_int_eq[OF n_pos H_sub])
  have cardS: "card S = card H"
    unfolding S_def by (rule card_mod_translate_int_eq[OF n_pos H_sub])
  have cardK: "card K = card H"
    unfolding K_def by (rule card_mod_translate_int_eq[OF n_pos H_sub])
  have b_R: "b \<in> R"
    unfolding R_def mod_translate_int_def
  proof (rule image_eqI)
    show "b = (b + 0) mod n"
      using b_bounds n_pos by simp
    show "0 \<in> H"
      by (rule zero_H)
  qed
  have c_S: "c \<in> S"
    unfolding S_def mod_translate_int_def
  proof (rule image_eqI)
    show "c = (c + 0) mod n"
      using c_bounds n_pos by simp
    show "0 \<in> H"
      by (rule zero_H)
  qed
  have X_nonempty: "?X \<noteq> {}"
    using b_in b_R by auto
  have Y_nonempty: "?Y \<noteq> {}"
    using c_in c_S by auto
  have finX: "finite ?X"
    using finA by simp
  have finY: "finite ?Y"
    using finA by simp
  have sum_residue_in_K: "(x + y) mod n \<in> K"
    if x_in: "x \<in> ?X" and y_in: "y \<in> ?Y" for x y
  proof -
    from x_in obtain h where h_in: "h \<in> H" and x_eq: "x = (b + h) mod n"
      by (auto simp: R_def mod_translate_int_def)
    from y_in obtain k where k_in: "k \<in> H" and y_eq: "y = (c + k) mod n"
      by (auto simp: S_def mod_translate_int_def)
    have hk_in: "(h + k) mod n \<in> H"
      by (rule add_closed[OF h_in k_in])
    have "(x + y) mod n = (b + c + ((h + k) mod n)) mod n"
    proof -
      have "(x + y) mod n = ((b + h) + (c + k)) mod n"
        using x_eq y_eq by (simp add: mod_simps)
      also have "\<dots> = (b + c + (h + k)) mod n"
        by (simp add: algebra_simps)
      also have "\<dots> = (b + c + ((h + k) mod n)) mod n"
        by (simp add: mod_simps)
      finally show ?thesis .
    qed
    then show ?thesis
      using hk_in by (auto simp: K_def mod_translate_int_def mod_simps algebra_simps)
  qed
  have T_bounds: "0 \<le> t \<and> t \<le> 2 * n - 2" if t_in: "t \<in> ?T" for t
  proof -
    from t_in obtain x y where x_in: "x \<in> ?X" and y_in: "y \<in> ?Y" and t_eq: "t = x + y"
      by (rule sumsetE)
    have x_bounds: "0 \<le> x" "x \<le> n - 1"
      using R_sub x_in by auto
    have y_bounds: "0 \<le> y" "y \<le> n - 1"
      using S_sub y_in by auto
    show ?thesis
      using x_bounds y_bounds t_eq by linarith
  qed
  have T_mod_K: "t mod n \<in> K" if t_in: "t \<in> ?T" for t
  proof -
    from t_in obtain x y where x_in: "x \<in> ?X" and y_in: "y \<in> ?Y" and t_eq: "t = x + y"
      by (rule sumsetE)
    show ?thesis
      using sum_residue_in_K[OF x_in y_in] t_eq by simp
  qed
  have low_sub: "?Low \<subseteq> lower_sum_holes A \<inter> K"
  proof
    fix x
    assume x_in: "x \<in> ?Low"
    then have x_T: "x \<in> ?T" and x_bounds: "0 \<le> x" "x < n"
      by auto
    have x_K: "x \<in> K"
      using T_mod_K[OF x_T] x_bounds n_pos by simp
    have x_not_A: "x \<notin> A"
      using K_disj x_K by auto
    have x_interval: "x \<in> interval_holes A"
      using x_bounds x_not_A by (auto simp: interval_holes_def max_eq)
    have x_sum: "x \<in> sumset A A"
      using x_T by (auto simp: sumset_def)
    show "x \<in> lower_sum_holes A \<inter> K"
      using x_interval x_sum x_K by (auto simp: lower_sum_holes_def)
  qed
  have up_sub: "?Up \<subseteq> upper_sum_holes A \<inter> K"
  proof
    fix x
    assume x_in: "x \<in> ?Up"
    then obtain t where t_high: "t \<in> ?High" and x_eq: "x = t - n"
      by auto
    then have t_T: "t \<in> ?T" and t_bounds: "n \<le> t" "t < 2 * n"
      by auto
    have x_bounds: "0 \<le> x" "x < n"
      using x_eq t_bounds by linarith+
    have t_mod: "t mod n = x"
    proof -
      have "t = n + x"
        using x_eq by simp
      then show ?thesis
        using x_bounds n_pos by simp
    qed
    have x_K: "x \<in> K"
      using T_mod_K[OF t_T] t_mod by simp
    have x_not_A: "x \<notin> A"
      using K_disj x_K by auto
    have x_interval: "x \<in> interval_holes A"
      using x_bounds x_not_A by (auto simp: interval_holes_def max_eq)
    have "n + x \<in> sumset A A"
      using t_T x_eq by (auto simp: sumset_def)
    then show "x \<in> upper_sum_holes A \<inter> K"
      using x_interval x_K by (auto simp: upper_sum_holes_def max_eq)
  qed
  have finT: "finite ?T"
    by (rule finite_sumset[OF finX finY])
  have T_split: "?T = ?Low \<union> ?High"
  proof
    show "?T \<subseteq> ?Low \<union> ?High"
    proof
      fix t
      assume t_in: "t \<in> ?T"
      then have bounds: "0 \<le> t" "t \<le> 2 * n - 2"
        using T_bounds by auto
      show "t \<in> ?Low \<union> ?High"
      proof (cases "t < n")
        case True
        with t_in bounds show ?thesis
          by auto
      next
        case False
        with t_in bounds show ?thesis
          by auto
      qed
    qed
    show "?Low \<union> ?High \<subseteq> ?T"
      by auto
  qed
  have disj_low_high: "?Low \<inter> ?High = {}"
    using n_pos by auto
  have finLow: "finite ?Low"
    using finT by simp
  have finHigh: "finite ?High"
    using finT by simp
  have card_T_split: "card ?T = card ?Low + card ?High"
  proof -
    have "card ?T = card (?Low \<union> ?High)"
      using T_split by simp
    also have "\<dots> = card ?Low + card ?High"
      by (rule card_Un_disjoint[OF finLow finHigh disj_low_high])
    finally show ?thesis .
  qed
  have inj_shift: "inj_on (\<lambda>t. t - n) ?High"
    by (rule inj_onI) simp
  have card_Up: "card ?Up = card ?High"
    by (simp add: card_image finHigh inj_shift)
  have card_T_low_up: "card ?T = card ?Low + card ?Up"
    using card_T_split card_Up by simp
  have low_union_up_sub_K: "?Low \<union> ?Up \<subseteq> K"
    using low_sub up_sub by auto
  have low_inter_up_sub_I: "?Low \<inter> ?Up \<subseteq> ?I"
    using low_sub up_sub by auto
  have finUp: "finite ?Up"
    using finHigh by simp
  have card_low_up_le: "card ?Low + card ?Up \<le> card K + card ?I"
  proof -
    have card_union_inter:
        "card ?Low + card ?Up = card (?Low \<union> ?Up) + card (?Low \<inter> ?Up)"
      by (rule card_Un_Int[OF finLow finUp])
    have "card (?Low \<union> ?Up) \<le> card K"
      by (rule card_mono[OF finK low_union_up_sub_K])
    moreover have "card (?Low \<inter> ?Up) \<le> card ?I"
      by (rule card_mono[OF _ low_inter_up_sub_I]) simp
    ultimately show ?thesis
      using card_union_inter by linarith
  qed
  have card_T_le: "card ?T \<le> card H + card ?I"
    using card_T_low_up card_low_up_le cardK by simp
  have sum_lower: "card ?X + card ?Y - 1 \<le> card ?T"
    by (rule card_sumset_ge_card_add_card_minus_one[OF finX finY X_nonempty Y_nonempty])
  have R_decomp: "R = ?X \<union> (R - A)"
    by auto
  have S_decomp: "S = ?Y \<union> (S - A)"
    by auto
  have R_disj: "?X \<inter> (R - A) = {}"
    by auto
  have S_disj: "?Y \<inter> (S - A) = {}"
    by auto
  have finRdiff: "finite (R - A)"
    using finR by simp
  have finSdiff: "finite (S - A)"
    using finS by simp
  have card_R_decomp: "card R = card ?X + card (R - A)"
  proof -
    have "card R = card (?X \<union> (R - A))"
      using R_decomp by simp
    also have "\<dots> = card ?X + card (R - A)"
      by (rule card_Un_disjoint[OF finX finRdiff R_disj])
    finally show ?thesis .
  qed
  have card_S_decomp: "card S = card ?Y + card (S - A)"
  proof -
    have "card S = card (?Y \<union> (S - A))"
      using S_decomp by simp
    also have "\<dots> = card ?Y + card (S - A)"
      by (rule card_Un_disjoint[OF finY finSdiff S_disj])
    finally show ?thesis .
  qed
  show ?thesis
    using sum_lower card_T_le cardR cardS card_R_decomp card_S_decomp by linarith
qed

lemma mod_fiber_int_subset:
  "mod_fiber_int n S r \<subseteq> S"
  by (auto simp: mod_fiber_int_def)

lemma finite_mod_fiber_int [intro]:
  assumes "finite S"
  shows "finite (mod_fiber_int n S r)"
  using finite_subset[OF mod_fiber_int_subset assms] .

interpretation Zmod: additive_abelian_group "{0..int ((p :: nat) - 1)}"
    "(\<lambda>x y. (x + y) mod int p)" "0::int"
  using additive_abelian_group_def residue_group[of p] by fastforce

lemma zmod_sumset_eq_mod_sumset_int:
  fixes A B :: "int set"
  assumes p_pos: "0 < p"
  assumes A_sub: "A \<subseteq> {0..int p - 1}"
  assumes B_sub: "B \<subseteq> {0..int p - 1}"
  shows "Zmod.sumset p A B = mod_sumset_int (int p) A B"
proof
  have zgroup: "additive_abelian_group {0..int (p - 1)}
      (\<lambda>x y. (x + y) mod int p) (0::int)"
    using additive_abelian_group_def residue_group[of p] by fastforce
  have A_carrier: "A \<subseteq> {0..int (p - 1)}"
    using p_pos A_sub by auto
  have B_carrier: "B \<subseteq> {0..int (p - 1)}"
    using p_pos B_sub by auto
  show "Zmod.sumset p A B \<subseteq> mod_sumset_int (int p) A B"
  proof
    fix x
    assume "x \<in> Zmod.sumset p A B"
    then have "x \<in> {c. \<exists>a \<in> A \<inter> {0..int (p - 1)}.
        \<exists>b \<in> B \<inter> {0..int (p - 1)}. c = (a + b) mod int p}"
      using additive_abelian_group.sumset_eq[OF zgroup, of A B] by auto
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> B"
      and x_eq: "x = (a + b) mod int p"
      by auto
    have "a + b \<in> sumset A B"
      using a_in b_in by (rule sumsetI)
    then show "x \<in> mod_sumset_int (int p) A B"
      using x_eq by (auto simp: mod_sumset_int_def mod_image_int_def)
  qed
  show "mod_sumset_int (int p) A B \<subseteq> Zmod.sumset p A B"
  proof
    fix x
    assume "x \<in> mod_sumset_int (int p) A B"
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> B"
      and x_eq: "x = (a + b) mod int p"
      by (auto simp: mod_sumset_int_iff)
    have a_carrier: "a \<in> {0..int (p - 1)}"
      using A_carrier a_in by auto
    have b_carrier: "b \<in> {0..int (p - 1)}"
      using B_carrier b_in by auto
    have "x \<in> {c. \<exists>a \<in> A \<inter> {0..int (p - 1)}.
        \<exists>b \<in> B \<inter> {0..int (p - 1)}. c = (a + b) mod int p}"
      using a_in a_carrier b_in b_carrier x_eq by blast
    show "x \<in> Zmod.sumset p A B"
      using \<open>x \<in> {c. \<exists>a \<in> A \<inter> {0..int (p - 1)}.
        \<exists>b \<in> B \<inter> {0..int (p - 1)}. c = (a + b) mod int p}\<close>
        additive_abelian_group.sumset_eq[OF zgroup, of A B]
      by auto
  qed
qed

lemma zmod_kneser_self:
  fixes B :: "int set"
  assumes p_pos: "0 < p"
  assumes B_sub: "B \<subseteq> {0..int p - 1}"
  assumes fin: "finite B"
  assumes nonempty: "B \<noteq> {}"
  defines "C \<equiv> Zmod.sumset p B B"
  defines "H \<equiv> Zmod.stabilizer p C"
  shows "card C \<ge> 2 * card (Zmod.sumset p B H) - card H"
proof -
  have B_carrier: "B \<subseteq> {0..int (p - 1)}"
    using p_pos B_sub by auto
  have "card (Zmod.sumset p B H) + card (Zmod.sumset p B H) - card H \<le> card C"
    unfolding C_def H_def
    by (rule Zmod.Kneser[OF B_carrier B_carrier fin fin nonempty nonempty])
  then show ?thesis
    by simp
qed

lemma zmod_sumset_iff:
  "x \<in> Zmod.sumset p A B \<longleftrightarrow>
    (\<exists>a\<in>A \<inter> {0..int (p - 1)}.
      \<exists>b\<in>B \<inter> {0..int (p - 1)}. x = (a + b) mod int p)"
proof -
  have zgroup: "additive_abelian_group {0..int (p - 1)}
      (\<lambda>x y. (x + y) mod int p) (0::int)"
    using additive_abelian_group_def residue_group[of p] by fastforce
  show ?thesis
    using additive_abelian_group.sumset_eq[OF zgroup, of A B] by auto
qed

lemma zmod_singleton_sumset_eq_mod_translate_int:
  assumes p_pos: "0 < p"
  assumes a_carrier: "a \<in> {0..int p - 1}"
  assumes H_sub: "H \<subseteq> {0..int p - 1}"
  shows "Zmod.sumset p {a} H = mod_translate_int (int p) a H"
proof
  have carrier_eq: "{0..int (p - 1)} = {0..int p - 1}"
    using p_pos by auto
  show "Zmod.sumset p {a} H \<subseteq> mod_translate_int (int p) a H"
  proof
    fix x
    assume x_in: "x \<in> Zmod.sumset p {a} H"
    then obtain h where h_in: "h \<in> H" and x_eq: "x = (a + h) mod int p"
      using zmod_sumset_iff[of x p "{a}" H] by blast
    show "x \<in> mod_translate_int (int p) a H"
      using h_in x_eq by (auto simp: mod_translate_int_def)
  qed
  show "mod_translate_int (int p) a H \<subseteq> Zmod.sumset p {a} H"
  proof
    fix x
    assume x_in: "x \<in> mod_translate_int (int p) a H"
    then obtain h where h_in: "h \<in> H" and x_eq: "x = (a + h) mod int p"
      by (auto simp: mod_translate_int_def)
    have a_carrier': "a \<in> {0..int (p - 1)}"
      using a_carrier carrier_eq by simp
    have h_carrier: "h \<in> {0..int (p - 1)}"
      using H_sub h_in carrier_eq by auto
    have "(a + h) mod int p \<in> Zmod.sumset p {a} H"
      by (rule Zmod.sumset.sumsetI) (use a_carrier' h_carrier h_in in auto)
    then show "x \<in> Zmod.sumset p {a} H"
      using x_eq by simp
  qed
qed

lemma zmod_self_sumset_contains_set:
  assumes p_pos: "0 < p"
  assumes B_sub: "B \<subseteq> {0..int p - 1}"
  assumes zero_B: "0 \<in> B"
  shows "B \<subseteq> Zmod.sumset p B B"
proof
  fix b
  assume b_in: "b \<in> B"
  have b_carrier: "b \<in> {0..int (p - 1)}"
    using B_sub b_in p_pos by auto
  have zero_carrier: "0 \<in> {0..int (p - 1)}"
    using p_pos by auto
  have "(b + 0) mod int p \<in> Zmod.sumset p B B"
    by (rule Zmod.sumset.sumsetI[OF b_in b_carrier zero_B zero_carrier])
  then show "b \<in> Zmod.sumset p B B"
    using b_carrier p_pos by simp
qed

lemma zmod_sumset_stabilizer_subset:
  assumes p_pos: "0 < p"
  assumes A_sub_C: "A \<subseteq> C"
  assumes C_sub: "C \<subseteq> {0..int p - 1}"
  shows "Zmod.sumset p A (Zmod.stabilizer p C) \<subseteq> C"
proof
  have carrier_eq: "{0..int (p - 1)} = {0..int p - 1}"
    using p_pos by auto
  fix x
  assume x_in: "x \<in> Zmod.sumset p A (Zmod.stabilizer p C)"
  then obtain a h where a_in: "a \<in> A" and a_carrier: "a \<in> {0..int (p - 1)}"
      and h_in: "h \<in> Zmod.stabilizer p C" and h_carrier: "h \<in> {0..int (p - 1)}"
      and x_eq: "x = (a + h) mod int p"
    using zmod_sumset_iff[of x p A "Zmod.stabilizer p C"] by blast
  have a_C: "a \<in> C"
    using A_sub_C a_in by auto
  have C_sub': "C \<subseteq> {0..int (p - 1)}"
    using C_sub carrier_eq by simp
  have coset_sub: "Zmod.sumset p {a} (Zmod.stabilizer p C) \<subseteq> C"
    by (rule Zmod.stabilizer_coset_subset[OF C_sub' a_C])
  have "x \<in> Zmod.sumset p {a} (Zmod.stabilizer p C)"
  proof -
    have "(a + h) mod int p \<in> Zmod.sumset p {a} (Zmod.stabilizer p C)"
      by (rule Zmod.sumset.sumsetI) (use a_carrier h_in h_carrier in auto)
    then show ?thesis
      using x_eq by simp
  qed
  then show "x \<in> C"
    using coset_sub by auto
qed

lemma zmod_obtain_sum_coset_disjoint_D:
  fixes B :: "int set"
  assumes p_pos: "0 < p"
  assumes B_sub: "B \<subseteq> {0..int p - 1}"
  assumes finB: "finite B"
  assumes zero_B: "0 \<in> B"
  defines "C \<equiv> Zmod.sumset p B B"
  defines "H \<equiv> Zmod.stabilizer p C"
  defines "D \<equiv> Zmod.sumset p B H"
  assumes not_subset: "\<not> B \<subseteq> H"
  obtains b c where "b \<in> B" "c \<in> B" "Zmod.sumset p {((b + c) mod int p)} H \<inter> D = {}"
proof -
  have carrier_eq: "{0..int (p - 1)} = {0..int p - 1}"
    using p_pos by auto
  have exists_coset:
    "\<exists>b c. b \<in> B \<and> c \<in> B \<and> Zmod.sumset p {((b + c) mod int p)} H \<inter> D = {}"
  proof (rule ccontr)
    assume no_coset:
      "\<not> (\<exists>b c. b \<in> B \<and> c \<in> B \<and>
        Zmod.sumset p {((b + c) mod int p)} H \<inter> D = {})"
    then have all_meet:
      "Zmod.sumset p {((b + c) mod int p)} H \<inter> D \<noteq> {}"
      if "b \<in> B" "c \<in> B" for b c
      using that by blast
    have C_sub: "C \<subseteq> {0..int p - 1}"
      unfolding C_def
      using Zmod.sumset_subset_carrier[of p B B] carrier_eq by auto
    have C_sub': "C \<subseteq> {0..int (p - 1)}"
      using C_sub carrier_eq by simp
    have H_sub: "H \<subseteq> {0..int p - 1}"
      unfolding H_def using Zmod.stabilizer_subset_group[of p C] carrier_eq by auto
    have zero_H: "0 \<in> H"
      unfolding H_def by (rule Zmod.zero_mem_stabilizer)
    have B_sub_C: "B \<subseteq> C"
      unfolding C_def by (rule zmod_self_sumset_contains_set[OF p_pos B_sub zero_B])
    have D_sub_C: "D \<subseteq> C"
      unfolding D_def H_def
      by (rule zmod_sumset_stabilizer_subset[OF p_pos B_sub_C C_sub])
    have C_sub_D: "C \<subseteq> D"
    proof
    fix r
    assume r_in: "r \<in> C"
    then obtain b c where b_in: "b \<in> B" and c_in: "c \<in> B"
        and r_eq: "r = (b + c) mod int p"
      unfolding C_def using zmod_sumset_iff[of r p B B] by blast
    have r_carrier: "r \<in> {0..int (p - 1)}"
      using C_sub' r_in by auto
    have coset_meet: "Zmod.sumset p {r} H \<inter> D \<noteq> {}"
      using all_meet[OF b_in c_in] r_eq by simp
    then obtain z where z_r: "z \<in> Zmod.sumset p {r} H" and z_D: "z \<in> D"
      by auto
    from z_D obtain b0 h0 where b0_in: "b0 \<in> B" and h0_in: "h0 \<in> H"
        and z_eq: "z = (b0 + h0) mod int p"
      unfolding D_def using zmod_sumset_iff[of z p B H] by blast
    have b0_carrier: "b0 \<in> {0..int (p - 1)}"
      using B_sub b0_in carrier_eq by auto
    have h0_carrier: "h0 \<in> {0..int (p - 1)}"
      using H_sub h0_in carrier_eq by auto
    have z_b0: "z \<in> Zmod.sumset p {b0} H"
    proof -
      have "(b0 + h0) mod int p \<in> Zmod.sumset p {b0} H"
        by (rule Zmod.sumset.sumsetI) (use b0_carrier h0_carrier h0_in in auto)
      then show ?thesis
        using z_eq by simp
    qed
    have b0_coset_sub_D: "Zmod.sumset p {b0} H \<subseteq> D"
      unfolding D_def
      by (rule Zmod.sumset_mono) (use b0_in in auto)
    have cosets_inter: "Zmod.sumset p {r} H \<inter> Zmod.sumset p {b0} H \<noteq> {}"
      using z_r z_b0 by auto
    have cosets_eq: "Zmod.sumset p {r} H = Zmod.sumset p {b0} H"
      using Zmod.sumset_stabilizer_eq_iff[OF r_carrier b0_carrier, of C] cosets_inter
      by (simp add: H_def)
    have r_in_own: "r \<in> Zmod.sumset p {r} H"
    proof -
      have "(r + 0) mod int p \<in> Zmod.sumset p {r} H"
        by (rule Zmod.sumset.sumsetI) (use r_carrier zero_H p_pos in auto)
      then show ?thesis
        using r_carrier p_pos by simp
    qed
    show "r \<in> D"
      using r_in_own cosets_eq b0_coset_sub_D by auto
  qed
  have C_eq_D: "C = D"
    using C_sub_D D_sub_C by auto
  have finC: "finite C"
    unfolding C_def by (rule Zmod.finite_sumset[OF finB finB])
  have zero_C: "0 \<in> C"
  proof -
    have zero_carrier: "0 \<in> {0..int (p - 1)}"
      using p_pos by auto
    have "(0 + 0) mod int p \<in> Zmod.sumset p B B"
      by (rule Zmod.sumset.sumsetI[OF zero_B zero_carrier zero_B zero_carrier])
    then show ?thesis
      by (simp add: C_def)
  qed
  have C_plus_C: "Zmod.sumset p C C = C"
  proof
    show "Zmod.sumset p C C \<subseteq> C"
    proof
      fix z
      assume z_in: "z \<in> Zmod.sumset p C C"
      then obtain x y where x_in: "x \<in> C" and y_in: "y \<in> C"
          and x_carrier: "x \<in> {0..int (p - 1)}"
          and y_carrier: "y \<in> {0..int (p - 1)}"
          and z_eq: "z = (x + y) mod int p"
        using zmod_sumset_iff[of z p C C] by blast
      from x_in have x_D: "x \<in> D"
        using C_eq_D by simp
      from y_in have y_D: "y \<in> D"
        using C_eq_D by simp
      from x_D obtain b h where b_in: "b \<in> B" and h_in: "h \<in> H"
          and x_eq: "x = (b + h) mod int p"
        unfolding D_def using zmod_sumset_iff[of x p B H] by blast
      from y_D obtain c k where c_in: "c \<in> B" and k_in: "k \<in> H"
          and y_eq: "y = (c + k) mod int p"
        unfolding D_def using zmod_sumset_iff[of y p B H] by blast
      have b_carrier: "b \<in> {0..int (p - 1)}"
        using B_sub b_in carrier_eq by auto
      have c_carrier: "c \<in> {0..int (p - 1)}"
        using B_sub c_in carrier_eq by auto
      have h_carrier: "h \<in> {0..int (p - 1)}"
        using H_sub h_in carrier_eq by auto
      have k_carrier: "k \<in> {0..int (p - 1)}"
        using H_sub k_in carrier_eq by auto
      have bc_C: "(b + c) mod int p \<in> C"
        unfolding C_def by (rule Zmod.sumset.sumsetI[OF b_in b_carrier c_in c_carrier])
      have hk_H: "(h + k) mod int p \<in> H"
      proof -
        interpret Hsub: subgroup H "{0..int (p - 1)}"
            "(\<lambda>x y. (x + y) mod int p)" "0::int"
          unfolding H_def by (rule Zmod.stabilizer_is_subgroup)
        show ?thesis
          by (rule Hsub.sub_composition_closed[OF h_in k_in])
      qed
      have hk_carrier: "(h + k) mod int p \<in> {0..int (p - 1)}"
        using hk_H H_sub carrier_eq by auto
      have bc_carrier: "(b + c) mod int p \<in> {0..int (p - 1)}"
        using bc_C C_sub' by auto
      have z_rewrite:
        "z = (((b + c) mod int p) + ((h + k) mod int p)) mod int p"
      proof -
        have "z = ((b + h) + (c + k)) mod int p"
          using z_eq x_eq y_eq by (simp add: mod_simps)
        also have "\<dots> = (b + c + (h + k)) mod int p"
          by (simp add: algebra_simps)
        also have "\<dots> =
            (((b + c) mod int p) + ((h + k) mod int p)) mod int p"
          by (simp add: mod_add_eq algebra_simps)
        finally show ?thesis .
      qed
      have z_in_CH: "z \<in> Zmod.sumset p C H"
      proof -
        have "(((b + c) mod int p) + ((h + k) mod int p)) mod int p
            \<in> Zmod.sumset p C H"
          by (rule Zmod.sumset.sumsetI[OF bc_C bc_carrier hk_H hk_carrier])
        then show ?thesis
          using z_rewrite by simp
      qed
      have CH_sub_C: "Zmod.sumset p C H \<subseteq> C"
        unfolding H_def
        by (rule zmod_sumset_stabilizer_subset[OF p_pos subset_refl C_sub])
      show "z \<in> C"
        using CH_sub_C z_in_CH by auto
    qed
  next
    show "C \<subseteq> Zmod.sumset p C C"
    proof
      fix x
      assume x_in: "x \<in> C"
      have x_carrier: "x \<in> {0..int (p - 1)}"
        using C_sub' x_in by auto
      have zero_carrier: "0 \<in> {0..int (p - 1)}"
        using p_pos by auto
      have "(x + 0) mod int p \<in> Zmod.sumset p C C"
        by (rule Zmod.sumset.sumsetI[OF x_in x_carrier zero_C zero_carrier])
      then show "x \<in> Zmod.sumset p C C"
        using x_carrier p_pos by simp
    qed
  qed
  have C_sub_H: "C \<subseteq> H"
    unfolding H_def
    by (rule Zmod.sumset_eq_sub_stabilizer[OF C_sub' C_sub' finC C_plus_C])
    have "B \<subseteq> H"
      using B_sub_C C_sub_H by auto
    show False
      using \<open>B \<subseteq> H\<close> not_subset by simp
  qed
  then obtain b c where b_in: "b \<in> B" and c_in: "c \<in> B"
      and disj: "Zmod.sumset p {((b + c) mod int p)} H \<inter> D = {}"
    by blast
  show ?thesis
    by (rule that[OF b_in c_in disj])
qed

lemma mod_image_int_subset_residues:
  assumes n_pos: "0 < n"
  shows "mod_image_int n A \<subseteq> {0..n - 1}"
  using n_pos by (auto simp: mod_image_int_def pos_mod_bound)

lemma mod_sumset_int_mod_image_self:
  assumes n_pos: "0 < n"
  shows "mod_sumset_int n (mod_image_int n A) (mod_image_int n A) =
    mod_sumset_int n A A"
proof
  show "mod_sumset_int n (mod_image_int n A) (mod_image_int n A) \<subseteq>
      mod_sumset_int n A A"
  proof
    fix r
    assume "r \<in> mod_sumset_int n (mod_image_int n A) (mod_image_int n A)"
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> A"
      and r_eq: "r = (a mod n + b mod n) mod n"
      by (auto simp: mod_sumset_int_iff mod_image_int_def)
    have "(a mod n + b mod n) mod n = (a + b) mod n"
      by (simp add: mod_simps)
    then show "r \<in> mod_sumset_int n A A"
      using a_in b_in r_eq by (auto simp: mod_sumset_int_iff)
  qed
  show "mod_sumset_int n A A \<subseteq>
      mod_sumset_int n (mod_image_int n A) (mod_image_int n A)"
  proof
    fix r
    assume "r \<in> mod_sumset_int n A A"
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> A"
      and r_eq: "r = (a + b) mod n"
      by (auto simp: mod_sumset_int_iff)
    have a_mod_in: "a mod n \<in> mod_image_int n A"
      using a_in by (auto simp: mod_image_int_def)
    have b_mod_in: "b mod n \<in> mod_image_int n A"
      using b_in by (auto simp: mod_image_int_def)
    have "r = (a mod n + b mod n) mod n"
      using r_eq by (simp add: mod_simps)
    then show "r \<in> mod_sumset_int n (mod_image_int n A) (mod_image_int n A)"
      using a_mod_in b_mod_in by (auto simp: mod_sumset_int_iff)
  qed
qed

lemma zmod_sumset_trivial_stabilizer_card_ge:
  fixes B :: "int set"
  assumes p_pos: "0 < p"
  assumes B_sub: "B \<subseteq> {0..int p - 1}"
  assumes fin: "finite B"
  assumes nonempty: "B \<noteq> {}"
  defines "C \<equiv> Zmod.sumset p B B"
  assumes trivial: "Zmod.stabilizer p C = {0}"
  shows "2 * card B - 1 \<le> card C"
proof -
  have B_carrier: "B \<subseteq> {0..int (p - 1)}"
    using p_pos B_sub by auto
  have zero_carrier: "{0::int} \<subseteq> {0..int (p - 1)}"
    using p_pos by auto
  have kneser_raw:
    "card (Zmod.sumset p B (Zmod.stabilizer p C)) +
      card (Zmod.sumset p B (Zmod.stabilizer p C)) -
      card (Zmod.stabilizer p C) \<le> card C"
    unfolding C_def
    by (rule Zmod.Kneser[OF B_carrier B_carrier fin fin nonempty nonempty])
  have stabilizer_rewrite:
    "card (Zmod.sumset p B (Zmod.stabilizer p C)) +
      card (Zmod.sumset p B (Zmod.stabilizer p C)) -
      card (Zmod.stabilizer p C) = 2 * card (Zmod.sumset p B {0}) - 1"
    using trivial by simp
  have zero_sumset: "Zmod.sumset p B {0} = B"
  proof -
    have "Zmod.sumset p B {0} = B \<inter> {0..int (p - 1)}"
      by (rule Zmod.sumset_D(1))
    also have "\<dots> = B"
      using B_carrier by auto
    finally show ?thesis .
  qed
  have "2 * card B - 1 =
      card (Zmod.sumset p B (Zmod.stabilizer p C)) +
      card (Zmod.sumset p B (Zmod.stabilizer p C)) -
      card (Zmod.stabilizer p C)"
  proof -
    have "2 * card (Zmod.sumset p B {0}) - 1 = 2 * card B - 1"
      by (subst zero_sumset) simp
    with stabilizer_rewrite show ?thesis
      by simp
  qed
  with kneser_raw show ?thesis
    by simp
qed

lemma zmod_nontrivial_stabilizer_obtain_positive_period:
  fixes C :: "int set"
  assumes p_pos: "0 < p"
  assumes nontrivial: "Zmod.stabilizer p C \<noteq> {0}"
  obtains h where "h \<in> Zmod.stabilizer p C" "0 < h" "h < int p"
proof -
  have zero_in: "0 \<in> Zmod.stabilizer p C"
    by (rule Zmod.zero_mem_stabilizer)
  from nontrivial obtain h where h_in: "h \<in> Zmod.stabilizer p C" and h_ne: "h \<noteq> 0"
    using zero_in by auto
  have h_carrier: "h \<in> {0..int (p - 1)}"
    using h_in Zmod.stabilizer_subset_group[of p C] by auto
  then have h_nonneg: "0 \<le> h" and h_le: "h \<le> int (p - 1)"
    by auto
  have h_pos: "0 < h"
    using h_nonneg h_ne by linarith
  have h_lt: "h < int p"
    using h_le p_pos by linarith
  show ?thesis
    by (rule that[OF h_in h_pos h_lt])
qed

lemma residue_add_closed_mult:
  fixes H :: "int set"
  assumes n_pos: "0 < n"
  assumes zero: "0 \<in> H"
  assumes add_closed: "\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> (x + y) mod n \<in> H"
  assumes h_in: "h \<in> H"
  shows "(int m * h) mod n \<in> H"
proof (induction m)
  case 0
  then show ?case
    using zero by simp
next
  case (Suc m)
  have prev: "(int m * h) mod n \<in> H"
    by (rule Suc.IH)
  have step: "(((int m * h) mod n) + h) mod n \<in> H"
    by (rule add_closed[OF prev h_in])
  have "(((int m * h) mod n) + h) mod n = (int (Suc m) * h) mod n"
    by (simp add: mod_simps algebra_simps)
  with step show ?case
    by simp
qed

lemma residue_add_closed_diff:
  fixes H :: "int set"
  assumes n_pos: "0 < n"
  assumes zero: "0 \<in> H"
  assumes add_closed: "\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> (x + y) mod n \<in> H"
  assumes x_in: "x \<in> H"
  assumes y_in: "y \<in> H"
  shows "(x - y) mod n \<in> H"
proof -
  have neg_y: "(int (nat n - 1) * y) mod n \<in> H"
    by (rule residue_add_closed_mult[OF n_pos zero add_closed y_in])
  have int_pred: "int (nat n - 1) = n - 1"
    using n_pos by simp
  have inH: "((x + ((int (nat n - 1) * y) mod n)) mod n) \<in> H"
    by (rule add_closed[OF x_in neg_y])
  have eq: "((x + ((int (nat n - 1) * y) mod n)) mod n) = (x - y) mod n"
  proof -
    have "((x + ((int (nat n - 1) * y) mod n)) mod n) =
        (x + ((n - 1) * y)) mod n"
      using int_pred by (simp add: mod_simps)
    also have "\<dots> = ((x - y) + n * y) mod n"
      by (simp add: algebra_simps)
    also have "\<dots> = (x - y) mod n"
      by (simp add: mod_simps)
    finally show ?thesis .
  qed
  from inH show ?thesis
    using eq by simp
qed

lemma residue_add_closed_obtain_proper_divisor:
  fixes H :: "int set"
  assumes n_pos: "0 < n"
  assumes H_sub: "H \<subseteq> {0..n - 1}"
  assumes zero: "0 \<in> H"
  assumes add_closed: "\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> (x + y) mod n \<in> H"
  assumes nontrivial: "H \<noteq> {0}"
  assumes proper: "H \<noteq> {0..n - 1}"
  obtains d where "1 < d" "d dvd n" "\<And>h. h \<in> H \<Longrightarrow> d dvd h"
proof -
  let ?S = "H - {0}"
  have finH: "finite H"
    using H_sub by (rule finite_subset) simp
  have finS: "finite ?S"
    using finH by simp
  have nonemptyS: "?S \<noteq> {}"
    using zero nontrivial by auto
  define d where "d = Min ?S"
  have d_inS: "d \<in> ?S"
    unfolding d_def by (rule Min_in[OF finS nonemptyS])
  then have d_in: "d \<in> H" and d_ne_zero: "d \<noteq> 0"
    by auto
  have d_bounds: "0 < d" "d < n"
  proof -
    have "d \<in> {0..n - 1}"
      using H_sub d_in by auto
    then have "0 \<le> d" "d < n"
      by auto
    with d_ne_zero show "0 < d" "d < n"
      by linarith+
  qed
  have dvd_H: "d dvd h" if h_in: "h \<in> H" for h
  proof (cases "h = 0")
    case True
    then show ?thesis
      by simp
  next
    case False
    have h_inS: "h \<in> ?S"
      using h_in False by simp
    have h_bounds: "0 \<le> h" "h < n"
      using H_sub h_in by auto
    have d_le_h: "d \<le> h"
      using Min_le[OF finS h_inS] by (simp add: d_def)
    define q where "q = h div d"
    define r where "r = h mod d"
    have q_nonneg: "0 \<le> q"
      using h_bounds d_bounds by (simp add: q_def pos_imp_zdiv_nonneg_iff)
    have r_bounds: "0 \<le> r" "r < d"
      using d_bounds by (simp_all add: r_def)
    have div_eq: "h = q * d + r"
      by (simp add: q_def r_def)
    have qd_bounds: "0 \<le> q * d" "q * d < n"
      using q_nonneg d_bounds h_bounds div_eq r_bounds by (simp, linarith)
    have qd_mod_in: "(int (nat q) * d) mod n \<in> H"
      by (rule residue_add_closed_mult[OF n_pos zero add_closed d_in])
    have qd_in: "q * d \<in> H"
      using qd_mod_in q_nonneg qd_bounds n_pos by simp
    have r_mod_in: "(h - q * d) mod n \<in> H"
      by (rule residue_add_closed_diff[OF n_pos zero add_closed h_in qd_in])
    have r_eq: "h - q * d = r"
      using div_eq by simp
    have r_in: "r \<in> H"
      using r_mod_in r_eq r_bounds d_bounds n_pos by simp
    have "r = 0"
    proof (rule ccontr)
      assume "r \<noteq> 0"
      then have r_inS: "r \<in> ?S"
        using r_in by simp
      have "d \<le> r"
        using Min_le[OF finS r_inS] by (simp add: d_def)
      with r_bounds show False
        by linarith
    qed
    then have "h = q * d"
      using div_eq by simp
    then show ?thesis
      unfolding dvd_def by (metis mult.commute)
  qed
  have d_dvd_n: "d dvd n"
  proof -
    define q where "q = n div d"
    define r where "r = n mod d"
    have q_nonneg: "0 \<le> q"
      using n_pos d_bounds by (simp add: q_def pos_imp_zdiv_nonneg_iff)
    have r_bounds: "0 \<le> r" "r < d"
      using d_bounds by (simp_all add: r_def)
    have n_eq: "n = q * d + r"
      by (simp add: q_def r_def)
    show ?thesis
    proof (cases "r = 0")
      case True
      then have "n = q * d"
        using n_eq by simp
      then show ?thesis
        unfolding dvd_def by (metis mult.commute)
    next
      case False
      then have r_pos: "0 < r"
        using r_bounds by linarith
      have qd_bounds: "0 < q * d" "q * d < n"
        using n_eq r_bounds r_pos d_bounds n_pos by linarith+
      have qd_mod_in: "(int (nat q) * d) mod n \<in> H"
        by (rule residue_add_closed_mult[OF n_pos zero add_closed d_in])
      have qd_in: "q * d \<in> H"
        using qd_mod_in q_nonneg qd_bounds n_pos by simp
      have r_mod_in: "(0 - q * d) mod n \<in> H"
        by (rule residue_add_closed_diff[OF n_pos zero add_closed zero qd_in])
      have neg_eq: "(0 - q * d) mod n = r"
      proof -
        have "q * d = n - r"
          using n_eq by simp
        then have "(0 - q * d) mod n = (r - n) mod n"
          by simp
        also have "\<dots> = r mod n"
          by (simp add: mod_simps)
        also have "\<dots> = r"
          using r_bounds d_bounds n_pos by simp
        finally show ?thesis .
      qed
      have r_in: "r \<in> H"
        using r_mod_in neg_eq by simp
      have r_inS: "r \<in> ?S"
        using r_in r_pos by auto
      have "d \<le> r"
        using Min_le[OF finS r_inS] by (simp add: d_def)
      with r_bounds show ?thesis
        by linarith
    qed
  qed
  have d_gt_one: "1 < d"
  proof (rule ccontr)
    assume "\<not> 1 < d"
    then have d_eq_one: "d = 1"
      using d_bounds by linarith
    have carrier_sub: "{0..n - 1} \<subseteq> H"
    proof
      fix x
      assume x_in: "x \<in> {0..n - 1}"
      then have x_bounds: "0 \<le> x" "x < n"
        by auto
      have "(int (nat x) * d) mod n \<in> H"
        by (rule residue_add_closed_mult[OF n_pos zero add_closed d_in])
      then show "x \<in> H"
        using x_bounds d_eq_one n_pos by simp
    qed
    have "H = {0..n - 1}"
      using H_sub carrier_sub by auto
    with proper show False
      by simp
  qed
  show ?thesis
    by (rule that[OF d_gt_one d_dvd_n dvd_H])
qed

lemma residue_add_closed_min_step_eq:
  fixes H :: "int set"
  assumes n_pos: "0 < n"
  assumes H_sub: "H \<subseteq> {0..n - 1}"
  assumes zero: "0 \<in> H"
  assumes add_closed: "\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> (x + y) mod n \<in> H"
  assumes nontrivial: "H \<noteq> {0}"
  defines "d \<equiv> Min (H - {0})"
  shows "0 < d"
    and "d dvd n"
    and "H = {x \<in> {0..n - 1}. d dvd x}"
proof -
  let ?S = "H - {0}"
  have finH: "finite H"
    using H_sub by (rule finite_subset) simp
  have finS: "finite ?S"
    using finH by simp
  have nonemptyS: "?S \<noteq> {}"
    using zero nontrivial by auto
  have d_inS: "d \<in> ?S"
    unfolding d_def by (rule Min_in[OF finS nonemptyS])
  then have d_in: "d \<in> H" and d_ne_zero: "d \<noteq> 0"
    by auto
  have d_bounds: "0 < d" "d < n"
  proof -
    have "d \<in> {0..n - 1}"
      using H_sub d_in by auto
    then have "0 \<le> d" "d < n"
      by auto
    with d_ne_zero show "0 < d" "d < n"
      by linarith+
  qed
  have dvd_H: "d dvd h" if h_in: "h \<in> H" for h
  proof (cases "h = 0")
    case True
    then show ?thesis
      by simp
  next
    case False
    have h_inS: "h \<in> ?S"
      using h_in False by simp
    have h_bounds: "0 \<le> h" "h < n"
      using H_sub h_in by auto
    define q where "q = h div d"
    define r where "r = h mod d"
    have q_nonneg: "0 \<le> q"
      using h_bounds d_bounds by (simp add: q_def pos_imp_zdiv_nonneg_iff)
    have r_bounds: "0 \<le> r" "r < d"
      using d_bounds by (simp_all add: r_def)
    have div_eq: "h = q * d + r"
      by (simp add: q_def r_def)
    have qd_bounds: "0 \<le> q * d" "q * d < n"
      using q_nonneg d_bounds h_bounds div_eq r_bounds by (simp, linarith)
    have qd_mod_in: "(int (nat q) * d) mod n \<in> H"
      by (rule residue_add_closed_mult[OF n_pos zero add_closed d_in])
    have qd_in: "q * d \<in> H"
      using qd_mod_in q_nonneg qd_bounds n_pos by simp
    have r_mod_in: "(h - q * d) mod n \<in> H"
      by (rule residue_add_closed_diff[OF n_pos zero add_closed h_in qd_in])
    have r_eq: "h - q * d = r"
      using div_eq by simp
    have r_in: "r \<in> H"
      using r_mod_in r_eq r_bounds d_bounds n_pos by simp
    have "r = 0"
    proof (rule ccontr)
      assume "r \<noteq> 0"
      then have r_inS: "r \<in> ?S"
        using r_in by simp
      have "d \<le> r"
        using Min_le[OF finS r_inS] by (simp add: d_def)
      with r_bounds show False
        by linarith
    qed
    then have "h = q * d"
      using div_eq by simp
    then show ?thesis
      unfolding dvd_def by (metis mult.commute)
  qed
  have d_dvd_n: "d dvd n"
  proof -
    define q where "q = n div d"
    define r where "r = n mod d"
    have q_nonneg: "0 \<le> q"
      using n_pos d_bounds by (simp add: q_def pos_imp_zdiv_nonneg_iff)
    have r_bounds: "0 \<le> r" "r < d"
      using d_bounds by (simp_all add: r_def)
    have n_eq: "n = q * d + r"
      by (simp add: q_def r_def)
    show ?thesis
    proof (cases "r = 0")
      case True
      then have "n = q * d"
        using n_eq by simp
      then show ?thesis
        unfolding dvd_def by (metis mult.commute)
    next
      case False
      then have r_pos: "0 < r"
        using r_bounds by linarith
      have qd_bounds: "0 < q * d" "q * d < n"
        using n_eq r_bounds r_pos d_bounds n_pos by linarith+
      have qd_mod_in: "(int (nat q) * d) mod n \<in> H"
        by (rule residue_add_closed_mult[OF n_pos zero add_closed d_in])
      have qd_in: "q * d \<in> H"
        using qd_mod_in q_nonneg qd_bounds n_pos by simp
      have r_mod_in: "(0 - q * d) mod n \<in> H"
        by (rule residue_add_closed_diff[OF n_pos zero add_closed zero qd_in])
      have neg_eq: "(0 - q * d) mod n = r"
      proof -
        have "q * d = n - r"
          using n_eq by simp
        then have "(0 - q * d) mod n = (r - n) mod n"
          by simp
        also have "\<dots> = r mod n"
          by (simp add: mod_simps)
        also have "\<dots> = r"
          using r_bounds d_bounds n_pos by simp
        finally show ?thesis .
      qed
      have r_in: "r \<in> H"
        using r_mod_in neg_eq by simp
      have r_inS: "r \<in> ?S"
        using r_in r_pos by auto
      have "d \<le> r"
        using Min_le[OF finS r_inS] by (simp add: d_def)
      with r_bounds show ?thesis
        by linarith
    qed
  qed
  have multiples_sub: "{x \<in> {0..n - 1}. d dvd x} \<subseteq> H"
  proof
    fix x
    assume x_in: "x \<in> {x \<in> {0..n - 1}. d dvd x}"
    then have x_bounds: "0 \<le> x" "x < n" and d_x: "d dvd x"
      by auto
    obtain q where x_eq: "x = d * q"
      using d_x unfolding dvd_def by blast
    have q_nonneg: "0 \<le> q"
    proof (rule ccontr)
      assume "\<not> 0 \<le> q"
      then have q_neg: "q < 0"
        by simp
      have "d * q < 0"
        using d_bounds q_neg by (simp add: mult_less_0_iff)
      then have "x < 0"
        using x_eq by simp
      with x_bounds show False
        by linarith
    qed
    have "(int (nat q) * d) mod n \<in> H"
      by (rule residue_add_closed_mult[OF n_pos zero add_closed d_in])
    moreover have "int (nat q) * d = x"
      using q_nonneg x_eq by (simp add: mult.commute)
    ultimately show "x \<in> H"
      using x_bounds n_pos by simp
  qed
  show "0 < d"
    by (rule d_bounds(1))
  show "d dvd n"
    by (rule d_dvd_n)
  show "H = {x \<in> {0..n - 1}. d dvd x}"
  proof
    show "H \<subseteq> {x \<in> {0..n - 1}. d dvd x}"
      using H_sub dvd_H by auto
    show "{x \<in> {0..n - 1}. d dvd x} \<subseteq> H"
      by (rule multiples_sub)
  qed
qed

lemma zmod_stabilizer_add_closed:
  assumes x_in: "x \<in> Zmod.stabilizer p C"
  assumes y_in: "y \<in> Zmod.stabilizer p C"
  shows "(x + y) mod int p \<in> Zmod.stabilizer p C"
proof -
  interpret H: subgroup "Zmod.stabilizer p C" "{0..int (p - 1)}"
      "(\<lambda>x y. (x + y) mod int p)" "0::int"
    by (rule Zmod.stabilizer_is_subgroup)
  show ?thesis
    by (rule H.sub_composition_closed[OF x_in y_in])
qed

lemma zmod_stabilizer_obtain_proper_divisor:
  fixes C :: "int set"
  assumes p_pos: "0 < p"
  assumes nontrivial: "Zmod.stabilizer p C \<noteq> {0}"
  assumes proper: "Zmod.stabilizer p C \<noteq> {0..int p - 1}"
  obtains d where "1 < d" "d dvd int p"
    "\<And>h. h \<in> Zmod.stabilizer p C \<Longrightarrow> d dvd h"
proof -
  let ?H = "Zmod.stabilizer p C"
  have H_sub: "?H \<subseteq> {0..int p - 1}"
    using Zmod.stabilizer_subset_group[of p C] p_pos by auto
  have zero: "0 \<in> ?H"
    by (rule Zmod.zero_mem_stabilizer)
  have add_closed: "\<And>x y. x \<in> ?H \<Longrightarrow> y \<in> ?H \<Longrightarrow> (x + y) mod int p \<in> ?H"
    by (rule zmod_stabilizer_add_closed)
  show ?thesis
    by (rule residue_add_closed_obtain_proper_divisor
        [OF _ H_sub zero add_closed nontrivial proper that])
      (use p_pos in simp)
qed

lemma zmod_full_stabilizer_zero_imp_carrier_subset:
  fixes C :: "int set"
  assumes p_pos: "0 < p"
  assumes C_sub: "C \<subseteq> {0..int p - 1}"
  assumes zero_C: "0 \<in> C"
  assumes full: "Zmod.stabilizer p C = {0..int p - 1}"
  shows "{0..int p - 1} \<subseteq> C"
proof
  fix x
  assume x_carrier: "x \<in> {0..int p - 1}"
  then have x_stab: "x \<in> Zmod.stabilizer p C"
    using full by simp
  have carrier_eq: "{0..int (p - 1)} = {0..int p - 1}"
    using p_pos by auto
  have zero_carrier: "0 \<in> {0..int (p - 1)}"
    using p_pos by auto
  have x_carrier': "x \<in> {0..int (p - 1)}"
    using x_carrier carrier_eq by simp
  have C_sub': "C \<subseteq> {0..int (p - 1)}"
    using C_sub carrier_eq by simp
  have coset_sub: "Zmod.sumset p {0} (Zmod.stabilizer p C) \<subseteq> C"
    by (rule Zmod.stabilizer_coset_subset[OF C_sub' zero_C])
  have x_sum: "x \<in> Zmod.sumset p {0} (Zmod.stabilizer p C)"
  proof -
    have "(0 + x) mod int p \<in> Zmod.sumset p {0} (Zmod.stabilizer p C)"
      by (rule Zmod.sumset.sumsetI) (use x_stab x_carrier' zero_carrier in auto)
    then show ?thesis
      using x_carrier p_pos by simp
  qed
  show "x \<in> C"
    using coset_sub x_sum by auto
qed

lemma mod_image_int_normalized_interval:
  fixes A :: "int set"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  shows "mod_image_int n A = A - {n}"
proof
  show "mod_image_int n A \<subseteq> A - {n}"
  proof
    fix r
    assume "r \<in> mod_image_int n A"
    then obtain a where a_in: "a \<in> A" and r_eq: "r = a mod n"
      by (auto simp: mod_image_int_def)
    have a_bounds: "0 \<le> a" "a \<le> n"
      using subset a_in by auto
    show "r \<in> A - {n}"
    proof (cases "a = n")
      case True
      then show ?thesis
        using zero r_eq n_pos by simp
    next
      case False
      then have "a < n"
        using a_bounds by simp
      then have "a mod n = a"
        using a_bounds n_pos by simp
      then show ?thesis
        using a_in r_eq False by simp
    qed
  qed
next
  show "A - {n} \<subseteq> mod_image_int n A"
  proof
    fix a
    assume a_in: "a \<in> A - {n}"
    then have "a \<in> A" and a_ne: "a \<noteq> n"
      by auto
    have a_bounds: "0 \<le> a" "a \<le> n"
      using subset \<open>a \<in> A\<close> by auto
    then have "a < n"
      using a_ne by simp
    then have a_mod: "a mod n = a"
      using a_bounds n_pos by simp
    show "a \<in> mod_image_int n A"
      unfolding mod_image_int_def
    proof (rule image_eqI)
      show "a = a mod n"
        using a_mod by simp
      show "a \<in> A"
        by fact
    qed
  qed
qed

lemma card_mod_image_int_normalized_interval:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  shows "card (mod_image_int n A) = card A - 1"
proof -
  have "card (mod_image_int n A) = card (A - {n})"
    by (simp add: mod_image_int_normalized_interval[OF n_pos subset zero top])
  also have "\<dots> = card A - 1"
    using fin top by simp
  finally show ?thesis .
qed

lemma normalized_mod_sumset_trivial_stabilizer_card_ge:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  defines "B \<equiv> mod_image_int n A"
  defines "p \<equiv> nat n"
  defines "C \<equiv> Zmod.sumset p B B"
  assumes trivial: "Zmod.stabilizer p C = {0}"
  shows "2 * card A - 3 \<le> card (mod_sumset_int n A A)"
proof -
  have p_pos: "0 < p"
    using n_pos by (simp add: p_def)
  have int_p: "int p = n"
    using n_pos by (simp add: p_def)
  have B_sub: "B \<subseteq> {0..int p - 1}"
    using mod_image_int_subset_residues[OF n_pos, of A] by (simp add: B_def int_p)
  have finB: "finite B"
    unfolding B_def by (rule finite_mod_image_int[OF fin])
  have zero_B: "0 \<in> B"
    unfolding B_def mod_image_int_def
  proof (rule image_eqI)
    show "0 = 0 mod n"
      by simp
    show "0 \<in> A"
      by (rule zero)
  qed
  have nonemptyB: "B \<noteq> {}"
    using zero_B by auto
  have cardB: "card B = card A - 1"
    unfolding B_def by (rule card_mod_image_int_normalized_interval[OF fin n_pos subset zero top])
  have trivial': "Zmod.stabilizer p (Zmod.sumset p B B) = {0}"
    using trivial by (simp add: C_def)
  have C_lower_unfolded: "2 * card B - 1 \<le> card (Zmod.sumset p B B)"
    by (rule zmod_sumset_trivial_stabilizer_card_ge
        [OF p_pos B_sub finB nonemptyB trivial'])
  have C_lower: "2 * card B - 1 \<le> card C"
    using C_lower_unfolded by (simp add: C_def)
  have C_eq_mod: "C = mod_sumset_int n A A"
  proof -
    have "C = mod_sumset_int (int p) B B"
      unfolding C_def by (rule zmod_sumset_eq_mod_sumset_int[OF p_pos B_sub B_sub])
    also have "\<dots> = mod_sumset_int n B B"
      by (simp add: int_p)
    also have "\<dots> = mod_sumset_int n A A"
      unfolding B_def by (rule mod_sumset_int_mod_image_self[OF n_pos])
    finally show ?thesis .
  qed
  have "2 * card A - 3 \<le> 2 * card B - 1"
    using cardB zero fin by (simp add: card_gt_0_iff)
  also have "\<dots> \<le> card C"
    by (rule C_lower)
  finally show ?thesis
    by (simp add: C_eq_mod)
qed

lemma mod_image_int_subset_mod_sumset_self:
  assumes zero: "0 \<in> A"
  shows "mod_image_int n A \<subseteq> mod_sumset_int n A A"
proof
  fix r
  assume "r \<in> mod_image_int n A"
  then obtain a where a_in: "a \<in> A" and r_eq: "r = a mod n"
    by (auto simp: mod_image_int_def)
  have "0 + a \<in> sumset A A"
    using zero a_in by (rule sumsetI)
  then show "r \<in> mod_sumset_int n A A"
    using r_eq by (auto simp: mod_sumset_int_def mod_image_int_def)
qed

lemma card_eq_sum_mod_fibers:
  fixes S :: "int set"
  assumes fin: "finite S"
  shows "card S = (\<Sum>r\<in>mod_image_int n S. card (mod_fiber_int n S r))"
proof -
  let ?C = "mod_image_int n S"
  have finC: "finite ?C"
    by (rule finite_mod_image_int[OF fin])
  have union_eq: "S = (\<Union> (mod_fiber_int n S ` ?C))"
    by (auto simp: mod_image_int_def mod_fiber_int_def)
  have fin_fibers: "\<forall>r\<in>?C. finite (mod_fiber_int n S r)"
    using fin by auto
  have disj_fibers:
    "\<forall>r\<in>?C. \<forall>t\<in>?C. r \<noteq> t \<longrightarrow>
      mod_fiber_int n S r \<inter> mod_fiber_int n S t = {}"
    by (auto simp: mod_fiber_int_def)
  have "card S = card (\<Union> (mod_fiber_int n S ` ?C))"
    using union_eq by simp
  also have "\<dots> = (\<Sum>r\<in>?C. card (mod_fiber_int n S r))"
    by (rule card_UN_disjoint[OF finC fin_fibers disj_fibers])
  finally show ?thesis .
qed

lemma card_mod_fiber_pos:
  fixes S :: "int set"
  assumes fin: "finite S"
  assumes r_in: "r \<in> mod_image_int n S"
  shows "0 < card (mod_fiber_int n S r)"
proof -
  from r_in obtain s where s_in: "s \<in> S" and r_eq: "r = s mod n"
    by (auto simp: mod_image_int_def)
  have "{s} \<subseteq> mod_fiber_int n S r"
    using s_in r_eq by (auto simp: mod_fiber_int_def)
  then have "card {s} \<le> card (mod_fiber_int n S r)"
    by (rule card_mono[OF finite_mod_fiber_int[OF fin]])
  then show ?thesis
    by simp
qed

lemma normalized_endpoint_zero_fiber_card_ge3:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  shows "3 \<le> card (mod_fiber_int n (sumset A A) 0)"
proof -
  let ?S = "sumset A A"
  have elems: "{0, n, 2 * n} \<subseteq> mod_fiber_int n ?S 0"
  proof
    fix y
    assume "y \<in> {0, n, 2 * n}"
    then consider "y = 0" | "y = n" | "y = 2 * n"
      by auto
    then show "y \<in> mod_fiber_int n ?S 0"
    proof cases
      case 1
      have "0 + 0 \<in> ?S"
        using zero zero by (rule sumsetI)
      then show ?thesis
        using 1 by (simp add: mod_fiber_int_def)
    next
      case 2
      have "0 + n \<in> ?S"
        using zero top by (rule sumsetI)
      then show ?thesis
        using 2 n_pos by (simp add: mod_fiber_int_def)
    next
      case 3
      have "n + n \<in> ?S"
        using top top by (rule sumsetI)
      then show ?thesis
        using 3 n_pos by (simp add: mod_fiber_int_def)
    qed
  qed
  have "card {0, n, 2 * n} \<le> card (mod_fiber_int n ?S 0)"
    by (rule card_mono[OF finite_mod_fiber_int[OF finite_sumset[OF fin fin]] elems])
  moreover have "card {0, n, 2 * n} = 3"
    using n_pos by auto
  ultimately show ?thesis
    by simp
qed

lemma normalized_endpoint_nonzero_fiber_card_ge2:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes r_in: "r \<in> mod_image_int n A"
  assumes r_ne: "r \<noteq> 0"
  shows "2 \<le> card (mod_fiber_int n (sumset A A) r)"
proof -
  let ?S = "sumset A A"
  from r_in obtain a where a_in: "a \<in> A" and r_eq: "r = a mod n"
    by (auto simp: mod_image_int_def)
  have a_bounds: "0 \<le> a" "a \<le> n"
    using subset a_in by auto
  have a_ne_n: "a \<noteq> n"
    using r_eq r_ne n_pos by auto
  then have a_lt: "a < n"
    using a_bounds by simp
  have a_ne_0: "a \<noteq> 0"
    using r_eq r_ne by auto
  have a_mod: "a mod n = a"
    using a_bounds a_lt n_pos by simp
  have elems: "{a, n + a} \<subseteq> mod_fiber_int n ?S r"
  proof
    fix y
    assume "y \<in> {a, n + a}"
    then show "y \<in> mod_fiber_int n ?S r"
    proof
      assume y_eq: "y = a"
      have "0 + a \<in> ?S"
        using zero a_in by (rule sumsetI)
      then show ?thesis
        using y_eq r_eq a_mod by (simp add: mod_fiber_int_def)
    next
      assume "y \<in> {n + a}"
      then have y_eq: "y = n + a"
        by simp
      have "n + a \<in> ?S"
        using top a_in by (rule sumsetI)
      moreover have "(n + a) mod n = r"
        using r_eq a_mod n_pos by simp
      ultimately show ?thesis
        using y_eq by (simp add: mod_fiber_int_def)
    qed
  qed
  have "card {a, n + a} \<le> card (mod_fiber_int n ?S r)"
    by (rule card_mono[OF finite_mod_fiber_int[OF finite_sumset[OF fin fin]] elems])
  moreover have "card {a, n + a} = 2"
    using n_pos by auto
  ultimately show ?thesis
    by simp
qed

lemma card_sumset_ge_mod_sumset_plus_card:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  shows "card (sumset A A) \<ge> card (mod_sumset_int n A A) + card A"
proof -
  let ?S = "sumset A A"
  let ?C = "mod_sumset_int n A A"
  let ?B = "mod_image_int n A"
  have finS: "finite ?S"
    by (rule finite_sumset[OF fin fin])
  have finC: "finite ?C"
    by (rule finite_mod_sumset_int[OF fin fin])
  have finB: "finite ?B"
    by (rule finite_mod_image_int[OF fin])
  have C_eq: "?C = mod_image_int n ?S"
    by (simp add: mod_sumset_int_def)
  have B_sub_C: "?B \<subseteq> ?C"
    by (rule mod_image_int_subset_mod_sumset_self[OF zero])
  have zero_in_B: "0 \<in> ?B"
    unfolding mod_image_int_def
  proof (rule image_eqI)
    show "0 = 0 mod n"
      by simp
    show "0 \<in> A"
      by (rule zero)
  qed
  have cardB: "card ?B = card A - 1"
    by (rule card_mod_image_int_normalized_interval[OF fin n_pos subset zero top])
  have cardA_pos: "0 < card A"
    using fin zero by (simp add: card_gt_0_iff, blast)
  have fiber_lower:
    "1 + (if r \<in> ?B then 1 else 0) + (if r = 0 then 1 else 0)
      \<le> card (mod_fiber_int n ?S r)" if r_in: "r \<in> ?C" for r
  proof (cases "r = 0")
    case True
    have "3 \<le> card (mod_fiber_int n ?S r)"
      using True by (simp add: normalized_endpoint_zero_fiber_card_ge3[OF fin n_pos zero top])
    then show ?thesis
      using True zero_in_B by simp
  next
    case r_ne_zero: False
    show ?thesis
    proof (cases "r \<in> ?B")
      case True
      have "2 \<le> card (mod_fiber_int n ?S r)"
        by (rule normalized_endpoint_nonzero_fiber_card_ge2
            [OF fin n_pos subset zero top True r_ne_zero])
      then show ?thesis
        using True r_ne_zero by simp
    next
      case False
      have "0 < card (mod_fiber_int n ?S r)"
        using r_in unfolding C_eq by (rule card_mod_fiber_pos[OF finS])
      then show ?thesis
        using False r_ne_zero by simp
    qed
  qed
  have extra_B_sum:
    "(\<Sum>r\<in>?C. (if r \<in> ?B then 1 else 0::nat)) = card ?B"
  proof -
    have "(\<Sum>r\<in>?C. (if r \<in> ?B then 1 else 0::nat)) =
        (\<Sum>r\<in>?B. 1)"
      using B_sub_C finB finC
      by (intro sum.mono_neutral_cong_right) auto
    then show ?thesis
      by simp
  qed
  have extra_zero_sum:
    "(\<Sum>r\<in>?C. (if r = 0 then 1 else 0::nat)) = 1"
  proof -
    have "0 \<in> ?C"
      using zero_in_B B_sub_C by auto
    then show ?thesis
      using finC by (simp add: sum.If_cases)
  qed
  have extra_total:
    "(\<Sum>r\<in>?C. 1 + (if r \<in> ?B then 1 else 0) + (if r = 0 then 1 else 0)) =
      card ?C + card ?B + 1"
  proof -
    have sum_suc:
      "(\<Sum>r\<in>X. 1 + (if r \<in> ?B then 1 else 0) + (if r = 0 then 1 else 0)) =
        card X + (\<Sum>r\<in>X. (if r \<in> ?B then 1 else 0) + (if r = 0 then 1 else 0))"
      if "finite X" for X
      using that
    proof (induction X rule: finite_induct)
      case empty
      then show ?case
        by simp
    next
      case (insert r R)
      then show ?case
        by simp
    qed
    have split_extra:
      "(\<Sum>r\<in>?C. (if r \<in> ?B then 1 else 0) + (if r = 0 then 1 else 0)) =
        (\<Sum>r\<in>?C. (if r \<in> ?B then 1 else 0)) +
        (\<Sum>r\<in>?C. (if r = 0 then 1 else 0::nat))"
      by (rule sum.distrib)
    show ?thesis
      using sum_suc[OF finC] split_extra extra_B_sum extra_zero_sum by simp
  qed
  have cardS_sum: "card ?S = (\<Sum>r\<in>?C. card (mod_fiber_int n ?S r))"
    unfolding C_eq by (rule card_eq_sum_mod_fibers[OF finS])
  have sum_lower: "(\<Sum>r\<in>?C. card (mod_fiber_int n ?S r)) \<ge>
      (\<Sum>r\<in>?C. 1 + (if r \<in> ?B then 1 else 0) + (if r = 0 then 1 else 0))"
    by (rule sum_mono) (rule fiber_lower)
  have target_eq: "card ?C + card ?B + 1 = card ?C + card A"
    using cardB cardA_pos by linarith
  show ?thesis
    using cardS_sum sum_lower extra_total target_eq by linarith
qed

lemma normalized_small_doubling_mod_stabilizer_nontrivial:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  defines "B \<equiv> mod_image_int n A"
  defines "p \<equiv> nat n"
  defines "C \<equiv> Zmod.sumset p B B"
  shows "Zmod.stabilizer p C \<noteq> {0}"
proof
  assume trivial: "Zmod.stabilizer p C = {0}"
  have trivial_unfolded:
    "Zmod.stabilizer (nat n)
      (Zmod.sumset (nat n) (mod_image_int n A) (mod_image_int n A)) = {0}"
    using trivial by (simp add: B_def p_def C_def)
  have mod_lower: "2 * card A - 3 \<le> card (mod_sumset_int n A A)"
    by (rule normalized_mod_sumset_trivial_stabilizer_card_ge
        [OF fin n_pos subset zero top trivial_unfolded])
  have sum_lower:
    "card (mod_sumset_int n A A) + card A \<le> card (sumset A A)"
    by (rule card_sumset_ge_mod_sumset_plus_card[OF fin n_pos subset zero top])
  have "3 * card A - 3 \<le> card (sumset A A)"
    using mod_lower sum_lower card_ge by linarith
  with small_doubling card_ge show False
    by linarith
qed

lemma normalized_small_doubling_obtain_positive_mod_period:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  defines "B \<equiv> mod_image_int n A"
  defines "p \<equiv> nat n"
  defines "C \<equiv> Zmod.sumset p B B"
  obtains h where "h \<in> Zmod.stabilizer p C" "0 < h" "h < n"
proof -
  have p_pos: "0 < p"
    using n_pos by (simp add: p_def)
  have int_p: "int p = n"
    using n_pos by (simp add: p_def)
  have nontrivial_unfolded:
    "Zmod.stabilizer (nat n)
      (Zmod.sumset (nat n) (mod_image_int n A) (mod_image_int n A)) \<noteq> {0}"
    by (rule normalized_small_doubling_mod_stabilizer_nontrivial
        [OF fin card_ge n_pos subset zero top small_doubling])
  have nontrivial: "Zmod.stabilizer p C \<noteq> {0}"
    using nontrivial_unfolded by (simp add: B_def p_def C_def)
  obtain h where h_in: "h \<in> Zmod.stabilizer p C" and h_pos: "0 < h" and h_lt_p: "h < int p"
    by (rule zmod_nontrivial_stabilizer_obtain_positive_period[OF p_pos nontrivial])
  have h_lt_n: "h < n"
    using h_lt_p by (simp add: int_p)
  show ?thesis
    by (rule that[OF h_in h_pos h_lt_n])
qed

lemma two_sided_unstable_hole_notin_mod_sumset:
  fixes A :: "int set"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes x_bounds: "0 < x" "x < n"
  assumes lower_missing: "x \<notin> sumset A A"
  assumes upper_missing: "n + x \<notin> sumset A A"
  shows "x \<notin> mod_sumset_int n A A"
proof
  assume "x \<in> mod_sumset_int n A A"
  then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> A" and mod_eq: "x = (a + b) mod n"
    by (auto simp: mod_sumset_int_iff)
  have a_bounds: "0 \<le> a" "a \<le> n"
    using subset a_in by auto
  have b_bounds: "0 \<le> b" "b \<le> n"
    using subset b_in by auto
  have sum_bounds: "0 \<le> a + b" "a + b \<le> 2 * n"
    using a_bounds b_bounds by linarith+
  from mod_eq have "(a + b) mod n = x"
    by simp
  moreover have "x mod n = x"
    using n_pos x_bounds by simp
  ultimately have "(a + b) mod n = x mod n"
    by simp
  then obtain d where d_eq: "x = (a + b) + n * d"
    by (rule mod_eqE)
  define q where "q = - d"
  have q_eq: "a + b = q * n + x"
    using d_eq by (simp add: q_def algebra_simps)
  have "q = 0 \<or> q = 1"
  proof -
    have lower: "0 \<le> q * n + x"
      using q_eq sum_bounds by simp
    have upper: "q * n + x \<le> 2 * n"
      using q_eq sum_bounds by simp
    have q_nonneg: "0 \<le> q"
    proof (rule ccontr)
      assume "\<not> 0 \<le> q"
      then have q_le: "q \<le> -1"
        by linarith
      have "q * n \<le> (-1) * n"
        using q_le n_pos by (intro mult_right_mono) simp_all
      then have "q * n + x < 0"
        using x_bounds by linarith
      with lower show False
        by linarith
    qed
    have q_lt_two: "q < 2"
    proof (rule ccontr)
      assume "\<not> q < 2"
      then have q_ge: "2 \<le> q"
        by linarith
      have "2 * n \<le> q * n"
        using q_ge n_pos by (intro mult_right_mono) simp_all
      then have "2 * n < q * n + x"
        using x_bounds by linarith
      with upper show False
        by linarith
    qed
    show ?thesis
      using q_nonneg q_lt_two
      by linarith
  qed
  then show False
  proof
    assume "q = 0"
    then have "a + b = x"
      using q_eq by simp
    moreover have "a + b \<in> sumset A A"
      using a_in b_in by (rule sumsetI)
    ultimately have "x \<in> sumset A A"
      by simp
    with lower_missing show False
      by simp
  next
    assume "q = 1"
    then have "a + b = n + x"
      using q_eq by simp
    moreover have "a + b \<in> sumset A A"
      using a_in b_in by (rule sumsetI)
    ultimately have "n + x \<in> sumset A A"
      by simp
    with upper_missing show False
      by simp
  qed
qed

lemma mod_sumset_gap_imp_stable_sum_hole:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes x_bounds: "0 < x" "x < n"
  assumes gap: "x \<notin> mod_sumset_int n A A"
  shows "x \<in> stable_sum_holes A"
proof -
  have nonempty: "A \<noteq> {}"
    using top by auto
  have max_eq: "Max A = n"
    using Max_eq_iff[OF fin nonempty, of n] subset top by auto
  have x_mod: "x mod n = x"
    using n_pos x_bounds by simp
  have x_notin_A: "x \<notin> A"
  proof
    assume x_in: "x \<in> A"
    have sum_x: "0 + x \<in> sumset A A"
      using zero x_in by (rule sumsetI)
    have "x \<in> mod_sumset_int n A A"
      unfolding mod_sumset_int_def mod_image_int_def
    proof (rule image_eqI)
      show "x = x mod n"
        using x_mod by simp
      show "x \<in> sumset A A"
        using sum_x by simp
    qed
    with gap show False
      by simp
  qed
  have x_not_lower: "x \<notin> lower_sum_holes A"
  proof
    assume x_lower: "x \<in> lower_sum_holes A"
    then have sum_x: "x \<in> sumset A A"
      by (simp add: lower_sum_holes_def)
    have "x \<in> mod_sumset_int n A A"
      unfolding mod_sumset_int_def mod_image_int_def
    proof (rule image_eqI)
      show "x = x mod n"
        using x_mod by simp
      show "x \<in> sumset A A"
        by (rule sum_x)
    qed
    with gap show False
      by simp
  qed
  have x_not_upper: "x \<notin> upper_sum_holes A"
  proof
    assume x_upper: "x \<in> upper_sum_holes A"
    then have sum_nx: "n + x \<in> sumset A A"
      by (simp add: upper_sum_holes_def max_eq)
    have nx_mod: "(n + x) mod n = x"
      using n_pos x_mod by simp
    have "x \<in> mod_sumset_int n A A"
      unfolding mod_sumset_int_def mod_image_int_def
    proof (rule image_eqI)
      show "x = (n + x) mod n"
        using nx_mod by simp
      show "n + x \<in> sumset A A"
        by (rule sum_nx)
    qed
    with gap show False
      by simp
  qed
  have "x \<in> interval_holes A"
    using x_bounds x_notin_A by (auto simp: interval_holes_def max_eq)
  with x_not_lower x_not_upper show ?thesis
    by (auto simp: stable_sum_holes_def)
qed

lemma stable_sum_holes_eq_mod_sumset_gaps:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  shows "stable_sum_holes A =
    {x. 0 < x \<and> x < n \<and> x \<notin> mod_sumset_int n A A}"
proof
  have nonempty: "A \<noteq> {}"
    using top by auto
  have max_eq: "Max A = n"
    using Max_eq_iff[OF fin nonempty, of n] subset top by auto
  show "stable_sum_holes A \<subseteq>
      {x. 0 < x \<and> x < n \<and> x \<notin> mod_sumset_int n A A}"
  proof
    fix x
    assume x_stable: "x \<in> stable_sum_holes A"
    then have x_hole: "x \<in> interval_holes A"
      by (auto simp: stable_sum_holes_def)
    then have x_nonneg: "0 \<le> x" and x_le: "x \<le> n" and x_notin: "x \<notin> A"
      by (auto simp: interval_holes_def max_eq)
    have x_ne_zero: "x \<noteq> 0"
      using x_notin zero by auto
    have x_pos: "0 < x"
      using x_nonneg x_ne_zero by linarith
    have x_ne_n: "x \<noteq> n"
      using x_notin top by auto
    have x_lt: "x < n"
      using x_le x_ne_n by linarith
    have x_not_lower: "x \<notin> lower_sum_holes A"
      using x_stable by (auto simp: stable_sum_holes_def)
    have x_not_upper: "x \<notin> upper_sum_holes A"
      using x_stable by (auto simp: stable_sum_holes_def)
    have lower_missing: "x \<notin> sumset A A"
    proof
      assume "x \<in> sumset A A"
      with x_hole have "x \<in> lower_sum_holes A"
        by (simp add: lower_sum_holes_def)
      with x_not_lower show False
        by simp
    qed
    have upper_missing: "n + x \<notin> sumset A A"
    proof
      assume "n + x \<in> sumset A A"
      with x_hole have "x \<in> upper_sum_holes A"
        by (simp add: upper_sum_holes_def max_eq)
      with x_not_upper show False
        by simp
    qed
    have "x \<notin> mod_sumset_int n A A"
      by (rule two_sided_unstable_hole_notin_mod_sumset
          [OF n_pos subset x_pos x_lt lower_missing upper_missing])
    with x_pos x_lt show "x \<in> {x. 0 < x \<and> x < n \<and> x \<notin> mod_sumset_int n A A}"
      by simp
  qed
  show "{x. 0 < x \<and> x < n \<and> x \<notin> mod_sumset_int n A A}
      \<subseteq> stable_sum_holes A"
  proof
    fix x
    assume "x \<in> {x. 0 < x \<and> x < n \<and> x \<notin> mod_sumset_int n A A}"
    then have x_bounds: "0 < x" "x < n" and gap: "x \<notin> mod_sumset_int n A A"
      by auto
    show "x \<in> stable_sum_holes A"
    by (rule mod_sumset_gap_imp_stable_sum_hole
        [OF fin n_pos subset zero top x_bounds gap])
  qed
qed

lemma mod_sumset_int_eq_mod_image_union_sum_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes max_eq: "Max A = n"
  shows "mod_sumset_int n A A =
    mod_image_int n A \<union> lower_sum_holes A \<union> upper_sum_holes A"
proof
  let ?C = "mod_sumset_int n A A"
  let ?B = "mod_image_int n A"
  have stable_eq:
    "stable_sum_holes A =
      {x. 0 < x \<and> x < n \<and> x \<notin> ?C}"
    by (rule stable_sum_holes_eq_mod_sumset_gaps[OF fin n_pos subset zero top])
  show "?C \<subseteq> ?B \<union> lower_sum_holes A \<union> upper_sum_holes A"
  proof
    fix r
    assume r_in: "r \<in> ?C"
    have r_res: "r \<in> {0..n - 1}"
      using r_in mod_image_int_subset_residues[OF n_pos, of "sumset A A"]
      by (auto simp: mod_sumset_int_def)
    show "r \<in> ?B \<union> lower_sum_holes A \<union> upper_sum_holes A"
    proof (cases "r \<in> ?B")
      case True
      then show ?thesis
        by simp
    next
      case False
      have r_not_A: "r \<notin> A"
      proof
        assume r_A: "r \<in> A"
        have r_mod: "r mod n = r"
          using r_res n_pos by simp
        have "r \<in> ?B"
          unfolding mod_image_int_def
        proof (rule image_eqI)
          show "r = r mod n"
            using r_mod by simp
          show "r \<in> A"
            by (rule r_A)
        qed
        with False show False
          by simp
      qed
      have r_hole: "r \<in> interval_holes A"
        using r_res r_not_A by (auto simp: interval_holes_def max_eq)
      have "r \<in> lower_sum_holes A \<union> upper_sum_holes A"
      proof (rule ccontr)
        assume "r \<notin> lower_sum_holes A \<union> upper_sum_holes A"
        then have "r \<in> stable_sum_holes A"
          using r_hole by (auto simp: stable_sum_holes_def)
        then have "r \<notin> ?C"
          using stable_eq by auto
        with r_in show False
          by simp
      qed
      then show ?thesis
        by simp
    qed
  qed
  show "?B \<union> lower_sum_holes A \<union> upper_sum_holes A \<subseteq> ?C"
  proof
    fix r
    assume r_in: "r \<in> ?B \<union> lower_sum_holes A \<union> upper_sum_holes A"
    then show "r \<in> ?C"
    proof
      assume "r \<in> ?B \<union> lower_sum_holes A"
      then show ?thesis
      proof
        assume "r \<in> ?B"
        then show ?thesis
          using mod_image_int_subset_mod_sumset_self[OF zero] by auto
      next
        assume r_lower: "r \<in> lower_sum_holes A"
        then have r_sum: "r \<in> sumset A A"
          by (simp add: lower_sum_holes_def)
        have r_bounds: "0 \<le> r" "r < n"
        proof -
          have r_hole: "r \<in> interval_holes A"
            using r_lower by (simp add: lower_sum_holes_def)
          then have "0 \<le> r" "r \<le> n" "r \<notin> A"
            by (auto simp: interval_holes_def max_eq)
          moreover have "r \<noteq> n"
            using \<open>r \<notin> A\<close> top by auto
          ultimately show "0 \<le> r" "r < n"
            by linarith+
        qed
        have r_mod: "r mod n = r"
          using r_bounds n_pos by simp
        show ?thesis
          unfolding mod_sumset_int_def mod_image_int_def
        proof (rule image_eqI)
          show "r = r mod n"
            using r_mod by simp
          show "r \<in> sumset A A"
            by (rule r_sum)
        qed
      qed
    next
      assume r_upper: "r \<in> upper_sum_holes A"
      then have nr_sum: "n + r \<in> sumset A A"
        by (simp add: upper_sum_holes_def max_eq)
      have r_bounds: "0 \<le> r" "r < n"
      proof -
        have r_hole: "r \<in> interval_holes A"
          using r_upper by (simp add: upper_sum_holes_def)
        then have "0 \<le> r" "r \<le> n" "r \<notin> A"
          by (auto simp: interval_holes_def max_eq)
        moreover have "r \<noteq> n"
          using \<open>r \<notin> A\<close> top by auto
        ultimately show "0 \<le> r" "r < n"
          by linarith+
      qed
      have nr_mod: "(n + r) mod n = r"
        using r_bounds n_pos by simp
      show ?thesis
        unfolding mod_sumset_int_def mod_image_int_def
      proof (rule image_eqI)
        show "r = (n + r) mod n"
          using nr_mod by simp
        show "n + r \<in> sumset A A"
          by (rule nr_sum)
      qed
    qed
  qed
qed

lemma card_mod_sumset_int_eq_card_mod_image_plus_unstable_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes max_eq: "Max A = n"
  shows "card (mod_sumset_int n A A) =
    card (mod_image_int n A) + card (lower_sum_holes A \<union> upper_sum_holes A)"
proof -
  let ?B = "mod_image_int n A"
  let ?U = "lower_sum_holes A \<union> upper_sum_holes A"
  have C_eq: "mod_sumset_int n A A = ?B \<union> ?U"
    using mod_sumset_int_eq_mod_image_union_sum_holes
      [OF fin n_pos subset zero top max_eq]
    by auto
  have finB: "finite ?B"
    by (rule finite_mod_image_int[OF fin])
  have finU: "finite ?U"
    by simp
  have disj: "?B \<inter> ?U = {}"
  proof
    show "?B \<inter> ?U \<subseteq> {}"
    proof
      fix r
      assume r_in: "r \<in> ?B \<inter> ?U"
      then have r_hole: "r \<in> interval_holes A"
        by (auto simp: lower_sum_holes_def upper_sum_holes_def)
      then have r_not_A: "r \<notin> A"
        by (simp add: interval_holes_def)
      from r_in obtain a where a_in: "a \<in> A" and r_eq: "r = a mod n"
        by (auto simp: mod_image_int_def)
      have a_bounds: "0 \<le> a" "a \<le> n"
        using subset a_in by auto
      show "r \<in> {}"
      proof (cases "a = n")
        case True
        then have "r = 0"
          using r_eq n_pos by simp
        with zero r_not_A show ?thesis
          by simp
      next
        case False
        then have "a < n"
          using a_bounds by simp
        then have "a mod n = a"
          using a_bounds n_pos by simp
        with r_eq a_in r_not_A show ?thesis
          by simp
      qed
    qed
  qed simp
  have "card (mod_sumset_int n A A) = card (?B \<union> ?U)"
    by (simp add: C_eq)
  also have "\<dots> = card ?B + card ?U"
    by (rule card_Un_disjoint[OF finB finU disj])
  finally show ?thesis .
qed

lemma card_mod_sumset_int_eq_card_A_minus_one_plus_unstable_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes max_eq: "Max A = n"
  shows "card (mod_sumset_int n A A) =
    card A - 1 + card (lower_sum_holes A \<union> upper_sum_holes A)"
proof -
  have card_mod:
    "card (mod_sumset_int n A A) =
      card (mod_image_int n A) + card (lower_sum_holes A \<union> upper_sum_holes A)"
    by (rule card_mod_sumset_int_eq_card_mod_image_plus_unstable_holes
        [OF fin n_pos subset zero top max_eq])
  have card_B: "card (mod_image_int n A) = card A - 1"
    by (rule card_mod_image_int_normalized_interval[OF fin n_pos subset zero top])
  show ?thesis
    using card_mod card_B by simp
qed

lemma normalized_sumset_card_eq_mod_sumset_plus_card_inter_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes max_eq: "Max A = n"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  shows "card (sumset A A) =
    card (mod_sumset_int n A A) + card A +
    card (lower_sum_holes A \<inter> upper_sum_holes A)"
proof -
  let ?L = "lower_sum_holes A"
  let ?U = "upper_sum_holes A"
  have sum_card:
    "card (sumset A A) = 2 * card A - 1 + card ?L + card ?U"
    by (rule normalized_sumset_card_eq_with_holes[OF fin zero nonneg])
  have mod_card:
    "card (mod_sumset_int n A A) = card A - 1 + card (?L \<union> ?U)"
    by (rule card_mod_sumset_int_eq_card_A_minus_one_plus_unstable_holes
        [OF fin n_pos subset zero top max_eq])
  have union_inter:
    "card ?L + card ?U = card (?L \<union> ?U) + card (?L \<inter> ?U)"
    by (rule card_Un_Int) simp_all
  show ?thesis
    using sum_card mod_card union_inter by linarith
qed

lemma card_mod_sumset_int_eq_diameter_minus_stable_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes max_eq: "Max A = n"
  shows "card (mod_sumset_int n A A) = nat n - card (stable_sum_holes A)"
proof -
  let ?C = "mod_sumset_int n A A"
  let ?R = "{0..n - 1}"
  let ?G = "{x. 0 < x \<and> x < n \<and> x \<notin> ?C}"
  have C_sub: "?C \<subseteq> ?R"
    unfolding mod_sumset_int_def by (rule mod_image_int_subset_residues[OF n_pos])
  have zero_C: "0 \<in> ?C"
    using zero unfolding mod_sumset_int_iff
    by (rule_tac x = 0 in bexI, rule_tac x = 0 in bexI) simp_all
  have R_minus_C: "?R - ?C = ?G"
  proof
    show "?R - ?C \<subseteq> ?G"
    proof
      fix x
      assume x_in: "x \<in> ?R - ?C"
      then have x_bounds: "0 \<le> x" "x < n"
        by auto
      have x_ne_zero: "x \<noteq> 0"
        using x_in zero_C by auto
      with x_bounds x_in show "x \<in> ?G"
        by auto
    qed
    show "?G \<subseteq> ?R - ?C"
    proof
      fix x
      assume "x \<in> ?G"
      then show "x \<in> ?R - ?C"
        by auto
    qed
  qed
  have stable_eq: "stable_sum_holes A = ?G"
    using stable_sum_holes_eq_mod_sumset_gaps[OF fin n_pos subset zero top] max_eq by simp
  have finC: "finite ?C"
    by (rule finite_mod_sumset_int[OF fin fin])
  have card_diff: "card (?R - ?C) = card ?R - card ?C"
    by (rule card_Diff_subset[OF finC C_sub])
  have cardC_le: "card ?C \<le> card ?R"
    by (rule card_mono[OF _ C_sub]) simp
  have cardR: "card ?R = nat n"
    using n_pos by simp
  have card_stable: "card (stable_sum_holes A) = nat n - card ?C"
    using card_diff cardR stable_eq R_minus_C by simp
  show ?thesis
    using card_stable cardC_le cardR by simp
qed

lemma mod_sub_translate_inj_on_residues:
  fixes x n :: int
  assumes n_pos: "0 < n"
  shows "inj_on (\<lambda>y. (x - y) mod n) {0..n - 1}"
proof (rule inj_onI)
  fix a b
  assume a_in: "a \<in> {0..n - 1}"
  assume b_in: "b \<in> {0..n - 1}"
  assume eq: "(x - a) mod n = (x - b) mod n"
  have a_bounds: "0 \<le> a" "a < n"
    using a_in by auto
  have b_bounds: "0 \<le> b" "b < n"
    using b_in by auto
  have dvd_ba: "n dvd b - a"
    using eq by (simp add: mod_eq_dvd_iff algebra_simps)
  then obtain q where q_eq: "b - a = n * q"
    by (auto elim: dvdE)
  have diff_lower: "- n < b - a"
    using a_bounds b_bounds by linarith
  have diff_upper: "b - a < n"
    using a_bounds b_bounds by linarith
  have "q = 0"
  proof (rule ccontr)
    assume "q \<noteq> 0"
    then consider "1 \<le> q" | "q \<le> -1"
      by linarith
    then show False
    proof cases
      case 1
      then have "n \<le> n * q"
      proof -
        have "1 * n \<le> q * n"
          using 1 n_pos by (intro mult_right_mono) simp_all
        then show ?thesis
          by (simp add: mult.commute)
      qed
      then show False
        using q_eq diff_upper by linarith
    next
      case 2
      then have "n * q \<le> - n"
      proof -
        have "q * n \<le> (-1) * n"
          using 2 n_pos by (intro mult_right_mono) simp_all
        then show ?thesis
          by (simp add: mult.commute)
      qed
      then show False
        using q_eq diff_lower by linarith
    qed
  qed
  then show "a = b"
    using q_eq by simp
qed

lemma card_mod_sub_translate_eq:
  fixes A :: "int set"
  fixes x n :: int
  assumes n_pos: "0 < n"
  assumes A_sub: "A \<subseteq> {0..n - 1}"
  shows "card ((\<lambda>y. (x - y) mod n) ` A) = card A"
proof -
  have finA: "finite A"
    using A_sub by (rule finite_subset) simp
  have inj_res: "inj_on (\<lambda>y. (x - y) mod n) {0..n - 1}"
    by (rule mod_sub_translate_inj_on_residues[OF n_pos])
  have inj_A: "inj_on (\<lambda>y. (x - y) mod n) A"
    by (rule inj_on_subset[OF inj_res A_sub])
  show ?thesis
    by (simp add: card_image finA inj_A)
qed

lemma stable_mod_gap_translate_disjoint:
  fixes A :: "int set"
  assumes n_pos: "0 < n"
  assumes x_mod: "x mod n = x"
  assumes gap: "x \<notin> mod_sumset_int n A A"
  shows "(\<lambda>y. (x - y) mod n) ` mod_image_int n A \<inter> mod_image_int n A = {}"
proof
  show "(\<lambda>y. (x - y) mod n) ` mod_image_int n A \<inter> mod_image_int n A \<subseteq> {}"
  proof
    fix r
    assume r_in: "r \<in> (\<lambda>y. (x - y) mod n) ` mod_image_int n A \<inter> mod_image_int n A"
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> A"
      and r_eq: "r = (x - (a mod n)) mod n"
      and r_mod: "r = b mod n"
      by (auto simp: mod_image_int_def)
    have x_sum_mod:
      "x mod n = ((a mod n) + (b mod n)) mod n"
      using r_eq r_mod by (simp add: mod_simps)
    have sum_mod: "x mod n = (a + b) mod n"
      using x_sum_mod by (simp add: mod_simps)
    have "x mod n \<in> mod_sumset_int n A A"
      using a_in b_in sum_mod by (auto simp: mod_sumset_int_iff)
    moreover have "x mod n = x"
      by (rule x_mod)
    ultimately have "x \<in> mod_sumset_int n A A"
      by simp
    with gap show "r \<in> {}"
      by simp
  qed
qed simp

lemma stable_mod_gap_card_le_half_diameter:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes n_pos: "0 < n"
  assumes subset: "A \<subseteq> {0..n}"
  assumes zero: "0 \<in> A"
  assumes top: "n \<in> A"
  assumes x_mod: "x mod n = x"
  assumes gap: "x \<notin> mod_sumset_int n A A"
  shows "2 * (card A - 1) \<le> nat n"
proof -
  let ?B = "mod_image_int n A"
  let ?T = "(\<lambda>y. (x - y) mod n) ` ?B"
  have B_sub: "?B \<subseteq> {0..n - 1}"
    by (rule mod_image_int_subset_residues[OF n_pos])
  have T_sub: "?T \<subseteq> {0..n - 1}"
    using n_pos by (auto intro!: pos_mod_bound)
  have disj: "?T \<inter> ?B = {}"
    by (rule stable_mod_gap_translate_disjoint[OF n_pos x_mod gap])
  have cardT: "card ?T = card ?B"
    by (rule card_mod_sub_translate_eq[OF n_pos B_sub])
  have cardB: "card ?B = card A - 1"
    by (rule card_mod_image_int_normalized_interval[OF fin n_pos subset zero top])
  have union_sub: "?T \<union> ?B \<subseteq> {0..n - 1}"
    using T_sub B_sub by auto
  have finT: "finite ?T"
    using T_sub by (rule finite_subset) simp
  have finB: "finite ?B"
    by (rule finite_mod_image_int[OF fin])
  have "card (?T \<union> ?B) = card ?T + card ?B"
    by (rule card_Un_disjoint[OF finT finB disj])
  also have "\<dots> = 2 * (card A - 1)"
    by (simp add: cardT cardB)
  finally have card_union: "card (?T \<union> ?B) = 2 * (card A - 1)" .
  have "card (?T \<union> ?B) \<le> card {0..n - 1}"
    by (rule card_mono[OF _ union_sub]) simp
  also have "\<dots> = nat n"
    using n_pos by simp
  finally show ?thesis
    using card_union by simp
qed

lemma stable_sum_holes_empty_of_short_diameter:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes short: "nat (Max A) \<le> 2 * card A - 3"
  shows "stable_sum_holes A = {}"
proof (rule ccontr)
  assume stable_nonempty: "stable_sum_holes A \<noteq> {}"
  then obtain x where x_stable: "x \<in> stable_sum_holes A"
    by auto
  let ?n = "Max A"
  have nonempty: "A \<noteq> {}"
    using zero by auto
  have top: "?n \<in> A"
    using fin nonempty by simp
  have subset: "A \<subseteq> {0..?n}"
    by (rule normalized_subset_interval[OF fin zero nonneg])
  have max_pos: "0 < ?n"
  proof -
    have "1 < card A"
      using card_ge by simp
    then have "A \<noteq> {0}"
      using zero fin by auto
    then obtain y where y_in: "y \<in> A" and y_ne: "y \<noteq> 0"
      using zero by auto
    have "0 < y"
      using nonneg[OF y_in] y_ne by linarith
    also have "y \<le> ?n"
      using fin y_in by simp
    finally show ?thesis .
  qed
  have stable_eq:
    "stable_sum_holes A =
      {x. 0 < x \<and> x < ?n \<and> x \<notin> mod_sumset_int ?n A A}"
    by (rule stable_sum_holes_eq_mod_sumset_gaps[OF fin max_pos subset zero top])
  have gap: "x \<notin> mod_sumset_int ?n A A"
    using x_stable stable_eq by auto
  have x_mod: "x mod ?n = x"
    using x_stable stable_eq max_pos by auto
  have lower: "2 * (card A - 1) \<le> nat ?n"
    by (rule stable_mod_gap_card_le_half_diameter[OF fin max_pos subset zero top x_mod gap])
  have card_pos: "0 < card A"
    using card_ge by simp
  have "2 * card A - 2 \<le> nat ?n"
    using lower card_pos by linarith
  with short card_ge show False
    by linarith
qed

lemma stable_sum_holes_nonempty_imp_large_diameter:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes stable_nonempty: "stable_sum_holes A \<noteq> {}"
  shows "2 * card A - 2 \<le> nat (Max A)"
proof (rule ccontr)
  assume "\<not> 2 * card A - 2 \<le> nat (Max A)"
  then have short: "nat (Max A) \<le> 2 * card A - 3"
    using card_ge by linarith
  have "stable_sum_holes A = {}"
    by (rule stable_sum_holes_empty_of_short_diameter[OF fin card_ge zero nonneg short])
  with stable_nonempty show False
    by simp
qed

subsection \<open>Normalization by the diameter gcd\<close>

definition shifted_int_set :: "int set \<Rightarrow> int set" where
  "shifted_int_set A = (\<lambda>x. x - Min A) ` A"

definition int_set_content :: "int set \<Rightarrow> int" where
  "int_set_content A = Gcd (shifted_int_set A)"

definition normalized_int_set :: "int set \<Rightarrow> int set" where
  "normalized_int_set A = (\<lambda>x. x div int_set_content A) ` shifted_int_set A"

lemma finite_shifted_int_set [intro]:
  assumes "finite A"
  shows "finite (shifted_int_set A)"
  using assms by (simp add: shifted_int_set_def)

lemma finite_normalized_int_set [intro]:
  assumes "finite A"
  shows "finite (normalized_int_set A)"
  using assms by (simp add: normalized_int_set_def shifted_int_set_def)

lemma zero_in_shifted_int_set:
  assumes "finite A" and "A \<noteq> {}"
  shows "0 \<in> shifted_int_set A"
  using assms by (auto simp: shifted_int_set_def)

lemma int_set_content_dvd_shift:
  assumes "x \<in> A"
  shows "int_set_content A dvd x - Min A"
  using assms by (auto simp: int_set_content_def shifted_int_set_def)

lemma int_set_content_dvd_shifted:
  assumes "s \<in> shifted_int_set A"
  shows "int_set_content A dvd s"
  using assms by (simp add: int_set_content_def)

lemma card_ge2_imp_Min_less_Max:
  assumes fin: "finite A" and card_ge2: "2 \<le> card A"
  shows "Min A < Max A"
proof -
  have nonempty: "A \<noteq> {}"
    using assms by auto
  have min_in: "Min A \<in> A"
    using fin nonempty by simp
  have "\<not> A \<subseteq> {Min A}"
  proof
    assume "A \<subseteq> {Min A}"
    with min_in have A_singleton: "A = {Min A}"
      by auto
    have "card A = card {Min A}"
      by (rule arg_cong[OF A_singleton])
    also have "\<dots> = 1"
      by simp
    finally have "card A = 1" .
    with card_ge2 show False
      by simp
  qed
  then obtain y where y_in: "y \<in> A" and y_ne: "y \<noteq> Min A"
    by auto
  have "Min A \<le> y"
    using fin y_in by simp
  with y_ne have "Min A < y"
    by simp
  also have "y \<le> Max A"
    using fin y_in by simp
  finally show ?thesis .
qed

lemma int_set_content_pos:
  assumes fin: "finite A" and card_ge2: "2 \<le> card A"
  shows "0 < int_set_content A"
proof -
  have nonempty: "A \<noteq> {}"
    using assms by auto
  have max_in: "Max A \<in> A"
    using fin nonempty by simp
  have min_lt_max: "Min A < Max A"
    by (rule card_ge2_imp_Min_less_Max[OF fin card_ge2])
  have max_shift: "Max A - Min A \<in> shifted_int_set A"
    using max_in by (auto simp: shifted_int_set_def)
  have "Max A - Min A \<noteq> 0"
    using min_lt_max by simp
  then have "\<not> shifted_int_set A \<subseteq> {0}"
    using max_shift by auto
  then have "int_set_content A \<noteq> 0"
    by (simp add: int_set_content_def)
  moreover have "0 \<le> int_set_content A"
    by (simp add: int_set_content_def)
  ultimately show ?thesis
    by simp
qed

lemma normalized_int_set_reconstruction:
  assumes fin: "finite A" and card_ge2: "2 \<le> card A"
  shows "affine_image_int (Min A) (int_set_content A) (normalized_int_set A) = A"
proof
  let ?g = "int_set_content A"
  show "affine_image_int (Min A) ?g (normalized_int_set A) \<subseteq> A"
  proof
    fix y
    assume "y \<in> affine_image_int (Min A) ?g (normalized_int_set A)"
    then obtain z where z_in: "z \<in> normalized_int_set A" and y_eq: "y = Min A + ?g * z"
      by (auto simp: affine_image_int_def)
    from z_in obtain s where s_in: "s \<in> shifted_int_set A" and z_eq: "z = s div ?g"
      by (auto simp: normalized_int_set_def)
    from s_in obtain x where x_in: "x \<in> A" and s_eq: "s = x - Min A"
      by (auto simp: shifted_int_set_def)
    have dvd: "?g dvd x - Min A"
      by (rule int_set_content_dvd_shift[OF x_in])
    have "?g * ((x - Min A) div ?g) = x - Min A"
      using dvd by simp
    then have "y = x"
      using y_eq z_eq s_eq by simp
    with x_in show "y \<in> A"
      by simp
  qed
next
  let ?g = "int_set_content A"
  show "A \<subseteq> affine_image_int (Min A) ?g (normalized_int_set A)"
  proof
    fix x
    assume x_in: "x \<in> A"
    have shift_in: "x - Min A \<in> shifted_int_set A"
      using x_in by (auto simp: shifted_int_set_def)
    have norm_in: "(x - Min A) div ?g \<in> normalized_int_set A"
      using shift_in by (auto simp: normalized_int_set_def)
    have dvd: "?g dvd x - Min A"
      by (rule int_set_content_dvd_shift[OF x_in])
    have "?g * ((x - Min A) div ?g) = x - Min A"
      using dvd by simp
    then have "x = Min A + ?g * ((x - Min A) div ?g)"
      by simp
    with norm_in show "x \<in> affine_image_int (Min A) ?g (normalized_int_set A)"
      by (auto simp: affine_image_int_def)
  qed
qed

lemma card_normalized_int_set:
  assumes fin: "finite A" and card_ge2: "2 \<le> card A"
  shows "card (normalized_int_set A) = card A"
proof -
  let ?g = "int_set_content A"
  have finN: "finite (normalized_int_set A)"
    by (rule finite_normalized_int_set[OF fin])
  have g_nonzero: "?g \<noteq> 0"
    using int_set_content_pos[OF fin card_ge2] by simp
  have "card A = card (affine_image_int (Min A) ?g (normalized_int_set A))"
    using normalized_int_set_reconstruction[OF fin card_ge2] by simp
  also have "\<dots> = card (normalized_int_set A)"
    by (rule card_affine_image_int[OF finN g_nonzero])
  finally show ?thesis
    by simp
qed

lemma card_sumset_normalized_int_set:
  assumes fin: "finite A" and card_ge2: "2 \<le> card A"
  shows "card (sumset (normalized_int_set A) (normalized_int_set A)) =
    card (sumset A A)"
proof -
  let ?N = "normalized_int_set A"
  let ?g = "int_set_content A"
  have finN: "finite ?N"
    by (rule finite_normalized_int_set[OF fin])
  have g_nonzero: "?g \<noteq> 0"
    using int_set_content_pos[OF fin card_ge2] by simp
  have A_eq: "A = affine_image_int (Min A) ?g ?N"
    using normalized_int_set_reconstruction[OF fin card_ge2] by simp
  let ?A' = "affine_image_int (Min A) ?g ?N"
  have sum_eq1: "sumset A A = sumset ?A' A"
    using A_eq by (rule arg_cong[where f = "\<lambda>X. sumset X A"])
  have sum_eq2: "sumset ?A' A = sumset ?A' ?A'"
    using A_eq by (rule arg_cong[where f = "\<lambda>X. sumset ?A' X"])
  have "card (sumset A A) = card (sumset ?A' ?A')"
    using sum_eq1 sum_eq2 by simp
  also have "\<dots> = card (sumset ?N ?N)"
    by (rule card_sumset_affine_image_int_self[OF finN g_nonzero])
  finally show ?thesis
    by simp
qed

lemma zero_in_normalized_int_set:
  assumes "finite A" and "A \<noteq> {}"
  shows "0 \<in> normalized_int_set A"
proof -
  have "0 div int_set_content A \<in> normalized_int_set A"
    unfolding normalized_int_set_def
  proof (rule image_eqI)
    show "0 div int_set_content A = 0 div int_set_content A"
      by simp
    show "0 \<in> shifted_int_set A"
      by (rule zero_in_shifted_int_set[OF assms])
  qed
  then show ?thesis
    by simp
qed

lemma normalized_int_set_nonneg:
  assumes fin: "finite A" and card_ge2: "2 \<le> card A"
  assumes x_in: "x \<in> normalized_int_set A"
  shows "0 \<le> x"
proof -
  let ?g = "int_set_content A"
  from x_in obtain s where s_in: "s \<in> shifted_int_set A" and x_eq: "x = s div ?g"
    by (auto simp: normalized_int_set_def)
  from s_in obtain a where a_in: "a \<in> A" and s_eq: "s = a - Min A"
    by (auto simp: shifted_int_set_def)
  have "Min A \<le> a"
    using fin a_in by simp
  then have "0 \<le> s"
    using s_eq by simp
  moreover have "0 < ?g"
    by (rule int_set_content_pos[OF fin card_ge2])
  ultimately show ?thesis
    using x_eq by (simp add: pos_imp_zdiv_nonneg_iff)
qed

lemma Gcd_normalized_int_set:
  assumes fin: "finite A" and card_ge2: "2 \<le> card A"
  shows "Gcd (normalized_int_set A) = 1"
proof -
  let ?N = "normalized_int_set A"
  let ?g = "int_set_content A"
  have g_nonzero: "?g \<noteq> 0"
    using int_set_content_pos[OF fin card_ge2] by simp
  have one_eq: "(1 :: int) = Gcd ?N"
  proof (rule GcdI)
    fix n
    assume "n \<in> ?N"
    show "(1 :: int) dvd n"
      by simp
  next
    fix c :: int
    assume c_dvd: "\<And>n. n \<in> ?N \<Longrightarrow> c dvd n"
    have gc_dvd_shift: "?g * c dvd s" if s_in: "s \<in> shifted_int_set A" for s
    proof -
      have div_in: "s div ?g \<in> ?N"
        using s_in by (auto simp: normalized_int_set_def)
      then have c_dvd_div: "c dvd s div ?g"
        by (rule c_dvd)
      obtain k where k: "s div ?g = c * k"
        using c_dvd_div unfolding dvd_def by blast
      have g_dvd_s: "?g dvd s"
        by (rule int_set_content_dvd_shifted[OF s_in])
      have "s = ?g * (s div ?g)"
        using g_dvd_s by simp
      also have "\<dots> = (?g * c) * k"
        using k by (simp add: algebra_simps)
      finally show ?thesis
        unfolding dvd_def by blast
    qed
    have "?g * c dvd Gcd (shifted_int_set A)"
      by (rule Gcd_greatest) (rule gc_dvd_shift)
    then have "?g * c dvd ?g"
      by (simp add: int_set_content_def)
    then have "?g * c dvd ?g * 1"
      by simp
    with g_nonzero show "c dvd (1 :: int)"
      by simp
  next
    show "normalize (1 :: int) = 1"
      by simp
  qed
  then show ?thesis
    by simp
qed

lemma group_closure_eq_UNIV_of_Gcd_one:
  fixes A :: "int set"
  assumes "Gcd A = 1"
  shows "group_closure A = UNIV"
  using assms by (auto simp: group_closure_eq)

lemma common_divisor_dvd_one_of_Gcd_one:
  fixes A :: "int set"
  assumes gcd_one: "Gcd A = 1"
  assumes dvd_all: "\<And>a. a \<in> A \<Longrightarrow> d dvd a"
  shows "d dvd (1 :: int)"
proof -
  have "d dvd Gcd A"
    by (rule Gcd_greatest) (rule dvd_all)
  then show ?thesis
    using gcd_one by simp
qed

lemma dvd_of_dvd_mod_and_modulus:
  fixes a n d :: int
  assumes d_n: "d dvd n"
  assumes d_mod: "d dvd (a mod n)"
  shows "d dvd a"
proof -
  have "a = n * (a div n) + a mod n"
    by simp
  moreover have "d dvd n * (a div n)"
    using d_n by simp
  ultimately show ?thesis
    using d_mod by (metis dvd_add)
qed

lemma Gcd_one_not_all_mod_multiples_of_proper_divisor:
  fixes A :: "int set"
  assumes gcd_one: "Gcd A = 1"
  assumes d_gt_one: "1 < d"
  assumes d_n: "d dvd n"
  assumes residues: "\<And>a. a \<in> A \<Longrightarrow> d dvd (a mod n)"
  shows False
proof -
  have dvd_all: "\<And>a. a \<in> A \<Longrightarrow> d dvd a"
  proof -
    fix a
    assume a_in: "a \<in> A"
    show "d dvd a"
      by (rule dvd_of_dvd_mod_and_modulus[OF d_n residues[OF a_in]])
  qed
  have "d dvd (1 :: int)"
    by (rule common_divisor_dvd_one_of_Gcd_one[OF gcd_one dvd_all])
  with d_gt_one show False
    by auto
qed

lemma normalized_mod_image_subset_stabilizer_contradicts_Gcd_one:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes gcd_one: "Gcd A = 1"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  assumes stable_nonempty: "stable_sum_holes A \<noteq> {}"
  defines "n \<equiv> Max A"
  defines "B \<equiv> mod_image_int n A"
  defines "p \<equiv> nat n"
  defines "C \<equiv> Zmod.sumset p B B"
  assumes B_subset_H: "B \<subseteq> Zmod.stabilizer p C"
  shows False
proof -
  have nonempty: "A \<noteq> {}"
    using zero by auto
  have top: "n \<in> A"
    using fin nonempty by (simp add: n_def)
  have subset: "A \<subseteq> {0..n}"
    using normalized_subset_interval[OF fin zero nonneg] by (simp add: n_def)
  have n_pos: "0 < n"
  proof -
    have "1 < card A"
      using card_ge by simp
    then have "A \<noteq> {0}"
      using zero fin by auto
    then obtain y where y_in: "y \<in> A" and y_ne: "y \<noteq> 0"
      using zero by auto
    have "0 < y"
      using nonneg[OF y_in] y_ne by linarith
    also have "y \<le> n"
      using fin y_in by (simp add: n_def)
    finally show ?thesis .
  qed
  have p_pos: "0 < p"
    using n_pos by (simp add: p_def)
  have int_p: "int p = n"
    using n_pos by (simp add: p_def)
  have B_sub: "B \<subseteq> {0..int p - 1}"
    using mod_image_int_subset_residues[OF n_pos, of A] by (simp add: B_def int_p)
  have C_eq_mod: "C = mod_sumset_int n A A"
  proof -
    have "C = mod_sumset_int (int p) B B"
      unfolding C_def by (rule zmod_sumset_eq_mod_sumset_int[OF p_pos B_sub B_sub])
    also have "\<dots> = mod_sumset_int n B B"
      by (simp add: int_p)
    also have "\<dots> = mod_sumset_int n A A"
      unfolding B_def by (rule mod_sumset_int_mod_image_self[OF n_pos])
    finally show ?thesis .
  qed
  have C_sub: "C \<subseteq> {0..int p - 1}"
    using C_eq_mod mod_image_int_subset_residues[OF n_pos, of "sumset A A"]
    by (auto simp: mod_sumset_int_def int_p)
  have zero_C: "0 \<in> C"
  proof -
    have witnesses: "\<exists>a\<in>A. \<exists>b\<in>A. 0 = (a + b) mod n"
    proof
      show "0 \<in> A"
        by (rule zero)
      show "\<exists>b\<in>A. 0 = (0 + b) mod n"
      proof
        show "0 \<in> A"
          by (rule zero)
        show "0 = (0 + 0) mod n"
          using n_pos by simp
      qed
    qed
    then have "0 \<in> mod_sumset_int n A A"
      by (simp add: mod_sumset_int_iff)
    then show ?thesis
      using C_eq_mod by simp
  qed
  have H_nontrivial:
    "Zmod.stabilizer p C \<noteq> {0}"
  proof -
    have "Zmod.stabilizer (nat n)
        (Zmod.sumset (nat n) (mod_image_int n A) (mod_image_int n A)) \<noteq> {0}"
      by (rule normalized_small_doubling_mod_stabilizer_nontrivial
          [OF fin card_ge n_pos subset zero top small_doubling])
    then show ?thesis
      by (simp add: B_def p_def C_def)
  qed
  have H_proper: "Zmod.stabilizer p C \<noteq> {0..int p - 1}"
  proof
    assume full: "Zmod.stabilizer p C = {0..int p - 1}"
    obtain x where x_stable: "x \<in> stable_sum_holes A"
      using stable_nonempty by auto
    have stable_eq:
      "stable_sum_holes A =
        {x. 0 < x \<and> x < n \<and> x \<notin> mod_sumset_int n A A}"
      by (rule stable_sum_holes_eq_mod_sumset_gaps[OF fin n_pos subset zero top])
    then have x_bounds: "0 < x" "x < n"
      using x_stable by auto
    have x_gap: "x \<notin> mod_sumset_int n A A"
      using x_stable stable_eq by auto
    have carrier_sub: "{0..int p - 1} \<subseteq> C"
      by (rule zmod_full_stabilizer_zero_imp_carrier_subset
          [OF p_pos C_sub zero_C full])
    have "x \<in> {0..int p - 1}"
      using x_bounds by (simp add: int_p)
    then have "x \<in> C"
      using carrier_sub by auto
    with x_gap C_eq_mod show False
      by simp
  qed
  obtain d where d_gt_one: "1 < d" and d_p: "d dvd int p"
      and d_H: "\<And>h. h \<in> Zmod.stabilizer p C \<Longrightarrow> d dvd h"
    using zmod_stabilizer_obtain_proper_divisor[OF p_pos H_nontrivial H_proper]
    by blast
  have d_n: "d dvd n"
    using d_p by (simp add: int_p)
  have residues: "\<And>a. a \<in> A \<Longrightarrow> d dvd (a mod n)"
  proof -
    fix a
    assume a_in: "a \<in> A"
    have "a mod n \<in> B"
      using a_in by (auto simp: B_def mod_image_int_def)
    then have "a mod n \<in> Zmod.stabilizer p C"
      using B_subset_H by auto
    then show "d dvd (a mod n)"
      by (rule d_H)
  qed
  show False
    by (rule Gcd_one_not_all_mod_multiples_of_proper_divisor
        [OF gcd_one d_gt_one d_n residues])
qed

lemma Min_normalized_int_set:
  assumes fin: "finite A" and card_ge2: "2 \<le> card A"
  shows "Min (normalized_int_set A) = 0"
proof -
  have nonempty: "A \<noteq> {}"
    using card_ge2 by auto
  have zero: "0 \<in> normalized_int_set A"
    by (rule zero_in_normalized_int_set[OF fin nonempty])
  have nonneg: "\<And>x. x \<in> normalized_int_set A \<Longrightarrow> 0 \<le> x"
    by (rule normalized_int_set_nonneg[OF fin card_ge2])
  show ?thesis
    by (rule Min_eq_zero_of_zero_mem_nonneg[OF finite_normalized_int_set[OF fin] zero nonneg])
qed

lemma affine_image_int_subset_ap:
  assumes "A \<subseteq> int_ap_segment a d n"
  shows "affine_image_int c e A \<subseteq> int_ap_segment (c + e * a) (e * d) n"
proof
  fix x
  assume "x \<in> affine_image_int c e A"
  then obtain y where y: "y \<in> A" and x: "x = c + e * y"
    by (auto simp: affine_image_int_def)
  from assms y obtain i where i_lt: "i < n" and y_eq: "y = a + int i * d"
    by (auto simp: int_ap_segment_def)
  have "x = (c + e * a) + int i * (e * d)"
    using x y_eq by (simp add: algebra_simps)
  with i_lt show "x \<in> int_ap_segment (c + e * a) (e * d) n"
    by (auto simp: int_ap_segment_def)
qed

subsection \<open>Progression covers\<close>

definition progression_cover_length_at_most :: "int set \<Rightarrow> nat \<Rightarrow> bool" where
  "progression_cover_length_at_most A L \<longleftrightarrow>
    (\<exists>a d n. 0 < d \<and> A \<subseteq> int_ap_segment a d n \<and> n \<le> L)"

lemma progression_cover_length_at_mostI:
  assumes "0 < d" and "A \<subseteq> int_ap_segment a d n" and "n \<le> L"
  shows "progression_cover_length_at_most A L"
  using assms unfolding progression_cover_length_at_most_def by blast

lemma progression_cover_length_at_mostE:
  assumes "progression_cover_length_at_most A L"
  obtains a d n where "0 < d" "A \<subseteq> int_ap_segment a d n" "n \<le> L"
  using assms unfolding progression_cover_length_at_most_def by blast

lemma progression_cover_length_at_most_mono:
  assumes cover: "progression_cover_length_at_most A L"
  assumes le: "L \<le> M"
  shows "progression_cover_length_at_most A M"
proof -
  obtain a d n where d_pos: "0 < d" and A_sub: "A \<subseteq> int_ap_segment a d n" and n_le: "n \<le> L"
    using cover by (rule progression_cover_length_at_mostE)
  from n_le le have "n \<le> M"
    by simp
  with d_pos A_sub show ?thesis
    by (rule progression_cover_length_at_mostI)
qed

lemma progression_cover_of_diameter_bound:
  assumes fin: "finite A"
  assumes nonempty: "A \<noteq> {}"
  assumes len_le: "nat (Max A - Min A + 1) \<le> L"
  shows "progression_cover_length_at_most A L"
proof -
  have one_pos: "0 < (1 :: int)"
    by simp
  have A_sub: "A \<subseteq> int_ap_segment (Min A) 1 (nat (Max A - Min A + 1))"
    by (rule finite_int_set_subset_min_max_ap[OF fin nonempty])
  show ?thesis
    by (rule progression_cover_length_at_mostI[OF one_pos A_sub len_le])
qed

lemma progression_cover_affine_image_pos:
  assumes cover: "progression_cover_length_at_most A L"
  assumes e_pos: "0 < e"
  shows "progression_cover_length_at_most (affine_image_int c e A) L"
proof -
  obtain a d n where d_pos: "0 < d" and A_sub: "A \<subseteq> int_ap_segment a d n" and n_le: "n \<le> L"
    using cover by (rule progression_cover_length_at_mostE)
  have ed_pos: "0 < e * d"
    using e_pos d_pos by simp
  have image_sub: "affine_image_int c e A \<subseteq> int_ap_segment (c + e * a) (e * d) n"
    by (rule affine_image_int_subset_ap[OF A_sub])
  show ?thesis
    by (rule progression_cover_length_at_mostI[OF ed_pos image_sub n_le])
qed

theorem freiman_3k_minus_4_from_diameter_bound:
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes diameter_le: "nat (Max A - Min A + 1) \<le> card (sumset A A) - card A + 1"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  have "A \<noteq> {}"
    using card_ge by auto
  then show ?thesis
    by (rule progression_cover_of_diameter_bound[OF fin _ diameter_le])
qed

theorem normalized_progression_cover_from_max_bound:
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes max_bound: "nat (Max A + 1) \<le> card (sumset A A) - card A + 1"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  have min0: "Min A = 0"
    by (rule Min_eq_zero_of_zero_mem_nonneg[OF fin zero nonneg])
  have "nat (Max A - Min A + 1) \<le> card (sumset A A) - card A + 1"
    using max_bound by (simp add: min0)
  then show ?thesis
    by (rule freiman_3k_minus_4_from_diameter_bound[OF fin card_ge])
qed

theorem normalized_progression_cover_from_hole_contribution:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes hole_cover:
    "card (interval_holes A) \<le> card (lower_sum_holes A) + card (upper_sum_holes A)"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  have max_bound: "nat (Max A + 1) \<le> card (sumset A A) - card A + 1"
    by (rule normalized_max_bound_from_hole_contribution[OF fin zero nonneg hole_cover])
  show ?thesis
    by (rule normalized_progression_cover_from_max_bound[OF fin card_ge zero nonneg max_bound])
qed

theorem normalized_progression_cover_from_no_stable_sum_holes:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes stable_empty: "stable_sum_holes A = {}"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  have hole_cover:
    "card (interval_holes A) \<le> card (lower_sum_holes A) + card (upper_sum_holes A)"
    by (rule hole_cover_of_no_stable_sum_holes[OF stable_empty])
  show ?thesis
    by (rule normalized_progression_cover_from_hole_contribution
        [OF fin card_ge zero nonneg hole_cover])
qed

theorem normalized_progression_cover_from_short_diameter:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes short: "nat (Max A) \<le> 2 * card A - 3"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  have stable_empty: "stable_sum_holes A = {}"
    by (rule stable_sum_holes_empty_of_short_diameter[OF fin card_ge zero nonneg short])
  show ?thesis
    by (rule normalized_progression_cover_from_no_stable_sum_holes
        [OF fin card_ge zero nonneg stable_empty])
qed

theorem normalized_progression_cover_from_stable_hole_contribution:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  assumes stable_contribution:
    "stable_sum_holes A \<noteq> {} \<Longrightarrow>
      card A - 2 \<le> card (lower_sum_holes A) + card (upper_sum_holes A)"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  have stable_empty: "stable_sum_holes A = {}"
  proof (rule ccontr)
    assume "stable_sum_holes A \<noteq> {}"
    then have extra:
      "card A - 2 \<le> card (lower_sum_holes A) + card (upper_sum_holes A)"
      by (rule stable_contribution)
    have lower:
      "2 * card A - 1 + card (lower_sum_holes A) + card (upper_sum_holes A)
        \<le> card (sumset A A)"
      by (rule normalized_sumset_lower_bound_with_holes[OF fin zero nonneg])
    have "3 * card A - 3 \<le> card (sumset A A)"
      using card_ge extra lower by linarith
    with small_doubling show False
      using card_ge by linarith
  qed
  show ?thesis
    by (rule normalized_progression_cover_from_no_stable_sum_holes
        [OF fin card_ge zero nonneg stable_empty])
qed

lemma normalized_stabilizer_count:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  defines "n \<equiv> Max A"
  defines "B \<equiv> mod_image_int n A"
  defines "p \<equiv> nat n"
  defines "C \<equiv> Zmod.sumset p B B"
  defines "H \<equiv> Zmod.stabilizer p C"
  defines "D \<equiv> Zmod.sumset p B H"
  assumes not_subset: "\<not> B \<subseteq> H"
  shows "card H \<le>
    1 + card (lower_sum_holes A \<inter> upper_sum_holes A) +
      2 * (card D - card B)"
proof -
  have nonempty: "A \<noteq> {}"
    using zero by auto
  have top: "n \<in> A"
    using fin nonempty by (simp add: n_def)
  have subset: "A \<subseteq> {0..n}"
    using normalized_subset_interval[OF fin zero nonneg] by (simp add: n_def)
  have max_eq: "Max A = n"
    by (simp add: n_def)
  have n_pos: "0 < n"
  proof -
    have "1 < card A"
      using card_ge by simp
    then have "A \<noteq> {0}"
      using zero fin by auto
    then obtain y where y_in: "y \<in> A" and y_ne: "y \<noteq> 0"
      using zero by auto
    have "0 < y"
      using nonneg[OF y_in] y_ne by linarith
    also have "y \<le> n"
      using fin y_in by (simp add: n_def)
    finally show ?thesis .
  qed
  have p_pos: "0 < p"
    using n_pos by (simp add: p_def)
  have int_p: "int p = n"
    using n_pos by (simp add: p_def)
  have B_sub: "B \<subseteq> {0..int p - 1}"
    using mod_image_int_subset_residues[OF n_pos, of A] by (simp add: B_def int_p)
  have H_sub: "H \<subseteq> {0..int p - 1}"
    unfolding H_def using Zmod.stabilizer_subset_group[of p C] p_pos by auto
  have H_sub_n: "H \<subseteq> {0..n - 1}"
    using H_sub by (simp add: int_p)
  have finB: "finite B"
    unfolding B_def by (rule finite_mod_image_int[OF fin])
  have zero_B: "0 \<in> B"
    unfolding B_def mod_image_int_def
  proof (rule image_eqI)
    show "0 = 0 mod n"
      by simp
    show "0 \<in> A"
      by (rule zero)
  qed
  have B_eq: "B = A - {n}"
    unfolding B_def by (rule mod_image_int_normalized_interval[OF n_pos subset zero top])
  have zero_H: "0 \<in> H"
    unfolding H_def by (rule Zmod.zero_mem_stabilizer)
  have add_closed_H: "(x + y) mod n \<in> H" if x_H: "x \<in> H" and y_H: "y \<in> H" for x y
  proof -
    have "(x + y) mod int p \<in> H"
      unfolding H_def by (rule zmod_stabilizer_add_closed[OF x_H[unfolded H_def] y_H[unfolded H_def]])
    then show ?thesis
      using int_p by simp
  qed
  have not_subset_unfolded:
    "\<not> B \<subseteq> Zmod.stabilizer p (Zmod.sumset p B B)"
    using not_subset by (simp add: H_def C_def)
  obtain b c where b_B: "b \<in> B" and c_B: "c \<in> B"
      and coset_disj_unfolded:
        "Zmod.sumset p {((b + c) mod int p)}
          (Zmod.stabilizer p (Zmod.sumset p B B)) \<inter>
          Zmod.sumset p B (Zmod.stabilizer p (Zmod.sumset p B B)) = {}"
    by (rule zmod_obtain_sum_coset_disjoint_D
        [OF p_pos B_sub finB zero_B not_subset_unfolded])
  have coset_disj: "Zmod.sumset p {((b + c) mod int p)} H \<inter> D = {}"
    using coset_disj_unfolded by (simp add: C_def H_def D_def)
  define R where "R = mod_translate_int n b H"
  define S where "S = mod_translate_int n c H"
  define K where "K = mod_translate_int n ((b + c) mod n) H"
  have b_A: "b \<in> A" and b_ne_top: "b \<noteq> n"
    using b_B B_eq by auto
  have c_A: "c \<in> A" and c_ne_top: "c \<noteq> n"
    using c_B B_eq by auto
  have b_bounds: "0 \<le> b" "b < n"
    using B_sub b_B b_ne_top by (auto simp: int_p)
  have c_bounds: "0 \<le> c" "c < n"
    using B_sub c_B c_ne_top by (auto simp: int_p)
  have center_carrier: "(b + c) mod int p \<in> {0..int p - 1}"
    using p_pos by (auto intro!: pos_mod_bound)
  have K_zmod: "Zmod.sumset p {((b + c) mod int p)} H = K"
    using zmod_singleton_sumset_eq_mod_translate_int[OF p_pos center_carrier H_sub]
    by (simp add: K_def int_p)
  have K_disj_D: "K \<inter> D = {}"
    using coset_disj K_zmod by simp
  have K_sub_n: "K \<subseteq> {0..n - 1}"
    unfolding K_def by (rule mod_translate_int_subset_residues[OF n_pos])
  have B_subset_D: "B \<subseteq> D"
  proof
    fix x
    assume x_B: "x \<in> B"
    have x_carrier: "x \<in> {0..int (p - 1)}"
      using B_sub x_B p_pos by auto
    have zero_carrier: "0 \<in> {0..int (p - 1)}"
      using p_pos by auto
    have "(x + 0) mod int p \<in> Zmod.sumset p B H"
      by (rule Zmod.sumset.sumsetI[OF x_B x_carrier zero_H zero_carrier])
    then show "x \<in> D"
      using x_carrier p_pos by (simp add: D_def)
  qed
  have K_disj_A: "K \<inter> A = {}"
  proof
    show "K \<inter> A \<subseteq> {}"
    proof
      fix x
      assume x_in: "x \<in> K \<inter> A"
      then have x_K: "x \<in> K" and x_A: "x \<in> A"
        by auto
      have x_bounds: "0 \<le> x" "x < n"
        using K_sub_n x_K by auto
      have x_ne_top: "x \<noteq> n"
        using x_bounds by linarith
      have x_B: "x \<in> B"
        using x_A x_ne_top B_eq by auto
      then have x_D: "x \<in> D"
        using B_subset_D by auto
      with x_K K_disj_D show "x \<in> {}"
        by auto
    qed
  qed simp
  have K_disj_raw: "mod_translate_int n ((b + c) mod n) H \<inter> A = {}"
    using K_disj_A by (simp add: K_def)
  have local_count_raw:
    "card H \<le>
      1 + card ((lower_sum_holes A \<inter> upper_sum_holes A) \<inter>
          mod_translate_int n ((b + c) mod n) H) +
        card (mod_translate_int n b H - A) + card (mod_translate_int n c H - A)"
    by (rule sum_coset_lower_upper_inter_card
        [OF n_pos fin max_eq H_sub_n zero_H add_closed_H b_A
          b_bounds(1) b_bounds(2) c_A c_bounds(1) c_bounds(2) K_disj_raw])
  have local_count:
    "card H \<le>
      1 + card ((lower_sum_holes A \<inter> upper_sum_holes A) \<inter> K) +
        card (R - A) + card (S - A)"
    using local_count_raw by (simp add: R_def S_def K_def)
  have D_sub: "D \<subseteq> {0..int p - 1}"
    unfolding D_def using Zmod.sumset_subset_carrier[of p B H] p_pos by auto
  have finD: "finite D"
    using D_sub by (rule finite_subset) simp
  have R_sub_D: "R \<subseteq> D"
  proof
    fix x
    assume x_R: "x \<in> R"
    then obtain h where h_H: "h \<in> H" and x_eq: "x = (b + h) mod n"
      by (auto simp: R_def mod_translate_int_def)
    have b_carrier: "b \<in> {0..int (p - 1)}"
      using B_sub b_B p_pos by auto
    have h_carrier: "h \<in> {0..int (p - 1)}"
      using H_sub h_H p_pos by auto
    have "(b + h) mod int p \<in> Zmod.sumset p B H"
      by (rule Zmod.sumset.sumsetI[OF b_B b_carrier h_H h_carrier])
    then show "x \<in> D"
      using x_eq by (simp add: D_def int_p)
  qed
  have S_sub_D: "S \<subseteq> D"
  proof
    fix x
    assume x_S: "x \<in> S"
    then obtain h where h_H: "h \<in> H" and x_eq: "x = (c + h) mod n"
      by (auto simp: S_def mod_translate_int_def)
    have c_carrier: "c \<in> {0..int (p - 1)}"
      using B_sub c_B p_pos by auto
    have h_carrier: "h \<in> {0..int (p - 1)}"
      using H_sub h_H p_pos by auto
    have "(c + h) mod int p \<in> Zmod.sumset p B H"
      by (rule Zmod.sumset.sumsetI[OF c_B c_carrier h_H h_carrier])
    then show "x \<in> D"
      using x_eq by (simp add: D_def int_p)
  qed
  have R_minus_sub: "R - A \<subseteq> D - B"
  proof
    fix x
    assume x_in: "x \<in> R - A"
    then have x_D: "x \<in> D"
      using R_sub_D by auto
    have "x \<notin> B"
      using x_in B_eq by auto
    then show "x \<in> D - B"
      using x_D by simp
  qed
  have S_minus_sub: "S - A \<subseteq> D - B"
  proof
    fix x
    assume x_in: "x \<in> S - A"
    then have x_D: "x \<in> D"
      using S_sub_D by auto
    have "x \<notin> B"
      using x_in B_eq by auto
    then show "x \<in> D - B"
      using x_D by simp
  qed
  have finDminus: "finite (D - B)"
    using finD by simp
  have card_R_minus: "card (R - A) \<le> card (D - B)"
    by (rule card_mono[OF finDminus R_minus_sub])
  have card_S_minus: "card (S - A) \<le> card (D - B)"
    by (rule card_mono[OF finDminus S_minus_sub])
  have card_inter:
    "card ((lower_sum_holes A \<inter> upper_sum_holes A) \<inter> K) \<le>
      card (lower_sum_holes A \<inter> upper_sum_holes A)"
  proof (rule card_mono)
    show "finite (lower_sum_holes A \<inter> upper_sum_holes A)"
      by simp
    show "lower_sum_holes A \<inter> upper_sum_holes A \<inter> K \<subseteq>
        lower_sum_holes A \<inter> upper_sum_holes A"
      by auto
  qed
  have diff_card: "card (D - B) = card D - card B"
    by (rule card_Diff_subset[OF finB B_subset_D])
  have "card H \<le>
      1 + card (lower_sum_holes A \<inter> upper_sum_holes A) +
        2 * card (D - B)"
    using local_count card_R_minus card_S_minus card_inter by linarith
  then show ?thesis
    using diff_card by simp
qed

theorem normalized_progression_cover_from_stabilizer_count:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes gcd_one: "Gcd A = 1"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  defines "n \<equiv> Max A"
  defines "B \<equiv> mod_image_int n A"
  defines "p \<equiv> nat n"
  defines "C \<equiv> Zmod.sumset p B B"
  defines "H \<equiv> Zmod.stabilizer p C"
  defines "D \<equiv> Zmod.sumset p B H"
  assumes stabilizer_count:
    "stable_sum_holes A \<noteq> {} \<Longrightarrow>
      \<not> B \<subseteq> H \<Longrightarrow>
      card H \<le>
        1 + card (lower_sum_holes A \<inter> upper_sum_holes A) +
        2 * (card D - card B)"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  have stable_empty: "stable_sum_holes A = {}"
  proof (rule ccontr)
    assume stable_nonempty: "stable_sum_holes A \<noteq> {}"
    have nonempty: "A \<noteq> {}"
      using zero by auto
    have top: "n \<in> A"
      using fin nonempty by (simp add: n_def)
    have subset: "A \<subseteq> {0..n}"
      using normalized_subset_interval[OF fin zero nonneg] by (simp add: n_def)
    have n_pos: "0 < n"
    proof -
      have "1 < card A"
        using card_ge by simp
      then have "A \<noteq> {0}"
        using zero fin by auto
      then obtain y where y_in: "y \<in> A" and y_ne: "y \<noteq> 0"
        using zero by auto
      have "0 < y"
        using nonneg[OF y_in] y_ne by linarith
      also have "y \<le> n"
        using fin y_in by (simp add: n_def)
      finally show ?thesis .
    qed
    have p_pos: "0 < p"
      using n_pos by (simp add: p_def)
    have int_p: "int p = n"
      using n_pos by (simp add: p_def)
    have B_sub: "B \<subseteq> {0..int p - 1}"
      using mod_image_int_subset_residues[OF n_pos, of A] by (simp add: B_def int_p)
    have finB: "finite B"
      unfolding B_def by (rule finite_mod_image_int[OF fin])
    have zero_B: "0 \<in> B"
      unfolding B_def mod_image_int_def
    proof (rule image_eqI)
      show "0 = 0 mod n"
        by simp
      show "0 \<in> A"
        by (rule zero)
    qed
    have nonemptyB: "B \<noteq> {}"
      using zero_B by auto
    have cardB: "card B = card A - 1"
      unfolding B_def
      by (rule card_mod_image_int_normalized_interval[OF fin n_pos subset zero top])
    have C_eq_mod: "C = mod_sumset_int n A A"
    proof -
      have "C = mod_sumset_int (int p) B B"
        unfolding C_def by (rule zmod_sumset_eq_mod_sumset_int[OF p_pos B_sub B_sub])
      also have "\<dots> = mod_sumset_int n B B"
        by (simp add: int_p)
      also have "\<dots> = mod_sumset_int n A A"
        unfolding B_def by (rule mod_sumset_int_mod_image_self[OF n_pos])
      finally show ?thesis .
    qed
    have sum_card:
      "card (sumset A A) =
        card C + card A + card (lower_sum_holes A \<inter> upper_sum_holes A)"
      using normalized_sumset_card_eq_mod_sumset_plus_card_inter_holes
        [OF fin n_pos subset zero top _ nonneg]
      by (simp add: n_def C_eq_mod)
    show False
    proof (cases "B \<subseteq> H")
      case True
      have B_subset_exact:
        "mod_image_int (Max A) A \<subseteq>
          Zmod.stabilizer (nat (Max A))
            (Zmod.sumset (nat (Max A))
              (mod_image_int (Max A) A) (mod_image_int (Max A) A))"
        using True by (simp add: n_def B_def p_def C_def H_def)
      show False
        by (rule normalized_mod_image_subset_stabilizer_contradicts_Gcd_one
            [OF fin card_ge zero nonneg gcd_one small_doubling stable_nonempty
             B_subset_exact])
    next
      case False
      have count:
        "card H \<le>
          1 + card (lower_sum_holes A \<inter> upper_sum_holes A) +
          2 * (card D - card B)"
        by (rule stabilizer_count[OF stable_nonempty False])
      have H_def': "H = Zmod.stabilizer p C"
        by (simp add: H_def)
      have D_def': "D = Zmod.sumset p B H"
        by (simp add: D_def)
      have kneser_raw:
        "2 * card (Zmod.sumset p B
            (Zmod.stabilizer p (Zmod.sumset p B B))) -
          card (Zmod.stabilizer p (Zmod.sumset p B B))
          \<le> card (Zmod.sumset p B B)"
        by (rule zmod_kneser_self[OF p_pos B_sub finB nonemptyB])
      have kneser:
        "2 * card D - card H \<le> card C"
        using kneser_raw by (simp add: C_def H_def D_def)
      have D_ge_B: "card B \<le> card D"
      proof -
        have B_subset_D: "B \<subseteq> D"
        proof
          fix b
          assume b_in: "b \<in> B"
          have b_carrier: "b \<in> {0..int (p - 1)}"
            using B_sub b_in p_pos by auto
          have "0 \<in> H"
            unfolding H_def by (rule Zmod.zero_mem_stabilizer)
          moreover have "0 \<in> {0..int (p - 1)}"
            using p_pos by auto
          ultimately have "(b + 0) mod int p \<in> Zmod.sumset p B H"
            by (rule Zmod.sumset.sumsetI[OF b_in b_carrier])
          then show "b \<in> D"
            using b_carrier p_pos by (simp add: D_def H_def)
        qed
        have finD: "finite D"
        proof -
          have "D \<subseteq> {0..int (p - 1)}"
            unfolding D_def by (rule Zmod.sumset_subset_carrier)
          then have "D \<subseteq> {0..int p - 1}"
            using p_pos by auto
          then show ?thesis
            by (rule finite_subset) simp
        qed
        show ?thesis
          by (rule card_mono[OF finD B_subset_D])
      qed
      have C_lower:
        "2 * card B - 1 - card (lower_sum_holes A \<inter> upper_sum_holes A)
          \<le> card C"
      proof -
        have "card H \<le>
            1 + card (lower_sum_holes A \<inter> upper_sum_holes A) +
            2 * card D - 2 * card B"
          using count D_ge_B by linarith
        with kneser D_ge_B show ?thesis
          by linarith
      qed
      have "3 * card A - 3 \<le> card (sumset A A)"
        using sum_card C_lower cardB card_ge by linarith
      with small_doubling card_ge show False
        by linarith
    qed
  qed
  show ?thesis
    by (rule normalized_progression_cover_from_no_stable_sum_holes
        [OF fin card_ge zero nonneg stable_empty])
qed

theorem normalized_progression_cover_from_gcd_one:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes zero: "0 \<in> A"
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> x"
  assumes gcd_one: "Gcd A = 1"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  define n where "n = Max A"
  define B where "B = mod_image_int n A"
  define p where "p = nat n"
  define C where "C = Zmod.sumset p B B"
  define H where "H = Zmod.stabilizer p C"
  define D where "D = Zmod.sumset p B H"
  have count:
    "card H \<le>
      1 + card (lower_sum_holes A \<inter> upper_sum_holes A) +
        2 * (card D - card B)"
    if stable_nonempty: "stable_sum_holes A \<noteq> {}" and not_subset: "\<not> B \<subseteq> H"
  proof -
    have not_subset_raw:
      "\<not> mod_image_int (Max A) A \<subseteq>
        Zmod.stabilizer (nat (Max A))
          (Zmod.sumset (nat (Max A))
            (mod_image_int (Max A) A) (mod_image_int (Max A) A))"
      using not_subset by (simp add: n_def B_def p_def C_def H_def)
    show ?thesis
      unfolding n_def B_def p_def C_def H_def D_def
      by (rule normalized_stabilizer_count[OF fin card_ge zero nonneg not_subset_raw])
  qed
  show ?thesis
  proof (rule normalized_progression_cover_from_stabilizer_count
      [OF fin card_ge zero nonneg gcd_one small_doubling])
    assume stable_nonempty: "stable_sum_holes A \<noteq> {}"
    assume not_subset_raw:
      "\<not> mod_image_int (Max A) A \<subseteq>
        Zmod.stabilizer (nat (Max A))
          (Zmod.sumset (nat (Max A))
            (mod_image_int (Max A) A) (mod_image_int (Max A) A))"
    show "card
        (Zmod.stabilizer (nat (Max A))
          (Zmod.sumset (nat (Max A))
            (mod_image_int (Max A) A) (mod_image_int (Max A) A)))
      \<le> 1 + card (lower_sum_holes A \<inter> upper_sum_holes A) +
        2 * (card
          (Zmod.sumset (nat (Max A)) (mod_image_int (Max A) A)
            (Zmod.stabilizer (nat (Max A))
              (Zmod.sumset (nat (Max A))
                (mod_image_int (Max A) A) (mod_image_int (Max A) A)))) -
          card (mod_image_int (Max A) A))"
      using count[OF stable_nonempty] not_subset_raw
      by (simp add: n_def B_def p_def C_def H_def D_def)
  qed
qed

theorem freiman_3k_minus_4_from_normalized_core:
  assumes core:
    "\<And>B. finite B \<Longrightarrow>
      3 \<le> card B \<Longrightarrow>
      0 \<in> B \<Longrightarrow>
      (\<And>x. x \<in> B \<Longrightarrow> 0 \<le> x) \<Longrightarrow>
      Gcd B = 1 \<Longrightarrow>
      card (sumset B B) \<le> 3 * card B - 4 \<Longrightarrow>
      progression_cover_length_at_most B (card (sumset B B) - card B + 1)"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof -
  let ?N = "normalized_int_set A"
  let ?g = "int_set_content A"
  have card_ge2: "2 \<le> card A"
    using card_ge by simp
  have nonempty: "A \<noteq> {}"
    using card_ge by auto
  have finN: "finite ?N"
    by (rule finite_normalized_int_set[OF fin])
  have cardN: "card ?N = card A"
    by (rule card_normalized_int_set[OF fin card_ge2])
  have sumN: "card (sumset ?N ?N) = card (sumset A A)"
    by (rule card_sumset_normalized_int_set[OF fin card_ge2])
  have cardN_ge: "3 \<le> card ?N"
    using card_ge cardN by simp
  have zeroN: "0 \<in> ?N"
    by (rule zero_in_normalized_int_set[OF fin nonempty])
  have nonnegN: "\<And>x. x \<in> ?N \<Longrightarrow> 0 \<le> x"
    by (rule normalized_int_set_nonneg[OF fin card_ge2])
  have gcdN: "Gcd ?N = 1"
    by (rule Gcd_normalized_int_set[OF fin card_ge2])
  have smallN: "card (sumset ?N ?N) \<le> 3 * card ?N - 4"
    using small_doubling cardN sumN by simp
  have coverN:
      "progression_cover_length_at_most ?N (card (sumset ?N ?N) - card ?N + 1)"
    by (rule core[OF finN cardN_ge zeroN nonnegN gcdN smallN])
  have g_pos: "0 < ?g"
    by (rule int_set_content_pos[OF fin card_ge2])
  have cover_image:
      "progression_cover_length_at_most
        (affine_image_int (Min A) ?g ?N)
        (card (sumset ?N ?N) - card ?N + 1)"
    by (rule progression_cover_affine_image_pos[OF coverN g_pos])
  have A_eq: "A = affine_image_int (Min A) ?g ?N"
    using normalized_int_set_reconstruction[OF fin card_ge2] by simp
  have length_eq:
      "card (sumset ?N ?N) - card ?N + 1 =
       card (sumset A A) - card A + 1"
    using cardN sumN by simp
  from cover_image A_eq have
      "progression_cover_length_at_most A (card (sumset ?N ?N) - card ?N + 1)"
    by metis
  with length_eq show ?thesis
    by metis
qed

subsection \<open>The target statement\<close>

text \<open>
  The AFP-facing statement combines the normalization lemmas above with the
  additive-combinatorial core proof: a finite integer set @{term A} with
  @{term "card (sumset A A) \<le> 3 * card A - 4"} and @{term "3 \<le> card A"}
  is contained in an arithmetic progression of length at most
  @{term "card (sumset A A) - card A + 1"}.
\<close>

theorem freiman_3k_minus_4:
  fixes A :: "int set"
  assumes fin: "finite A"
  assumes card_ge: "3 \<le> card A"
  assumes small_doubling: "card (sumset A A) \<le> 3 * card A - 4"
  shows "progression_cover_length_at_most A (card (sumset A A) - card A + 1)"
proof (rule freiman_3k_minus_4_from_normalized_core[OF _ fin card_ge small_doubling])
  fix B :: "int set"
  assume finB: "finite B"
  assume cardB_ge: "3 \<le> card B"
  assume zeroB: "0 \<in> B"
  assume nonnegB: "\<And>x. x \<in> B \<Longrightarrow> 0 \<le> x"
  assume gcdB: "Gcd B = 1"
  assume smallB: "card (sumset B B) \<le> 3 * card B - 4"
  show "progression_cover_length_at_most B (card (sumset B B) - card B + 1)"
    by (rule normalized_progression_cover_from_gcd_one
        [OF finB cardB_ge zeroB nonnegB gcdB smallB])
qed

end
