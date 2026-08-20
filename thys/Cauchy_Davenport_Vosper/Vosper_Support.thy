theory Vosper_Support
  imports Cauchy_Davenport_Prime_Field
begin

section \<open>Arithmetic progressions in prime fields\<close>

text \<open>
  Vosper's theorem is formulated in terms of arithmetic progressions with a
  shared common difference. This theory isolates the corresponding progression
  notation, translation lemmas, and the overlap criterion that recovers a
  progression from near-invariance under translation.
\<close>

subsection \<open>Basic progression infrastructure\<close>

definition ap_segment :: "'a::semiring_1 \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set" where
  "ap_segment a d n = (\<lambda>i. a + of_nat i * d) ` {..<n}"

definition arithmetic_progression :: "'a::semiring_1 set \<Rightarrow> bool" where
  "arithmetic_progression A \<longleftrightarrow> (\<exists>a d n. A = ap_segment a d n)"

lemma arithmetic_progressionI:
  "A = ap_segment a d n \<Longrightarrow> arithmetic_progression A"
  unfolding arithmetic_progression_def by blast

lemma arithmetic_progressionE:
  assumes "arithmetic_progression A"
  obtains a d n where "A = ap_segment a d n"
  using assms by (auto simp: arithmetic_progression_def)

lemma finite_ap_segment [simp]:
  "finite (ap_segment a d n)"
  by (simp add: ap_segment_def)

lemma ap_segment_empty [simp]:
  "ap_segment a d 0 = {}"
  by (simp add: ap_segment_def)

lemma ap_segment_zero_step:
  fixes a :: "'a::semiring_1"
  assumes "0 < n"
  shows "ap_segment a 0 n = {a}"
proof
  show "ap_segment a 0 n \<subseteq> {a}"
    by (auto simp: ap_segment_def)
next
  have "a + of_nat 0 * 0 \<in> ap_segment a 0 n"
    using assms by (auto simp: ap_segment_def)
  then show "{a} \<subseteq> ap_segment a 0 n"
    by simp
qed

lemma ap_segment_translate:
  fixes a d c :: "'a::semiring_1"
  shows "translate c (ap_segment a d n) = ap_segment (c + a) d n"
proof
  show "translate c (ap_segment a d n) \<subseteq> ap_segment (c + a) d n"
    by (auto simp: translate_def ap_segment_def ac_simps)
next
  show "ap_segment (c + a) d n \<subseteq> translate c (ap_segment a d n)"
  proof
    fix x
    assume "x \<in> ap_segment (c + a) d n"
    then obtain i where i_lt: "i < n" and x: "x = (c + a) + of_nat i * d"
      by (auto simp: ap_segment_def)
    have "a + of_nat i * d \<in> ap_segment a d n"
      using i_lt by (auto simp: ap_segment_def)
    moreover have "x = c + (a + of_nat i * d)"
      using x by (simp add: ac_simps)
    ultimately show "x \<in> translate c (ap_segment a d n)"
      by (auto simp: translate_def)
  qed
qed

lemma arithmetic_progression_translate [simp]:
  fixes c :: "'a::ring_1"
  shows "arithmetic_progression (translate c A) \<longleftrightarrow> arithmetic_progression A"
proof
  assume "arithmetic_progression (translate c A)"
  then obtain a d n where eq: "translate c A = ap_segment a d n"
    unfolding arithmetic_progression_def by blast
  have "A = translate (- c) (translate c A)"
  proof
    show "A \<subseteq> translate (- c) (translate c A)"
    proof
      fix x
      assume "x \<in> A"
      then have cx_in: "c + x \<in> translate c A"
        by (auto simp: translate_def)
      have x_eq: "x = - c + (c + x)"
        by simp
      show "x \<in> translate (- c) (translate c A)"
      proof (unfold translate_def, rule image_eqI[where x = "c + x"])
        show "c + x \<in> (+) c ` A"
          using cx_in unfolding translate_def by simp
        show "x = - c + (c + x)"
          using x_eq by simp
      qed
    qed
  next
    show "translate (- c) (translate c A) \<subseteq> A"
    proof
      fix x
      assume "x \<in> translate (- c) (translate c A)"
      then obtain y where y_in: "y \<in> translate c A" and x: "x = - c + y"
        by (auto simp: translate_def)
      then obtain z where z_in: "z \<in> A" and y: "y = c + z"
        by (auto simp: translate_def)
      from x y have "x = z"
        by simp
      with z_in show "x \<in> A"
        by simp
    qed
  qed
  also have "\<dots> = ap_segment ((- c) + a) d n"
    using eq by (simp add: ap_segment_translate)
  finally show "arithmetic_progression A"
    unfolding arithmetic_progression_def by blast
next
  assume "arithmetic_progression A"
  then obtain a d n where "A = ap_segment a d n"
    unfolding arithmetic_progression_def by blast
  then show "arithmetic_progression (translate c A)"
    unfolding arithmetic_progression_def
    by (intro exI[of _ "c + a"] exI[of _ d] exI[of _ n]) (simp add: ap_segment_translate)
qed

lemma sumset_ap_segment_pair_suc:
  fixes a d :: "'a::semiring_1"
  shows "sumset (ap_segment a d (Suc n)) {0, d} = ap_segment a d (Suc (Suc n))"
proof
  show "sumset (ap_segment a d (Suc n)) {0, d} \<subseteq> ap_segment a d (Suc (Suc n))"
  proof
    fix x
    assume "x \<in> sumset (ap_segment a d (Suc n)) {0, d}"
    then obtain y b where
        y_in: "y \<in> ap_segment a d (Suc n)"
      and b_in: "b \<in> {0, d}"
      and x_eq: "x = y + b"
      by (rule sumsetE)
    from y_in obtain i where i_lt: "i < Suc n" and y_eq: "y = a + of_nat i * d"
      by (auto simp: ap_segment_def)
    show "x \<in> ap_segment a d (Suc (Suc n))"
    proof (cases "b = 0")
      case True
      have "i < Suc (Suc n)"
        using i_lt by simp
      with True x_eq y_eq show ?thesis
        by (auto simp: ap_segment_def)
    next
      case False
      with b_in have "b = d"
        by simp
      with x_eq y_eq have "x = a + of_nat (Suc i) * d"
        by (simp add: algebra_simps)
      moreover have "Suc i < Suc (Suc n)"
        using i_lt by simp
      ultimately show ?thesis
      proof -
        have "a + of_nat (Suc i) * d \<in> ap_segment a d (Suc (Suc n))"
        proof (unfold ap_segment_def, rule image_eqI[where x = "Suc i"])
          show "Suc i \<in> {..<Suc (Suc n)}"
            using i_lt by simp
          show "a + of_nat (Suc i) * d = a + of_nat (Suc i) * d"
            by simp
        qed
        then show ?thesis
          using \<open>x = a + of_nat (Suc i) * d\<close> by simp
      qed
    qed
  qed
next
  show "ap_segment a d (Suc (Suc n)) \<subseteq> sumset (ap_segment a d (Suc n)) {0, d}"
  proof
    fix x
    assume "x \<in> ap_segment a d (Suc (Suc n))"
    then obtain j where j_lt: "j < Suc (Suc n)" and x_eq: "x = a + of_nat j * d"
      by (auto simp: ap_segment_def)
    show "x \<in> sumset (ap_segment a d (Suc n)) {0, d}"
    proof (cases "j < Suc n")
      case True
      have "a + of_nat j * d \<in> ap_segment a d (Suc n)"
        using True by (auto simp: ap_segment_def)
      then have "(a + of_nat j * d) + 0 \<in> sumset (ap_segment a d (Suc n)) {0, d}"
        by (rule sumsetI) simp_all
      then show ?thesis
        using x_eq by simp
    next
      case False
      with j_lt have j_eq: "j = Suc n"
        by simp
      have "a + of_nat n * d \<in> ap_segment a d (Suc n)"
        by (auto simp: ap_segment_def)
      moreover have "x = (a + of_nat n * d) + d"
        using x_eq j_eq by (simp add: algebra_simps)
      ultimately show ?thesis
      proof -
        have "(a + of_nat n * d) + d \<in> sumset (ap_segment a d (Suc n)) {0, d}"
          using \<open>a + of_nat n * d \<in> ap_segment a d (Suc n)\<close>
          by (rule sumsetI) simp_all
        then show ?thesis
          using \<open>x = (a + of_nat n * d) + d\<close> by simp
      qed
    qed
  qed
qed

lemma of_nat_eq_below_prime_card:
  fixes i j :: nat
  assumes prime_card: "prime (card (UNIV :: 'a::finite_field set))"
  assumes i_lt: "i < card (UNIV :: 'a set)"
  assumes j_lt: "j < card (UNIV :: 'a set)"
  assumes eq: "(of_nat i :: 'a) = of_nat j"
  shows "i = j"
proof (cases i j rule: linorder_cases)
  case less
  have "CHAR('a) dvd (j - i)"
    using eq less by (simp add: of_nat_eq_iff_char_dvd)
  then have card_dvd: "card (UNIV :: 'a set) dvd (j - i)"
    by (simp add: prime_card_eq_char[OF prime_card])
  have "j - i > 0"
    using less by simp
  then have "card (UNIV :: 'a set) \<le> j - i"
    using card_dvd prime_card by (meson dvd_imp_le prime_gt_0_nat)
  moreover have "j - i < card (UNIV :: 'a set)"
    using i_lt j_lt less by simp
  ultimately show ?thesis
    by simp
next
  case greater
  have "CHAR('a) dvd (i - j)"
  proof -
    have "(of_nat j :: 'a) = of_nat i"
      using eq by simp
    with greater show ?thesis
      by (simp add: of_nat_eq_iff_char_dvd)
  qed
  then have card_dvd: "card (UNIV :: 'a set) dvd (i - j)"
    by (simp add: prime_card_eq_char[OF prime_card])
  have "i - j > 0"
    using greater by simp
  then have "card (UNIV :: 'a set) \<le> i - j"
    using card_dvd prime_card by (meson dvd_imp_le prime_gt_0_nat)
  moreover have "i - j < card (UNIV :: 'a set)"
    using i_lt j_lt greater by simp
  ultimately show ?thesis
    by simp
qed simp

lemma inj_on_ap_segment_index:
  fixes a d :: "'a::finite_field"
  assumes prime_card: "prime (card (UNIV :: 'a::finite_field set))"
  assumes d_nonzero: "d \<noteq> 0"
  assumes n_le: "n \<le> card (UNIV :: 'a set)"
  shows "inj_on (\<lambda>i. a + of_nat i * d) {..<n}"
proof (rule inj_onI)
  fix i j
  assume i_in: "i \<in> {..<n}"
  assume j_in: "j \<in> {..<n}"
  assume eq: "a + of_nat i * d = a + of_nat j * d"
  have "(of_nat i :: 'a) = of_nat j"
  proof -
    have "((of_nat i :: 'a) - of_nat j) * d = 0"
      using eq by (simp add: algebra_simps)
    with d_nonzero have "(of_nat i :: 'a) - of_nat j = 0"
      by auto
    then show ?thesis
      by simp
  qed
  then show "i = j"
    using i_in j_in n_le prime_card by (intro of_nat_eq_below_prime_card) auto
qed

lemma card_ap_segment:
  fixes a d :: "'a::finite_field"
  assumes prime_card: "prime (card (UNIV :: 'a::finite_field set))"
  assumes d_nonzero: "d \<noteq> 0"
  assumes n_le: "n \<le> card (UNIV :: 'a set)"
  shows "card (ap_segment a d n) = n"
  by (simp add: ap_segment_def card_image inj_on_ap_segment_index[OF prime_card d_nonzero n_le])

lemma arithmetic_progression_obtain_card:
  fixes A :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes ap: "arithmetic_progression A"
  assumes card_ge2: "2 \<le> card A"
  assumes small: "card A < card (UNIV :: 'a set)"
  obtains a d where "d \<noteq> 0" "A = ap_segment a d (card A)"
proof -
  obtain a d n where A_eq: "A = ap_segment a d n"
    using ap by (rule arithmetic_progressionE)
  have n_pos: "0 < n"
  proof (rule ccontr)
    assume "\<not> 0 < n"
    then have "n = 0"
      by simp
    with A_eq card_ge2 show False
      by simp
  qed
  have d_nonzero: "d \<noteq> 0"
  proof
    assume "d = 0"
    with A_eq n_pos have "A = {a}"
      by (simp add: ap_segment_zero_step)
    with card_ge2 show False
      by simp
  qed
  let ?p = "card (UNIV :: 'a set)"
  have n_lt_p: "n < ?p"
  proof (rule ccontr)
    assume "\<not> n < ?p"
    then have p_le_n: "?p \<le> n"
      by simp
    have "ap_segment a d ?p \<subseteq> ap_segment a d n"
      using p_le_n by (auto simp: ap_segment_def)
    moreover have "ap_segment a d ?p = UNIV"
    proof -
      have "card (ap_segment a d ?p) = ?p"
        by (rule card_ap_segment[OF prime_card d_nonzero]) simp
      moreover have "ap_segment a d ?p \<subseteq> UNIV"
        by simp
      ultimately show ?thesis
        using finite_UNIV by (intro card_subset_eq) auto
    qed
    ultimately have "UNIV \<subseteq> A"
      using A_eq by simp
    then have "A = UNIV"
      by auto
    with small show False
      by simp
  qed
  have n_le_p: "n \<le> ?p"
    using n_lt_p by simp
  have "card A = n"
    using A_eq card_ap_segment[OF prime_card d_nonzero n_le_p, of a] by simp
  then have "A = ap_segment a d (card A)"
    using A_eq by simp
  then show ?thesis
    using d_nonzero that by blast
qed

lemma step_image_UNIV:
  fixes a d :: "'a::finite_field"
  assumes prime_card: "prime (card (UNIV :: 'a::finite_field set))"
  assumes d_nonzero: "d \<noteq> 0"
  shows "(\<lambda>i. a + of_nat i * d) ` {..<card (UNIV :: 'a set)} = UNIV"
proof -
  have inj: "inj_on (\<lambda>i. a + of_nat i * d) {..<card (UNIV :: 'a set)}"
    by (rule inj_on_ap_segment_index[OF prime_card d_nonzero]) simp
  have "card ((\<lambda>i. a + of_nat i * d) ` {..<card (UNIV :: 'a set)}) = card (UNIV :: 'a set)"
    by (simp add: card_image inj)
  moreover have "(\<lambda>i. a + of_nat i * d) ` {..<card (UNIV :: 'a set)} \<subseteq> UNIV"
    by simp
  ultimately show ?thesis
    using finite_UNIV by (intro card_subset_eq) auto
qed

lemma predecessor_closed_initial_segment:
  fixes S :: "nat set"
  assumes fin: "finite S"
  assumes zero: "0 \<in> S"
  assumes pred: "\<And>k. Suc k \<in> S \<Longrightarrow> k \<in> S"
  shows "S = {..<card S}"
proof
  have init: "{..<Suc k} \<subseteq> S" if "k \<in> S" for k
    using that
  proof (induction k)
    case 0
    then show ?case
      by auto
  next
    case (Suc k)
    have "k \<in> S"
      using pred Suc.prems by blast
    then have "{..<Suc k} \<subseteq> S"
      by (rule Suc.IH)
    show ?case
    proof
      fix x
      assume x_lt: "x \<in> {..<Suc (Suc k)}"
      show "x \<in> S"
      proof (cases "x = Suc k")
        case True
        with Suc.prems show ?thesis
          by simp
      next
        case False
        with x_lt have "x < Suc k"
          by simp
        with \<open>{..<Suc k} \<subseteq> S\<close> show ?thesis
          by auto
      qed
    qed
  qed
  show "S \<subseteq> {..<card S}"
  proof
    fix k
    assume "k \<in> S"
    then have "{..<Suc k} \<subseteq> S"
      by (rule init)
    then have "Suc k \<le> card S"
    proof -
      have "card {..<Suc k} = Suc k"
        by simp
      moreover have "card {..<Suc k} \<le> card S"
        using fin \<open>{..<Suc k} \<subseteq> S\<close> by (intro card_mono) auto
      ultimately show ?thesis
        by simp
    qed
    then show "k \<in> {..<card S}"
      by simp
  qed
next
  show "{..<card S} \<subseteq> S"
  proof
    have down: "i \<in> S" if "i \<le> j" "j \<in> S" for i j
      using that
    proof (induction j arbitrary: i)
      case 0
      then show ?case
        by simp
    next
      case (Suc j)
      show ?case
      proof (cases "i = Suc j")
        case True
        with Suc.prems show ?thesis
          by simp
      next
        case False
        with Suc.prems have i_le_j: "i \<le> j"
          by simp
        have "j \<in> S"
          using pred Suc.prems(2) by simp
        from Suc.IH[OF i_le_j this] show ?thesis .
      qed
    qed
    fix k
    assume k_lt: "k \<in> {..<card S}"
    show "k \<in> S"
    proof (rule ccontr)
      assume k_notin: "k \<notin> S"
      have "S \<subseteq> {..<k}"
      proof
        fix j
        assume j_in: "j \<in> S"
        show "j \<in> {..<k}"
        proof (rule ccontr)
          assume "j \<notin> {..<k}"
          then have "k \<le> j"
            by simp
          then have "k \<in> S"
            using j_in by (rule down)
          with k_notin show False
            by simp
        qed
      qed
      then have "card S \<le> k"
      proof -
        have "card S \<le> card {..<k}"
          using fin \<open>S \<subseteq> {..<k}\<close> by (intro card_mono) auto
        then show ?thesis
          by simp
      qed
      with k_lt show False
        by simp
    qed
  qed
qed

subsection \<open>Recovering a progression from maximal overlap\<close>

text \<open>
  The following lemmas package the structural step used repeatedly in the
  Vosper proof: if a set is almost preserved by translation with a nonzero step,
  then it must itself be an arithmetic progression with that step.
\<close>

lemma ap_segment_from_maximal_shift_overlap:
  fixes A :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes d_nonzero: "d \<noteq> 0"
  assumes small: "card A < card (UNIV :: 'a set)"
  assumes overlap: "card (A \<inter> translate d A) = card A - 1"
  obtains a where "A = ap_segment a d (card A)"
proof (cases "A = {}")
  case True
  then show ?thesis
  proof -
    have "A = ap_segment 0 d (card A)"
      using True by simp
    then show ?thesis
      by (rule that)
  qed
next
  case False
  have finA: "finite A"
    using finite_subset[of A "UNIV :: 'a set"] by simp
  have cardA_pos: "0 < card A"
    using False finA by auto
  have one_start: "card (A - translate d A) = 1"
  proof -
    have "A \<inter> translate d A \<subseteq> A"
      by simp
    then have "card (A - (A \<inter> translate d A)) = card A - card (A \<inter> translate d A)"
      using finA by (simp add: card_Diff_subset)
    moreover have "A - (A \<inter> translate d A) = A - translate d A"
      by auto
    ultimately show ?thesis
      using overlap cardA_pos by simp
  qed
  then obtain a where a_start: "A - translate d A = {a}"
    by (meson card_1_singletonE)
  then have a_in: "a \<in> A" and a_notin: "a \<notin> translate d A"
    by auto
  define p where "p = card (UNIV :: 'a set)"
  define f where "f i = a + of_nat i * d" for i
  define S where "S = {i \<in> {..<p}. f i \<in> A}"
  have p_pos: "0 < p"
    unfolding p_def using prime_card prime_gt_0_nat by blast
  have image_all: "f ` {..<p} = UNIV"
    unfolding p_def f_def by (rule step_image_UNIV[OF prime_card d_nonzero])
  have A_as_image: "A = f ` S"
    unfolding S_def
    using image_all by (auto simp: f_def)
  have inj_f: "inj_on f {..<p}"
    unfolding p_def f_def
    by (rule inj_on_ap_segment_index[OF prime_card d_nonzero]) simp
  have finS: "finite S"
    unfolding S_def by simp
  have cardS: "card S = card A"
  proof -
    have S_subset: "S \<subseteq> {..<p}"
      unfolding S_def by auto
    have inj_fS: "inj_on f S"
      using inj_f S_subset by (rule inj_on_subset)
    have "card (f ` S) = card S"
      using finS inj_fS by (simp add: card_image)
    with A_as_image show ?thesis
      by simp
  qed
  have zero_in_S: "0 \<in> S"
    using a_in p_pos by (simp add: S_def f_def)
  have pred_closed: "Suc k \<in> S \<Longrightarrow> k \<in> S" for k
  proof -
    assume suc_in: "Suc k \<in> S"
    then have sk_lt: "Suc k < p"
      by (simp add: S_def)
    have fk_in: "f (Suc k) \<in> A"
      using suc_in by (simp add: S_def)
    have fk_neq_a: "f (Suc k) \<noteq> a"
    proof
      assume "f (Suc k) = a"
      then have "f (Suc k) = f 0"
        by (simp add: f_def)
      have suc_mem: "Suc k \<in> {..<p}"
        using sk_lt by simp
      have zero_mem: "0 \<in> {..<p}"
        using p_pos by simp
      from inj_f suc_mem zero_mem \<open>f (Suc k) = f 0\<close> have "Suc k = 0"
        unfolding inj_on_def by blast
      then show False
        by simp
    qed
    have "f (Suc k) \<in> A - translate d A \<Longrightarrow> False"
      using a_start fk_neq_a by auto
    then have fk_shift: "f (Suc k) \<in> translate d A"
      using fk_in by blast
    then obtain y where y_in: "y \<in> A" and fy: "f (Suc k) = d + y"
      by (auto simp: translate_iff)
    have "y = f k"
      using fy by (simp add: f_def algebra_simps)
    with y_in show "k \<in> S"
      using sk_lt by (simp add: S_def)
  qed
  have S_init: "S = {..<card S}"
    by (rule predecessor_closed_initial_segment[OF finS zero_in_S pred_closed])
  have "A = f ` {..<card A}"
    using A_as_image S_init cardS by simp
  also have "\<dots> = ap_segment a d (card A)"
    by (simp add: ap_segment_def f_def)
  finally have "A = ap_segment a d (card A)" .
  then show ?thesis
    using that by blast
qed

lemma arithmetic_progression_from_maximal_shift_overlap:
  fixes A :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes d_nonzero: "d \<noteq> 0"
  assumes small: "card A < card (UNIV :: 'a set)"
  assumes overlap: "card (A \<inter> translate d A) = card A - 1"
  shows "arithmetic_progression A"
proof -
  obtain a where "A = ap_segment a d (card A)"
    by (rule ap_segment_from_maximal_shift_overlap[OF prime_card d_nonzero small overlap])
  then show ?thesis
    unfolding arithmetic_progression_def by blast
qed

end
