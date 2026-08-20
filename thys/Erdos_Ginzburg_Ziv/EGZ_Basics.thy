theory EGZ_Basics
  imports
    Main
    "HOL-Library.Multiset"
    "HOL-Number_Theory.Cong"
    "HOL-Computational_Algebra.Primes"
begin

section \<open>Residue and subset-sum infrastructure\<close>

text \<open>
  This theory isolates the finite combinatorial infrastructure used in the prime
  case. We work with a recursive set of subset sums modulo @{term p}, together
  with modular translations on the residue set @{term "residues p"}. The key
  output is that a list of @{text "p - 1"} nonzero residues modulo a prime
  already generates every residue class by subset summation.
\<close>

subsection \<open>Residues and modular translations\<close>

definition residues :: "nat \<Rightarrow> int set" where
  "residues p = {0..<int p}"

definition mod_translate :: "nat \<Rightarrow> int \<Rightarrow> int set \<Rightarrow> int set" where
  "mod_translate p d A = ((\<lambda>x. (x + d) mod int p) ` A)"

definition list_index_sum :: "int list \<Rightarrow> nat set \<Rightarrow> int" where
  "list_index_sum xs I = (\<Sum>i\<in>I. xs ! i)"

fun mod_subset_sums :: "nat \<Rightarrow> int list \<Rightarrow> int set" where
  "mod_subset_sums p [] = {0}"
| "mod_subset_sums p (d # ds) = mod_subset_sums p ds \<union> mod_translate p d (mod_subset_sums p ds)"

lemma residues_finite [simp]:
  "finite (residues p)"
  by (simp add: residues_def)

lemma card_residues [simp]:
  assumes "0 < p"
  shows "card (residues p) = p"
  using assms by (simp add: residues_def)

lemma mod_translate_iff:
  "x \<in> mod_translate p d A \<longleftrightarrow> (\<exists>a\<in>A. x = (a + d) mod int p)"
  by (auto simp: mod_translate_def)

lemma mod_translate_subset_residues:
  assumes "0 < p"
  assumes "A \<subseteq> residues p"
  shows "mod_translate p d A \<subseteq> residues p"
  using assms by (auto simp: mod_translate_def residues_def)

lemma mod_translate_inj_on_residues:
  assumes "0 < p"
  shows "inj_on (\<lambda>x. (x + d) mod int p) (residues p)"
proof (rule inj_onI)
  fix x y
  assume x_in: "x \<in> residues p"
  assume y_in: "y \<in> residues p"
  assume eq: "(x + d) mod int p = (y + d) mod int p"

  have cong_xyc: "[x + d = y + d] (mod int p)"
    using eq by (simp add: cong_def)
  then have cong_xy: "[x = y] (mod int p)"
    by (simp add: cong_add_rcancel)

  from x_in have x_bounds: "0 \<le> x" "x < int p"
    by (auto simp: residues_def)
  from y_in have y_bounds: "0 \<le> y" "y < int p"
    by (auto simp: residues_def)

  show "x = y"
    by (rule cong_less_imp_eq_int[OF x_bounds y_bounds cong_xy])
qed

lemma card_mod_translate_eq:
  assumes "0 < p"
  assumes "A \<subseteq> residues p"
  shows "card (mod_translate p d A) = card A"
proof -
  have finite_A: "finite A"
    using assms by (meson finite_subset residues_finite)
  have inj_residues: "inj_on (\<lambda>x. (x + d) mod int p) (residues p)"
    by (rule mod_translate_inj_on_residues[OF assms(1)])
  have inj_A: "inj_on (\<lambda>x. (x + d) mod int p) A"
    by (rule inj_on_subset[OF inj_residues assms(2)])
  show ?thesis
    unfolding mod_translate_def
    by (simp add: card_image finite_A inj_A)
qed

lemma mod_translate_compose:
  assumes "0 < p"
  shows "mod_translate p c (mod_translate p d A) = mod_translate p (c + d) A"
proof
  show "mod_translate p c (mod_translate p d A) \<subseteq> mod_translate p (c + d) A"
  proof
    fix x
    assume "x \<in> mod_translate p c (mod_translate p d A)"
    then obtain y a where aA: "a \<in> A" and y_eq: "y = (a + d) mod int p"
      and x_eq: "x = (y + c) mod int p"
      by (auto simp: mod_translate_iff)
    have "x = (a + (c + d)) mod int p"
      using assms x_eq y_eq by (simp add: algebra_simps mod_simps)
    then show "x \<in> mod_translate p (c + d) A"
      using aA by (force simp: mod_translate_iff)
  qed
next
  show "mod_translate p (c + d) A \<subseteq> mod_translate p c (mod_translate p d A)"
  proof
    fix x
    assume "x \<in> mod_translate p (c + d) A"
    then obtain a where aA: "a \<in> A" and x_eq: "x = (a + (c + d)) mod int p"
      by (auto simp: mod_translate_iff)
    let ?y = "(a + d) mod int p"
    have "?y \<in> mod_translate p d A"
      using aA by (auto simp: mod_translate_iff)
    moreover have "x = (?y + c) mod int p"
      using assms x_eq by (simp add: algebra_simps mod_simps)
    ultimately show "x \<in> mod_translate p c (mod_translate p d A)"
      by (force simp: mod_translate_iff)
  qed
qed

lemma mod_subset_sums_contains_zero [simp]:
  "0 \<in> mod_subset_sums p ds"
  by (induction ds) auto

lemma mod_subset_sums_nonempty [simp]:
  "mod_subset_sums p ds \<noteq> {}"
  using mod_subset_sums_contains_zero by blast

lemma mod_subset_sums_subset_residues:
  assumes "0 < p"
  shows "mod_subset_sums p ds \<subseteq> residues p"
proof (induction ds)
  case Nil
  then show ?case
    using assms by (auto simp: residues_def)
next
  case (Cons d ds)
  then show ?case
    using mod_translate_subset_residues[OF assms Cons.IH]
    by auto
qed

lemma mod_mult_inj_on_residues:
  assumes prime_p: "prime p"
  assumes d_nz: "d mod int p \<noteq> 0"
  shows "inj_on (\<lambda>x. (x * d) mod int p) (residues p)"
proof (rule inj_onI)
  fix x y
  assume x_in: "x \<in> residues p"
  assume y_in: "y \<in> residues p"
  assume eq: "(x * d) mod int p = (y * d) mod int p"

  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  have p_not_dvd_d: "\<not> int p dvd d"
    using d_nz by (simp add: dvd_eq_mod_eq_0)
  have cop_d: "coprime d (int p)"
    using prime_imp_coprime_int[of "int p" d] p_not_dvd_d prime_p
    by (simp add: coprime_commute)
  have cong_xyd: "[x * d = y * d] (mod int p)"
    using eq by (simp add: cong_def)
  then have cong_xy: "[x = y] (mod int p)"
    using cop_d by (simp add: cong_mult_rcancel)

  from x_in have x_bounds: "0 \<le> x" "x < int p"
    by (auto simp: residues_def)
  from y_in have y_bounds: "0 \<le> y" "y < int p"
    by (auto simp: residues_def)
  show "x = y"
    by (rule cong_less_imp_eq_int[OF x_bounds y_bounds cong_xy])
qed

lemma image_mult_residues:
  assumes prime_p: "prime p"
  assumes d_nz: "d mod int p \<noteq> 0"
  shows "((\<lambda>x. (x * d) mod int p) ` residues p) = residues p"
proof -
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  have subset_res: "(\<lambda>x. (x * d) mod int p) ` residues p \<subseteq> residues p"
    using p_pos by (auto simp: residues_def)
  have inj: "inj_on (\<lambda>x. (x * d) mod int p) (residues p)"
    by (rule mod_mult_inj_on_residues[OF assms])
  have "card (((\<lambda>x. (x * d) mod int p) ` residues p)) = p"
    using p_pos inj by (simp add: card_image)
  moreover have "card (residues p) = p"
    using p_pos by simp
  ultimately show ?thesis
    using subset_res by (intro card_subset_eq) auto
qed

lemma mod_translate_eq_self_imp_full:
  assumes prime_p: "prime p"
  assumes A_sub: "A \<subseteq> residues p"
  assumes A_nonempty: "A \<noteq> {}"
  assumes A_fix: "mod_translate p d A = A"
  assumes d_nz: "d mod int p \<noteq> 0"
  shows "A = residues p"
proof
  show "A \<subseteq> residues p"
    using A_sub .
next
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  from A_nonempty obtain a where aA: "a \<in> A"
    by auto

  have step_closed: "((a + int n * d) mod int p) \<in> A" for n :: nat
  proof (induction n)
    case 0
    then show ?case
      using aA A_sub by (auto simp: residues_def)
  next
    case (Suc n)
    have prev: "((a + int n * d) mod int p) \<in> A"
      by (rule Suc.IH)
    then have "(((a + int n * d) mod int p) + d) mod int p \<in> mod_translate p d A"
      by (auto simp: mod_translate_iff)
    then show ?case
      using A_fix by (simp add: algebra_simps mod_simps)
  qed

  show "residues p \<subseteq> A"
  proof
    fix x
    assume x_in: "x \<in> residues p"
    define b where "b = (x - a) mod int p"
    have b_in: "b \<in> residues p"
      using p_pos by (auto simp: b_def residues_def)
    from image_mult_residues[OF prime_p d_nz]
    have "b \<in> (\<lambda>t. (t * d) mod int p) ` residues p"
      using b_in by simp
    then obtain t where t_in: "t \<in> residues p" and b_eq: "b = (t * d) mod int p"
      by auto
    from t_in have t_bounds: "0 \<le> t" "t < int p"
      by (auto simp: residues_def)
    define n where "n = nat t"
    have t_eq: "t = int n"
      using t_bounds by (simp add: n_def)
    have "(a + int n * d) mod int p \<in> A"
      by (rule step_closed)
    moreover have "(a + int n * d) mod int p = x"
    proof -
      have lhs: "((x - a) mod int p + a) mod int p = x"
        using x_in by (simp add: residues_def mod_simps)
      have "((x - a) mod int p + a) mod int p = ((int n * d) mod int p + a) mod int p"
        using b_eq by (simp add: b_def t_eq)
      with lhs have "x = ((int n * d) mod int p + a) mod int p"
        by simp
      also have "\<dots> = (a + int n * d) mod int p"
        by (simp add: algebra_simps mod_simps)
      finally show ?thesis
        by simp
    qed
    ultimately show "x \<in> A"
      by simp
  qed
qed

lemma mod_translate_proper_union_grows:
  assumes prime_p: "prime p"
  assumes A_sub: "A \<subseteq> residues p"
  assumes A_nonempty: "A \<noteq> {}"
  assumes A_proper: "A \<noteq> residues p"
  assumes d_nz: "d mod int p \<noteq> 0"
  shows "card (A \<union> mod_translate p d A) > card A"
proof -
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  have fin_A: "finite A"
    using A_sub by (rule finite_subset) auto
  have trans_subset: "mod_translate p d A \<subseteq> residues p"
    by (rule mod_translate_subset_residues[OF p_pos A_sub])
  have trans_card: "card (mod_translate p d A) = card A"
    by (rule card_mod_translate_eq[OF p_pos A_sub])
  have trans_not_eq: "mod_translate p d A \<noteq> A"
  proof
    assume fix_eq: "mod_translate p d A = A"
    then have "A = residues p"
      by (rule mod_translate_eq_self_imp_full[OF prime_p A_sub A_nonempty _ d_nz])
    with A_proper show False
      by contradiction
  qed
  have trans_not_sub: "\<not> mod_translate p d A \<subseteq> A"
  proof
    assume trans_sub_A: "mod_translate p d A \<subseteq> A"
    have "card (mod_translate p d A) \<le> card A"
      using fin_A trans_sub_A by (rule card_mono)
    with trans_card have "card (mod_translate p d A) = card A"
      by simp
    have trans_eq: "mod_translate p d A = A"
      by (simp add: card_subset_eq fin_A trans_card trans_sub_A)
    from trans_eq trans_not_eq show False
      by contradiction
  qed
  then obtain x where x_in: "x \<in> mod_translate p d A" and x_notin: "x \<notin> A"
    by auto
  have psub: "A < A \<union> mod_translate p d A"
    using x_in x_notin by auto
  have fin_union: "finite (A \<union> mod_translate p d A)"
  proof (rule finite_UnI)
    show "finite A"
      using fin_A .
    show "finite (mod_translate p d A)"
      by (rule finite_subset[OF trans_subset]) auto
  qed
  show ?thesis
    by (rule psubset_card_mono[OF fin_union psub])
qed

subsection \<open>Growth of subset sums\<close>

lemma card_mod_subset_sums_lower_bound:
  assumes prime_p: "prime p"
  assumes nonzero: "\<forall>d\<in>set ds. d mod int p \<noteq> 0"
  shows "card (mod_subset_sums p ds) \<ge> min p (Suc (length ds))"
proof -
  have aux: "(\<forall>d\<in>set xs. d mod int p \<noteq> 0) \<Longrightarrow> card (mod_subset_sums p xs) \<ge> min p (Suc (length xs))" for xs
  proof (induction xs)
    case Nil
    then show ?case
      using prime_gt_0_nat[OF prime_p] by simp
  next
    case (Cons e ds)
    let ?A = "mod_subset_sums p ds"
    let ?B = "mod_subset_sums p (e # ds)"
    have p_pos: "0 < p"
      using prime_gt_0_nat[OF prime_p] .
    have nz_cons: "\<forall>d\<in>set (e # ds). d mod int p \<noteq> 0"
      by (rule Cons.prems)
    have head_nz: "e mod int p \<noteq> 0"
      using nz_cons by simp
    have rest_nz: "\<forall>d\<in>set ds. d mod int p \<noteq> 0"
      using nz_cons by simp
    have ih: "card ?A \<ge> min p (Suc (length ds))"
      by (rule Cons.IH[OF rest_nz])
    have A_sub: "?A \<subseteq> residues p"
      by (rule mod_subset_sums_subset_residues[OF p_pos])
    have B_sub: "?B \<subseteq> residues p"
      by (rule mod_subset_sums_subset_residues[OF p_pos])
    have finite_residues: "finite (residues p)"
      by simp
    have finite_B: "finite ?B"
      by (rule finite_subset[OF B_sub]) auto
    have card_A_le: "card ?A \<le> p"
      by (metis A_sub card_mono card_residues finite_residues p_pos)
    have card_B_le: "card ?B \<le> p"
      by (metis B_sub card_mono card_residues finite_residues p_pos)
    show ?case
    proof (cases "card ?A = p")
      case True
      have A_sub_B: "?A \<subseteq> ?B"
        by auto
      have "card ?A \<le> card ?B"
        by (rule card_mono[OF finite_B A_sub_B])
      then have card_B_ge: "p \<le> card ?B"
        using True by simp
      from card_B_ge card_B_le have "card ?B = p"
        by simp
      then show ?thesis
        by simp
    next
      case False
      then have card_A_lt: "card ?A < p"
        using card_A_le by simp
      have A_proper: "?A \<noteq> residues p"
        using False p_pos by force
      have grow: "card (?A \<union> mod_translate p e ?A) > card ?A"
        by (rule mod_translate_proper_union_grows[OF prime_p A_sub mod_subset_sums_nonempty A_proper head_nz])
      then have grow_suc: "Suc (card ?A) \<le> card ?B"
        by simp
      have len_lt: "Suc (length ds) < p"
        using card_A_lt ih by linarith
      have ih': "Suc (length ds) \<le> card ?A"
        using ih len_lt by simp
      have "Suc (Suc (length ds)) \<le> card ?B"
        using grow_suc ih' by simp
      then show ?thesis
        using len_lt by simp
    qed
  qed
  show ?thesis
    by (rule aux[OF nonzero])
qed

subsection \<open>Realizing subset sums by index sets\<close>

lemma mod_subset_sums_iff_nths:
  "x \<in> mod_subset_sums p ds \<longleftrightarrow> (\<exists>I. I \<subseteq> {..<length ds} \<and> x = sum_list (nths ds I) mod int p)"
proof (induction ds arbitrary: x)
  case Nil
  show ?case
  proof
    assume "x \<in> mod_subset_sums p []"
    then show "\<exists>I. I \<subseteq> {..<length []} \<and> x = sum_list (nths [] I) mod int p"
      by (intro exI[of _ "{}"]) simp
  next
    assume "\<exists>I. I \<subseteq> {..<length []} \<and> x = sum_list (nths [] I) mod int p"
    then show "x \<in> mod_subset_sums p []"
      by auto
  qed
next
  case (Cons d ds)
  show ?case
  proof
    assume x_in: "x \<in> mod_subset_sums p (d # ds)"
    show "\<exists>I. I \<subseteq> {..<length (d # ds)} \<and> x = sum_list (nths (d # ds) I) mod int p"
    proof (cases "x \<in> mod_subset_sums p ds")
      case True
      then obtain I where I_sub: "I \<subseteq> {..<length ds}" and x_eq: "x = sum_list (nths ds I) mod int p"
        using Cons.IH by blast
      define I' where "I' = Suc ` I"
      have I'_sub: "I' \<subseteq> {..<length (d # ds)}"
        using I_sub by (auto simp: I'_def)
      have I'_tail: "{j. Suc j \<in> I'} = I"
        by (auto simp: I'_def)
      have zero_notin_I': "0 \<notin> I'"
        by (auto simp: I'_def)
      have nths_eq: "nths (d # ds) I' = nths ds I"
        using zero_notin_I' I'_tail by (simp add: nths_Cons)
      show ?thesis
        using I'_sub x_eq by (intro exI[of _ I']) (simp add: nths_eq)
    next
      case False
      with x_in obtain y where y_in: "y \<in> mod_subset_sums p ds" and x_eq: "x = (y + d) mod int p"
        by (auto simp: mod_translate_iff)
      then obtain I where I_sub: "I \<subseteq> {..<length ds}" and y_eq: "y = sum_list (nths ds I) mod int p"
        using Cons.IH by blast
      define I' where "I' = insert 0 (Suc ` I)"
      have I'_sub: "I' \<subseteq> {..<length (d # ds)}"
        using I_sub by (auto simp: I'_def)
      have I'_tail: "{j. Suc j \<in> I'} = I"
        by (auto simp: I'_def)
      have zero_in_I': "0 \<in> I'"
        by (simp add: I'_def)
      have nths_eq: "nths (d # ds) I' = d # nths ds I"
        using zero_in_I' I'_tail by (simp add: nths_Cons)
      have "x = sum_list (nths (d # ds) I') mod int p"
        using x_eq y_eq by (simp add: nths_eq algebra_simps mod_simps)
      then show ?thesis
        using I'_sub by (intro exI[of _ I']) simp
    qed
  next
    assume "\<exists>I. I \<subseteq> {..<length (d # ds)} \<and> x = sum_list (nths (d # ds) I) mod int p"
    then obtain I where I_sub: "I \<subseteq> {..<length (d # ds)}" and x_eq: "x = sum_list (nths (d # ds) I) mod int p"
      by blast
    define J where "J = {j. Suc j \<in> I}"
    have J_sub: "J \<subseteq> {..<length ds}"
      using I_sub by (auto simp: J_def)
    have J_tail: "{j. Suc j \<in> I} = J"
      by (simp add: J_def)
    have tail_in: "sum_list (nths ds J) mod int p \<in> mod_subset_sums p ds"
      using Cons.IH J_sub by blast
    show "x \<in> mod_subset_sums p (d # ds)"
    proof (cases "0 \<in> I")
      case False
      have nths_eq: "nths (d # ds) I = nths ds J"
        using False J_tail by (simp add: nths_Cons)
      have "x = sum_list (nths ds J) mod int p"
        using x_eq by (simp add: nths_eq)
      with tail_in show ?thesis
        by simp
    next
      case True
      have nths_eq: "nths (d # ds) I = d # nths ds J"
        using True J_tail by (simp add: nths_Cons)
      have "x = (sum_list (nths ds J) + d) mod int p"
        using x_eq by (simp add: nths_eq algebra_simps mod_simps)
      then have x_translated: "x = ((sum_list (nths ds J) mod int p) + d) mod int p"
        by (simp add: mod_simps)
      have "x \<in> mod_translate p d (mod_subset_sums p ds)"
        using tail_in x_translated by (auto simp: mod_translate_iff)
      then show ?thesis
        by simp
    qed
  qed
qed

lemma mod_subset_sums_eq_residues:
  assumes prime_p: "prime p"
  assumes len: "length ds = p - 1"
  assumes nonzero: "\<forall>d\<in>set ds. d mod int p \<noteq> 0"
  shows "mod_subset_sums p ds = residues p"
text \<open>
  The lower-bound lemma shows that each nonzero increment strictly enlarges the
  current set of subset sums until all @{term p} residues have been reached.
  Since all subset sums stay inside @{term "residues p"}, cardinality forces
  equality with the full residue system.
\<close>
proof -
  have p_pos: "0 < p"
    using prime_gt_0_nat[OF prime_p] .
  have subset_res: "mod_subset_sums p ds \<subseteq> residues p"
    by (rule mod_subset_sums_subset_residues[OF p_pos])
  have lower: "p \<le> card (mod_subset_sums p ds)"
    using card_mod_subset_sums_lower_bound[OF prime_p nonzero] by (simp add: len)
  have upper: "card (mod_subset_sums p ds) \<le> p"
    by (metis card_mono card_residues p_pos residues_finite subset_res)
  have card_eq: "card (mod_subset_sums p ds) = card (residues p)"
    using lower upper p_pos by simp
  show ?thesis
    by (simp add: card_eq card_subset_eq subset_res)
qed

lemma sum_list_nths_eq_list_index_sum:
  assumes I_sub: "I \<subseteq> {..<length xs}"
  shows "sum_list (nths xs I) = list_index_sum xs I"
  using I_sub
proof (induction xs arbitrary: I)
  case Nil
  then show ?case
    by (auto simp: list_index_sum_def)
next
  case (Cons x xs)
  define J where "J = {j. Suc j \<in> I}"
  have J_sub: "J \<subseteq> {..<length xs}"
    using Cons.prems by (auto simp: J_def)
  have finite_J: "finite J"
    using J_sub by (rule finite_subset) auto
  have IH: "sum_list (nths xs J) = list_index_sum xs J"
    by (rule Cons.IH[OF J_sub])
  show ?case
  proof (cases "0 \<in> I")
    case False
    have nths_eq: "nths (x # xs) I = nths xs J"
      using False by (simp add: J_def nths_Cons)
    have I_eq: "I = Suc ` J"
    proof
      show "I \<subseteq> Suc ` J"
      proof
        fix i
        assume iI: "i \<in> I"
        from False have zero_notin: "0 \<notin> I"
          by simp
        have "0 < i"
          using iI zero_less_iff_neq_zero zero_notin by auto
        then obtain j where i_eq: "i = Suc j"
          by (cases i) auto
        have "j \<in> J"
          using iI i_eq by (simp add: J_def)
        then show "i \<in> Suc ` J"
          by (simp add: i_eq)
      qed
      show "Suc ` J \<subseteq> I"
        by (auto simp: J_def)
    qed
    have "list_index_sum (x # xs) I = (\<Sum>i\<in>Suc ` J. (x # xs) ! i)"
      by (simp add: I_eq list_index_sum_def)
    also have "\<dots> = (\<Sum>j\<in>J. (x # xs) ! Suc j)"
      by (rule sum.reindex_bij_witness[where i = Suc and j = Nat.pred]) auto
    also have "\<dots> = (\<Sum>j\<in>J. xs ! j)"
      by simp
    also have "\<dots> = list_index_sum xs J"
      by (simp add: list_index_sum_def)
    finally show ?thesis
      using IH by (simp add: nths_eq)
  next
    case True
    have nths_eq: "nths (x # xs) I = x # nths xs J"
      using True by (simp add: J_def nths_Cons)
    have I_eq: "I = insert 0 (Suc ` J)"
    proof
      show "I \<subseteq> insert 0 (Suc ` J)"
      proof
        fix i
        assume iI: "i \<in> I"
        show "i \<in> insert 0 (Suc ` J)"
          by (metis J_def iI imageI insertI1 insertI2 mem_Collect_eq old.nat.exhaust)
      qed
      show "insert 0 (Suc ` J) \<subseteq> I"
        using True by (auto simp: J_def)
    qed
    have "list_index_sum (x # xs) I = (\<Sum>i\<in>insert 0 (Suc ` J). (x # xs) ! i)"
      by (simp add: I_eq list_index_sum_def)
    also have "\<dots> = (x # xs) ! 0 + (\<Sum>i\<in>Suc ` J. (x # xs) ! i)"
      by (simp add: finite_J)
    also have "\<dots> = x + (\<Sum>j\<in>J. (x # xs) ! Suc j)"
      by (subst sum.reindex_bij_witness[where i = Suc and j = Nat.pred]) auto
    also have "\<dots> = x + (\<Sum>j\<in>J. xs ! j)"
      by simp
    also have "\<dots> = x + list_index_sum xs J"
      by (simp add: list_index_sum_def)
    finally show ?thesis
      using IH by (simp add: nths_eq)
  qed
qed

lemma mod_subset_sums_iff_list_index_sum:
  "x \<in> mod_subset_sums p ds \<longleftrightarrow> (\<exists>I. I \<subseteq> {..<length ds} \<and> x = list_index_sum ds I mod int p)"
proof
  assume "x \<in> mod_subset_sums p ds"
  then obtain I where I_sub: "I \<subseteq> {..<length ds}" and x_eq: "x = sum_list (nths ds I) mod int p"
    using mod_subset_sums_iff_nths by blast
  have "x = list_index_sum ds I mod int p"
    using x_eq sum_list_nths_eq_list_index_sum[OF I_sub] by simp
  then show "\<exists>I. I \<subseteq> {..<length ds} \<and> x = list_index_sum ds I mod int p"
    using I_sub by blast
next
  assume "\<exists>I. I \<subseteq> {..<length ds} \<and> x = list_index_sum ds I mod int p"
  then obtain I where I_sub: "I \<subseteq> {..<length ds}" and x_eq: "x = list_index_sum ds I mod int p"
    by blast
  have "x = sum_list (nths ds I) mod int p"
    using x_eq sum_list_nths_eq_list_index_sum[OF I_sub] by simp
  then show "x \<in> mod_subset_sums p ds"
    using I_sub mod_subset_sums_iff_nths by blast
qed

lemma mset_nths_subseteq:
  "mset (nths xs I) \<subseteq># mset xs"
proof (rule mset_subset_eqI)
  fix a
  show "count (mset (nths xs I)) a \<le> count (mset xs) a"
  proof (induction xs arbitrary: I)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    show ?case
    proof (cases "0 \<in> I")
      case False
      then have "count (mset (nths (x # xs) I)) a = count (mset (nths xs {j. Suc j \<in> I})) a"
        by (simp add: nths_Cons)
      also have "\<dots> \<le> count (mset xs) a"
        by (rule Cons.IH)
      also have "\<dots> \<le> count (mset (x # xs)) a"
        by simp
      finally show ?thesis .
    next
      case True
      then have "count (mset (nths (x # xs) I)) a = count (mset (nths xs {j. Suc j \<in> I})) a + (if a = x then 1 else 0)"
        by (simp add: nths_Cons)
      also have "\<dots> \<le> count (mset xs) a + (if a = x then 1 else 0)"
        using Cons.IH by simp
      also have "\<dots> = count (mset (x # xs)) a"
        by simp
      finally show ?thesis .
    qed
  qed
qed

lemma list_index_sum_partition:
  assumes I_sub: "I \<subseteq> {..<length xs}"
  shows "list_index_sum xs ({..<length xs} - I) + list_index_sum xs I = sum_list xs"
proof -
  have fin: "finite {..<length xs}"
    by simp
  have finite_I: "finite I"
    using I_sub by (rule finite_subset) auto
  have disj: "({..<length xs} - I) \<inter> I = {}"
    by auto
  have union: "({..<length xs} - I) \<union> I = {..<length xs}"
    using I_sub by auto
  have "list_index_sum xs ({..<length xs} - I) + list_index_sum xs I =
      (\<Sum>i\<in>{..<length xs} - I. xs ! i) + (\<Sum>i\<in>I. xs ! i)"
    by (simp add: list_index_sum_def)
  also have "\<dots> = (\<Sum>i\<in>({..<length xs} - I) \<union> I. xs ! i)"
    using fin finite_I disj I_sub by (subst sum.union_disjoint) auto
  also have "\<dots> = (\<Sum>i\<in>{..<length xs}. xs ! i)"
    by (simp only: union)
  also have "\<dots> = sum_list xs"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  finally show ?thesis .
qed

lemma list_index_sum_map2_diff:
  assumes len: "length xs = length ys"
  assumes I_sub: "I \<subseteq> {..<length xs}"
  shows "list_index_sum (map2 (\<lambda>x y. y - x) xs ys) I = list_index_sum ys I - list_index_sum xs I"
proof -
  have "list_index_sum (map2 (\<lambda>x y. y - x) xs ys) I = (\<Sum>i\<in>I. ys ! i - xs ! i)"
    unfolding list_index_sum_def
  proof (rule sum.cong)
    show "I = I"
      by simp
    fix i
    assume iI: "i \<in> I"
    with I_sub have i_lt: "i < length xs"
      by auto
    show "(map2 (\<lambda>x y. y - x) xs ys) ! i = ys ! i - xs ! i"
      using i_lt len by (simp add: nth_zip)
  qed
  also have "\<dots> = (\<Sum>i\<in>I. ys ! i) - (\<Sum>i\<in>I. xs ! i)"
    by (simp add: sum_subtractf)
  also have "\<dots> = list_index_sum ys I - list_index_sum xs I"
    by (simp add: list_index_sum_def)
  finally show ?thesis .
qed

end

