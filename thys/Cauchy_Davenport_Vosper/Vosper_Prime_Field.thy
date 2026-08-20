theory Vosper_Prime_Field
  imports Vosper_Support
begin

section \<open>Vosper over prime fields\<close>

text \<open>
  This theory formalizes Vosper's theorem in the prime-field setting. The proof
  is organized around Davenport transforms, first deriving one-sided
  progression results under a normalization hypothesis and then combining the
  normalized arguments to obtain the full shared-difference conclusion.
\<close>

subsection \<open>Davenport transforms and translation lemmas\<close>

definition davenport_transform ::
  "'a::ring_1 set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
where
  "davenport_transform A B e = {b \<in> B. e - b \<notin> sumset A B}"

definition davenport_remainder ::
  "'a::ring_1 set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
where
  "davenport_remainder A B e = {b \<in> B. e - b \<in> sumset A B}"

lemma sumset_mono_left:
  assumes "A \<subseteq> A'"
  shows "sumset A B \<subseteq> sumset A' B"
  using assms by (auto simp: sumset_def)

lemma sumset_mono_right:
  assumes "B \<subseteq> B'"
  shows "sumset A B \<subseteq> sumset A B'"
  using assms by (auto simp: sumset_def)

lemma sumset_translate_right:
  fixes A B :: "('a::comm_monoid_add) set"
  shows "sumset A (translate c B) = translate c (sumset A B)"
proof
  show "sumset A (translate c B) \<subseteq> translate c (sumset A B)"
  proof
    fix x
    assume "x \<in> sumset A (translate c B)"
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> B" and x_eq: "x = a + (c + b)"
      by (auto simp: sumset_def translate_def)
    have "a + b \<in> sumset A B"
      using a_in b_in by (rule sumsetI)
    then show "x \<in> translate c (sumset A B)"
    proof -
      have "x = c + (a + b)"
        using x_eq by (simp add: ac_simps)
      then show ?thesis
        using \<open>a + b \<in> sumset A B\<close> by (auto simp: translate_def)
    qed
  qed
next
  show "translate c (sumset A B) \<subseteq> sumset A (translate c B)"
  proof
    fix x
    assume "x \<in> translate c (sumset A B)"
    then obtain y where y_in: "y \<in> sumset A B" and x_eq: "x = c + y"
      by (auto simp: translate_def)
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> B" and y_eq: "y = a + b"
      by (auto simp: sumset_def)
    have "c + b \<in> translate c B"
      using b_in by (auto simp: translate_def)
    then show "x \<in> sumset A (translate c B)"
      using a_in x_eq y_eq by (auto simp: sumset_def ac_simps)
  qed
qed

lemma sumset_translate_left:
  fixes A B :: "('a::comm_monoid_add) set"
  shows "sumset (translate c A) B = translate c (sumset A B)"
proof
  show "sumset (translate c A) B \<subseteq> translate c (sumset A B)"
  proof
    fix x
    assume "x \<in> sumset (translate c A) B"
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> B" and x_eq: "x = (c + a) + b"
      by (auto simp: sumset_def translate_def)
    have "a + b \<in> sumset A B"
      using a_in b_in by (rule sumsetI)
    then show "x \<in> translate c (sumset A B)"
    proof -
      have "x = c + (a + b)"
        using x_eq by (simp add: ac_simps)
      then show ?thesis
        using \<open>a + b \<in> sumset A B\<close> by (auto simp: translate_def)
    qed
  qed
next
  show "translate c (sumset A B) \<subseteq> sumset (translate c A) B"
  proof
    fix x
    assume "x \<in> translate c (sumset A B)"
    then obtain y where y_in: "y \<in> sumset A B" and x_eq: "x = c + y"
      by (auto simp: translate_def)
    then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> B" and y_eq: "y = a + b"
      by (auto simp: sumset_def)
    have "c + a \<in> translate c A"
      using a_in by (auto simp: translate_def)
    then show "x \<in> sumset (translate c A) B"
    proof -
      have "x = (c + a) + b"
        using x_eq y_eq by (simp add: ac_simps)
      then show ?thesis
        using \<open>c + a \<in> translate c A\<close> b_in by (auto simp: sumset_def)
    qed
  qed
qed

lemma card_uminus_image_eq [simp]:
  fixes A :: "('a::ab_group_add) set"
  assumes "finite A"
  shows "card ((uminus) ` A) = card A"
  using assms by (simp add: card_image)

lemma card_2_zero_obtain:
  fixes B :: "('a::zero) set"
  assumes fin: "finite B"
  assumes zero_in: "0 \<in> B"
  assumes card2: "card B = 2"
  obtains d where "d \<noteq> 0" "B = {0, d}"
proof -
  have "card (B - {0}) = 1"
    using assms by simp
  then obtain d where diff: "B - {0} = {d}"
    by (meson card_1_singletonE)
  have "B = {0, d}"
    using diff zero_in by auto
  moreover have "d \<noteq> 0"
    using card2 calculation by auto
  ultimately show ?thesis
    using that by blast
qed

lemma davenport_partition:
  "davenport_transform A B e \<union> davenport_remainder A B e = B"
  "davenport_transform A B e \<inter> davenport_remainder A B e = {}"
  by (auto simp: davenport_transform_def davenport_remainder_def)

lemma davenport_transform_subset [simp]:
  "davenport_transform A B e \<subseteq> B"
  by (auto simp: davenport_transform_def)

lemma davenport_remainder_subset [simp]:
  "davenport_remainder A B e \<subseteq> B"
  by (auto simp: davenport_remainder_def)

lemma card_lt_univ_if_not_univ:
  fixes S :: "'a::finite set"
  assumes "S \<noteq> UNIV"
  shows "card S < card (UNIV :: 'a set)"
proof (rule ccontr)
  assume "\<not> card S < card (UNIV :: 'a set)"
  moreover have "card S \<le> card (UNIV :: 'a set)"
    by (intro card_mono) auto
  ultimately have "card S = card (UNIV :: 'a set)"
    by linarith
  then have "S = UNIV"
    using finite_UNIV by (intro card_subset_eq) auto
  with assms show False
    by simp
qed

subsection \<open>One-sided progression results\<close>

text \<open>
  The first main step shows that equality in Cauchy-Davenport, together with a
  normalization such as @{term "0 \<in> B"}, forces the opposite set to be an
  arithmetic progression.
\<close>

theorem vosper_progression_left_zero:
  fixes A B :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes zero_in_B: "0 \<in> B"
  assumes B_ge2: "2 \<le> card B"
  assumes comp_ge2: "2 \<le> card (UNIV - sumset A B)"
  assumes eq: "card (sumset A B) = card A + card B - 1"
  shows "arithmetic_progression A"
proof -
  let ?p = "card (UNIV :: 'a set)"
  have aux:
    "\<And>n::nat. \<And>A B::'a set.
      card B = n \<Longrightarrow>
      0 \<in> B \<Longrightarrow>
      2 \<le> card B \<Longrightarrow>
      2 \<le> card (UNIV - sumset A B) \<Longrightarrow>
      card (sumset A B) = card A + card B - 1 \<Longrightarrow>
      arithmetic_progression A"
  proof -
    fix n :: nat
    fix A B :: "'a set"
    show "card B = n \<Longrightarrow>
      0 \<in> B \<Longrightarrow>
      2 \<le> card B \<Longrightarrow>
      2 \<le> card (UNIV - sumset A B) \<Longrightarrow>
      card (sumset A B) = card A + card B - 1 \<Longrightarrow>
      arithmetic_progression A"
    proof (induction n arbitrary: A B rule: less_induct)
      case (less n)
      note IH = less.IH
      assume cardB: "card B = n"
      assume zero_in_B: "0 \<in> B"
      assume B_ge2: "2 \<le> card B"
      assume comp_ge2: "2 \<le> card (UNIV - sumset A B)"
      assume eq: "card (sumset A B) = card A + card B - 1"

      have finA: "finite A" and finB: "finite B"
        by simp_all
      have B_nonempty: "B \<noteq> {}"
        using B_ge2 by auto
      have A_nonempty: "A \<noteq> {}"
        using eq B_ge2 by auto
      have A_subset_sumset: "A \<subseteq> sumset A B"
      proof
        fix x
        assume x_in: "x \<in> A"
        have "x + 0 \<in> sumset A B"
          using x_in zero_in_B by (rule sumsetI)
        then show "x \<in> sumset A B"
          by simp
      qed
      have sumset_not_full: "sumset A B \<noteq> UNIV"
        using comp_ge2 by auto
      have sumset_small: "card (sumset A B) < ?p"
      proof (rule ccontr)
        assume "\<not> card (sumset A B) < ?p"
        moreover have "card (sumset A B) \<le> ?p"
          using finite_UNIV finite_sumset[OF finA finB] by (intro card_mono) auto
        ultimately have "card (sumset A B) = ?p"
          by linarith
        then have "sumset A B = UNIV"
          using finite_UNIV by (intro card_subset_eq) auto
        with sumset_not_full show False
          by simp
      qed

      show "arithmetic_progression A"
      proof (cases "card B = 2")
        case True
        obtain d where d_nonzero: "d \<noteq> 0" and B_eq: "B = {0, d}"
          by (rule card_2_zero_obtain[OF finB zero_in_B True])
        have sumset_eq: "sumset A B = A \<union> translate d A"
          using B_eq by (simp add: sumset_pair_zero)
        have card_overlap: "card (A \<inter> translate d A) = card A - 1"
        proof -
          have fin_translate: "finite (translate d A)"
            by simp
          have "card (sumset A B) = card (A \<union> translate d A)"
            using sumset_eq by simp
          also have "\<dots> = card A + card (translate d A) - card (A \<inter> translate d A)"
          proof -
            have "card A + card (translate d A) =
                card (A \<union> translate d A) + card (A \<inter> translate d A)"
              using finA fin_translate by (rule card_Un_Int)
            then show ?thesis
              by linarith
          qed
          also have "\<dots> = card A + card A - card (A \<inter> translate d A)"
            using finA by (simp add: card_translate_eq)
          finally show ?thesis
            using eq True by simp
        qed
        have smallA: "card A < ?p"
          using A_subset_sumset sumset_small finA finite_sumset[OF finA finB]
          by (meson card_mono le_less_trans)
        from arithmetic_progression_from_maximal_shift_overlap
          [OF prime_card d_nonzero smallA card_overlap]
        show ?thesis .
      next
        case False
        have cardB_gt2: "2 < card B"
          using B_ge2 False by linarith
        define S where "S = sumset A B"
        define T where "T = sumset S B"
        define E where "E = T - S"

        have finS: "finite S" and finT: "finite T" and finE: "finite E"
          unfolding S_def T_def E_def by auto
        have S_nonempty: "S \<noteq> {}"
          using A_nonempty B_nonempty unfolding S_def by auto
        have S_subset_T: "S \<subseteq> T"
        proof
          fix x
          assume x_in: "x \<in> S"
          have "x + 0 \<in> T"
            using x_in zero_in_B unfolding T_def by (rule sumsetI)
          then show "x \<in> T"
            by simp
        qed
        have T_lb: "card T \<ge> min ?p (card S + card B - 1)"
        proof -
          have "card (sumset S B) \<ge> min ?p (card S + card B - 1)"
            using cauchy_davenport_prime_field[where A = S and B = B, OF prime_card S_nonempty B_nonempty]
            by simp
          then show ?thesis
            unfolding T_def .
        qed
        have min_gt: "min ?p (card S + card B - 1) > card S"
        proof (cases "?p < card S + card B - 1")
          case True
          then show ?thesis
            using sumset_small unfolding S_def by simp
        next
          case False
          then have "min ?p (card S + card B - 1) = card S + card B - 1"
            by simp
          with B_ge2 show ?thesis
            by simp
        qed
        have T_gt: "card T > card S"
          using T_lb min_gt by linarith
        have cardE: "card E = card T - card S"
          using S_subset_T finT unfolding E_def by (simp add: card_Diff_subset)
        have E_nonempty: "E \<noteq> {}"
          using T_gt cardE by auto

        show ?thesis
        proof (rule ccontr)
          assume not_ap: "\<not> arithmetic_progression A"

          have transform_singleton:
            "davenport_transform A B e = {0}" if e_in: "e \<in> E" for e
          proof -
            let ?D = "davenport_transform A B e"
            let ?R = "davenport_remainder A B e"

            have e_notin_S: "e \<notin> S"
              using e_in unfolding E_def by auto
            have zero_in_D: "0 \<in> ?D"
              using zero_in_B e_notin_S unfolding davenport_transform_def S_def by auto
            have D_nonempty: "?D \<noteq> {}"
              using zero_in_D by auto
            have R_nonempty: "?R \<noteq> {}"
            proof -
              from e_in have "e \<in> T"
                unfolding E_def by auto
              then obtain s b where s_in: "s \<in> S" and b_in: "b \<in> B" and e_eq: "e = s + b"
                unfolding T_def by (auto simp: sumset_def)
              have "b \<in> ?R"
                using s_in b_in e_eq unfolding davenport_remainder_def S_def by simp
              then show ?thesis
                by auto
            qed
            have part: "?D \<union> ?R = B" "?D \<inter> ?R = {}"
              by (rule davenport_partition)+
            have finD: "finite ?D" and finR: "finite ?R"
              by auto
            have cardD_lt: "card ?D < card B"
            proof -
              have "card (?D \<union> ?R) = card ?D + card ?R"
                using finD finR part(2) by (simp add: card_Un_disjoint)
              then have "card B = card ?D + card ?R"
                using part(1) by simp
              moreover have "0 < card ?R"
                using R_nonempty finR by auto
              ultimately show ?thesis
                by linarith
            qed
            have left_subset: "sumset A ?D \<subseteq> S"
            proof
              fix x
              assume x_in: "x \<in> sumset A ?D"
              then obtain a b where a_in: "a \<in> A" and b_in: "b \<in> ?D" and x_eq: "x = a + b"
                by (auto simp: sumset_def)
              have "b \<in> B"
                using b_in unfolding davenport_transform_def by auto
              then show "x \<in> S"
                using a_in x_eq unfolding S_def by (auto simp: sumset_def)
            qed
            have right_subset: "(\<lambda>b. e - b) ` ?R \<subseteq> S"
              unfolding davenport_remainder_def S_def by auto
            have disj_subset: "sumset A ?D \<inter> (\<lambda>b. e - b) ` ?R \<subseteq> {}"
            proof
              fix x
              assume x_in: "x \<in> sumset A ?D \<inter> (\<lambda>b. e - b) ` ?R"
              then obtain a d r where
                  a_in: "a \<in> A" and d_in: "d \<in> ?D" and r_in: "r \<in> ?R"
                and x_eq1: "x = a + d" and x_eq2: "x = e - r"
                by (auto simp: sumset_def)
              have eq_ed: "e - d = a + r"
                using x_eq1 x_eq2 by (simp add: algebra_simps)
              have ar_in_S: "a + r \<in> S"
                using a_in r_in unfolding S_def davenport_remainder_def by (auto intro: sumsetI)
              have ed_notin: "e - d \<notin> sumset A B"
                using d_in unfolding davenport_transform_def by auto
              have ed_in: "e - d \<in> sumset A B"
                using eq_ed ar_in_S unfolding S_def by simp
              show "x \<in> {}"
                using ed_notin ed_in by blast
            qed
            have disj: "sumset A ?D \<inter> (\<lambda>b. e - b) ` ?R = {}"
              using disj_subset by blast
            have card_right: "card ((\<lambda>b. e - b) ` ?R) = card ?R"
            proof -
              have "inj_on (\<lambda>b. e - b) ?R"
                by (rule inj_onI) simp
              with finR show ?thesis
                by (simp add: card_image)
            qed
            have cardS_lb: "card S \<ge> card (sumset A ?D) + card ?R"
            proof -
              have card_union_le: "card S \<ge> card (sumset A ?D \<union> (\<lambda>b. e - b) ` ?R)"
                using left_subset right_subset finS finite_sumset[OF finA finD]
                by (intro card_mono) auto
              have fin_image: "finite ((\<lambda>b. e - b) ` ?R)"
                using finR by auto
              have card_union:
                "card (sumset A ?D \<union> (\<lambda>b. e - b) ` ?R) =
                 card (sumset A ?D) + card ((\<lambda>b. e - b) ` ?R)"
                by (rule card_Un_disjoint[OF finite_sumset[OF finA finD] fin_image disj])
              have card_union':
                "card (sumset A ?D \<union> (\<lambda>b. e - b) ` ?R) =
                 card (sumset A ?D) + card ?R"
                using card_union card_right by simp
              from card_union_le card_union' show ?thesis
                by simp
            qed
            have cardB_split: "card B = card ?D + card ?R"
            proof -
              have "card (?D \<union> ?R) = card ?D + card ?R"
                using finD finR part(2) by (simp add: card_Un_disjoint)
              then show ?thesis
                using part(1) by simp
            qed
            have upperD: "card (sumset A ?D) \<le> card A + card ?D - 1"
              using cardS_lb eq cardB_split unfolding S_def by linarith
            have sumsetD_le_S: "card (sumset A ?D) \<le> card S"
              using left_subset finS finite_sumset[OF finA finD] by (intro card_mono) auto
            have sumsetD_small: "card (sumset A ?D) < ?p"
              using sumsetD_le_S sumset_small unfolding S_def by linarith
            have eqD: "card (sumset A ?D) = card A + card ?D - 1"
            proof -
              have cdD: "card (sumset A ?D) \<ge> min ?p (card A + card ?D - 1)"
                using cauchy_davenport_prime_field[OF prime_card A_nonempty D_nonempty]
                by simp
              have "card A + card ?D - 1 < ?p"
              proof (rule ccontr)
                assume not_lt: "\<not> card A + card ?D - 1 < ?p"
                then have "min ?p (card A + card ?D - 1) = ?p"
                  by simp
                with cdD have "card (sumset A ?D) \<ge> ?p"
                  by simp
                with sumsetD_small show False
                  by simp
              qed
              with cdD upperD show ?thesis
                by simp
            qed
            have compD_ge2: "2 \<le> card (UNIV - sumset A ?D)"
            proof -
              have "UNIV - S \<subseteq> UNIV - sumset A ?D"
                using left_subset by auto
              then have "card (UNIV - S) \<le> card (UNIV - sumset A ?D)"
                by (intro card_mono) auto
              with comp_ge2 show ?thesis
                unfolding S_def by linarith
            qed

            show ?thesis
            proof (cases "2 \<le> card ?D")
              case True
              have cardD_lt_n: "card ?D < n"
                using cardD_lt cardB by simp
              have "arithmetic_progression A"
                using IH[of "card ?D" ?D A] cardD_lt_n zero_in_D True compD_ge2 eqD by blast
              with not_ap show ?thesis
                by simp
            next
              case False
              have cardD_pos: "0 < card ?D"
                using D_nonempty finD by auto
              have "card ?D = 1"
                using cardD_pos False by linarith
              then obtain x where D_eq: "?D = {x}"
                by (auto simp: card_1_singleton_iff)
              with zero_in_D show ?thesis
                by auto
            qed
          qed

          let ?Bx = "B - {0}"
          have card_Bx: "card ?Bx = card B - 1"
            using finB zero_in_B by simp
          have Bx_nonempty: "?Bx \<noteq> {}"
          proof -
            have "0 < card ?Bx"
              using card_Bx cardB_gt2 by linarith
            then show ?thesis
              using finB by (simp add: card_gt_0_iff)
          qed
          have A_disj_subset: "A \<inter> sumset E ((uminus) ` ?Bx) \<subseteq> {}"
          proof
            fix x
            assume x_in: "x \<in> A \<inter> sumset E ((uminus) ` ?Bx)"
            then obtain e b where e_in: "e \<in> E" and b_in: "b \<in> ?Bx" and x_eq: "x = e - b"
              by (auto simp: sumset_def)
            have "e = x + b"
              using x_eq by simp
            moreover have "x + b \<in> S"
              using x_in b_in unfolding S_def by (auto intro: sumsetI)
            ultimately have e_in_S: "e \<in> S"
              by simp
            have e_notin_S: "e \<notin> S"
              using e_in unfolding E_def by auto
            show "x \<in> {}"
              using e_in_S e_notin_S by blast
          qed
          have A_disj: "A \<inter> sumset E ((uminus) ` ?Bx) = {}"
            using A_disj_subset by blast
          have E_minus_subset: "sumset E ((uminus) ` ?Bx) \<subseteq> S"
          proof
            fix x
            assume x_in: "x \<in> sumset E ((uminus) ` ?Bx)"
            then obtain e b where e_in: "e \<in> E" and b_in: "b \<in> ?Bx" and x_eq: "x = e - b"
              by (auto simp: sumset_def)
            have b_notin_D: "b \<notin> davenport_transform A B e"
              using b_in transform_singleton[OF e_in] by auto
            have b_in_B: "b \<in> B"
              using b_in by auto
            have "b \<in> davenport_remainder A B e"
              using b_notin_D b_in_B unfolding davenport_transform_def davenport_remainder_def
              by auto
            then have "e - b \<in> S"
              unfolding davenport_remainder_def S_def by auto
            then show "x \<in> S"
              using x_eq by simp
          qed
          have A_union_subset: "A \<union> sumset E ((uminus) ` ?Bx) \<subseteq> S"
            using A_subset_sumset E_minus_subset unfolding S_def by auto
          have Eminus_not_full: "sumset E ((uminus) ` ?Bx) \<noteq> UNIV"
            using A_nonempty A_disj by auto
          have finEminus: "finite (sumset E ((uminus) ` ?Bx))"
            by auto
          have card_neg_Bx: "card ((uminus) ` ?Bx) = card ?Bx"
          proof -
            have "inj_on uminus ?Bx"
              by (rule inj_onI) simp
            then show ?thesis
              by (simp add: card_image)
          qed
          have neg_Bx_nonempty: "(uminus) ` ?Bx \<noteq> {}"
            using Bx_nonempty by auto
          have E_lb: "card (sumset E ((uminus) ` ?Bx)) \<ge> card E + card ?Bx - 1"
          proof -
            have cdE:
              "card (sumset E ((uminus) ` ?Bx)) \<ge> min ?p (card E + card ((uminus) ` ?Bx) - 1)"
              using cauchy_davenport_prime_field[OF prime_card E_nonempty neg_Bx_nonempty]
              by simp
            then have cdE': "card (sumset E ((uminus) ` ?Bx)) \<ge> min ?p (card E + card ?Bx - 1)"
              using card_neg_Bx by simp
            have "card (sumset E ((uminus) ` ?Bx)) < ?p"
            proof (rule ccontr)
              assume not_lt: "\<not> card (sumset E ((uminus) ` ?Bx)) < ?p"
              have le_p: "card (sumset E ((uminus) ` ?Bx)) \<le> ?p"
                using finEminus finite_UNIV by (intro card_mono) auto
              with not_lt have eq_p: "card (sumset E ((uminus) ` ?Bx)) = ?p"
                by linarith
              then have "sumset E ((uminus) ` ?Bx) = UNIV"
                using finEminus finite_UNIV by (intro card_subset_eq) auto
              with Eminus_not_full show False
                by simp
            qed
            with cdE' show ?thesis
              by simp
          qed
          have cardS_ge: "card S \<ge> card A + card (sumset E ((uminus) ` ?Bx))"
          proof -
            have card_union_le: "card S \<ge> card (A \<union> sumset E ((uminus) ` ?Bx))"
              using A_union_subset finS finEminus
              by (intro card_mono) auto
            have card_union:
              "card (A \<union> sumset E ((uminus) ` ?Bx)) =
               card A + card (sumset E ((uminus) ` ?Bx))"
              by (rule card_Un_disjoint[OF finA finEminus A_disj])
            from card_union_le card_union show ?thesis
              by simp
          qed
          have cardE_le1: "card E \<le> 1"
            using cardS_ge E_lb eq cardB_gt2 card_Bx unfolding S_def by linarith
          have cardE_pos: "0 < card E"
            using E_nonempty finE by (simp add: card_gt_0_iff)
          have cardE_one: "card E = 1"
            using cardE_pos cardE_le1 by linarith

          show False
          proof (cases "T = UNIV")
            case True
            have "card E = card (UNIV - S)"
              using True unfolding E_def by auto
            also have "\<dots> \<ge> 2"
              using comp_ge2 unfolding S_def by simp
            finally show False
              using cardE_one by simp
          next
            case False
            have cdT: "card T \<ge> min ?p (card S + card B - 1)"
              unfolding T_def
              using cauchy_davenport_prime_field[OF prime_card S_nonempty B_nonempty]
              by simp
            have T_small: "card T < ?p"
            proof (rule ccontr)
              assume not_lt: "\<not> card T < ?p"
              have le_p: "card T \<le> ?p"
                using finT finite_UNIV by (intro card_mono) auto
              with not_lt have "card T = ?p"
                by linarith
              then have "T = UNIV"
                using finT finite_UNIV by (intro card_subset_eq) auto
              with False show False
                by simp
            qed
            have T_lb': "card T \<ge> card S + card B - 1"
              using cdT T_small by simp
            have cardS_le_T: "card S \<le> card T"
              using S_subset_T finT by (intro card_mono) auto
            have "card T = card S + card E"
            proof -
              have "card T = card S + (card T - card S)"
                using cardS_le_T by simp
              also have "\<dots> = card S + card E"
                using cardE by simp
              finally show ?thesis .
            qed
            with T_lb' cardE_one have "card B \<le> 2"
              by linarith
            with cardB_gt2 show False
              by simp
        qed
        qed
  qed
  qed
  qed
  from aux[where n = "card B" and A = A and B = B] zero_in_B B_ge2 comp_ge2 eq show ?thesis
    by simp
qed

theorem vosper_progression_right_zero:
  fixes A B :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes zero_in_A: "0 \<in> A"
  assumes A_ge2: "2 \<le> card A"
  assumes comp_ge2: "2 \<le> card (UNIV - sumset A B)"
  assumes eq: "card (sumset A B) = card A + card B - 1"
  shows "arithmetic_progression B"
proof -
  have comp_ge2': "2 \<le> card (UNIV - sumset B A)"
    using comp_ge2 by (simp add: sumset_commute)
  have eq': "card (sumset B A) = card B + card A - 1"
    using eq by (simp add: sumset_commute add.commute)
  show ?thesis
    by (rule vosper_progression_left_zero[OF prime_card zero_in_A A_ge2 comp_ge2' eq'])
qed

lemma vosper_left_with_right_ap_zero_two:
  fixes A :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes d_nonzero: "d \<noteq> 0"
  assumes A_ge2: "2 \<le> card A"
  assumes comp_ge2: "2 \<le> card (UNIV - sumset A (ap_segment 0 d (Suc (Suc 0))))"
  assumes eq: "card (sumset A (ap_segment 0 d (Suc (Suc 0)))) = card A + Suc 0"
  shows "\<exists>a. A = ap_segment a d (card A)"
proof -
  let ?p = "card (UNIV :: 'a set)"
  let ?two = "Suc (Suc 0)"
  have finA: "finite A"
    by simp
  have A_nonempty: "A \<noteq> {}"
  proof
    assume "A = {}"
    then have "card A = 0"
      by simp
    then have "2 \<le> (0::nat)"
      using A_ge2 by simp
    then show False
      by simp
  qed
  have sumset_not_full: "sumset A (ap_segment 0 d ?two) \<noteq> UNIV"
    using comp_ge2 by auto
  have sumset_small: "card (sumset A (ap_segment 0 d ?two)) < card (UNIV :: 'a set)"
    using sumset_not_full card_lt_univ_if_not_univ[of "sumset A (ap_segment 0 d ?two)"] by simp
  have B_eq: "ap_segment 0 d ?two = {0, d}"
  proof
    show "ap_segment 0 d ?two \<subseteq> {0, d}"
    proof
      fix x
      assume "x \<in> ap_segment 0 d ?two"
      then obtain i where i_lt: "i < ?two" and x_eq: "x = 0 + of_nat i * d"
        by (auto simp: ap_segment_def)
      from i_lt have "i = 0 \<or> i = 1"
        by auto
      with x_eq show "x \<in> {0, d}"
        by auto
    qed
  next
    show "{0, d} \<subseteq> ap_segment 0 d ?two"
    proof
      fix x
      assume x_in: "x \<in> {0, d}"
      show "x \<in> ap_segment 0 d ?two"
      proof (cases "x = 0")
        case x0: True
        have "0 \<in> ap_segment 0 d ?two"
        proof (unfold ap_segment_def, rule image_eqI[where x = 0])
          show "0 \<in> {..< ?two}"
            by simp
          show "0 = 0 + of_nat 0 * d"
            by simp
        qed
        then show ?thesis
          using x0 by simp
      next
        case False
        with x_in have "x = d"
          by simp
        then show ?thesis
        proof -
          have "d \<in> ap_segment 0 d ?two"
          proof (unfold ap_segment_def, rule image_eqI[where x = 1])
            show "1 \<in> {..< ?two}"
              by simp
            show "d = 0 + of_nat 1 * d"
              by simp
          qed
          then show ?thesis
            using \<open>x = d\<close> by simp
        qed
      qed
    qed
  qed
  have zero_in_B: "0 \<in> ap_segment 0 d ?two"
    using B_eq by simp
  have A_subset_sumset: "A \<subseteq> sumset A (ap_segment 0 d ?two)"
  proof
    fix x
    assume x_in: "x \<in> A"
    have "x + 0 \<in> sumset A (ap_segment 0 d ?two)"
      using x_in zero_in_B by (rule sumsetI)
    then show "x \<in> sumset A (ap_segment 0 d ?two)"
      by simp
  qed
  have smallA: "card A < ?p"
    using A_subset_sumset sumset_small finite_sumset[OF finA finite_ap_segment[of 0 d ?two]]
    by (meson card_mono le_less_trans)
  have sumset_eq: "sumset A (ap_segment 0 d ?two) = A \<union> translate d A"
    using B_eq by (simp add: sumset_pair_zero)
  have fin_translate: "finite (translate d A)"
    by simp
  have card_overlap: "card (A \<inter> translate d A) = card A - 1"
  proof -
    have "card (sumset A (ap_segment 0 d ?two)) = card (A \<union> translate d A)"
      using sumset_eq by simp
    also have "\<dots> = card A + card (translate d A) - card (A \<inter> translate d A)"
    proof -
      have "card A + card (translate d A) =
          card (A \<union> translate d A) + card (A \<inter> translate d A)"
        using finA fin_translate by (rule card_Un_Int)
      then show ?thesis
        by linarith
    qed
    also have "\<dots> = card A + card A - card (A \<inter> translate d A)"
      using finA by (simp add: card_translate_eq)
    finally show ?thesis
      using eq by simp
  qed
  show ?thesis
  proof (rule ap_segment_from_maximal_shift_overlap[OF prime_card d_nonzero smallA card_overlap])
    fix a
    assume "A = ap_segment a d (card A)"
    then show "\<exists>a. A = ap_segment a d (card A)"
      by blast
  qed
qed

lemma vosper_left_with_right_ap_zero_aux:
  fixes A :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes A_ge2: "2 \<le> card A"
  assumes d_nonzero: "d \<noteq> 0"
  assumes comp_ge2: "2 \<le> card (UNIV - sumset A (ap_segment 0 d (Suc (Suc m))))"
  assumes eq: "card (sumset A (ap_segment 0 d (Suc (Suc m)))) = card A + Suc m"
  shows "\<exists>a. A = ap_segment a d (card A)"
proof -
  let ?P = "\<lambda>k X.
    2 \<le> card X \<longrightarrow>
    2 \<le> card (UNIV - sumset X (ap_segment 0 d (Suc (Suc k)))) \<longrightarrow>
    card (sumset X (ap_segment 0 d (Suc (Suc k)))) = card X + Suc k \<longrightarrow>
    (\<exists>a. X = ap_segment a d (card X))"
  have aux: "?P k X" for k X
  proof (induction k arbitrary: X)
    case 0
    show ?case
    proof (intro impI)
      assume X_ge2: "2 \<le> card X"
      assume X_comp_raw: "2 \<le> card (UNIV - sumset X (ap_segment 0 d (Suc (Suc 0))))"
      assume X_eq_raw: "card (sumset X (ap_segment 0 d (Suc (Suc 0)))) = card X + Suc 0"
      show "\<exists>a. X = ap_segment a d (card X)"
        by (rule vosper_left_with_right_ap_zero_two[OF prime_card d_nonzero X_ge2 X_comp_raw X_eq_raw])
    qed
  next
    case (Suc k)
    show ?case
    proof (intro impI)
      let ?p = "card (UNIV :: 'a set)"
      let ?n = "Suc (Suc (Suc k))"
      let ?D = "ap_segment 0 d (Suc (Suc k))"
      assume X_ge2: "2 \<le> card X"
      assume X_comp: "2 \<le> card (UNIV - sumset X (ap_segment 0 d ?n))"
      assume X_eq: "card (sumset X (ap_segment 0 d ?n)) = card X + Suc (Suc k)"
      define C where "C = sumset X ?D"
      have finX: "finite X"
        by simp
      have X_nonempty: "X \<noteq> {}"
      proof
        assume "X = {}"
        then have "card X = 0"
          by simp
        then have "2 \<le> (0::nat)"
          using X_ge2 by simp
        then show False
          by simp
      qed
      have sumset_not_full: "sumset X (ap_segment 0 d ?n) \<noteq> UNIV"
        using X_comp by auto
      have sumset_small: "card (sumset X (ap_segment 0 d ?n)) < card (UNIV :: 'a set)"
        using sumset_not_full card_lt_univ_if_not_univ[of "sumset X (ap_segment 0 d ?n)"] by simp
      have D_decomp: "ap_segment 0 d ?n = sumset ?D {0, d}"
        by (simp add: sumset_ap_segment_pair_suc)
      have final_as_C: "sumset X (ap_segment 0 d ?n) = sumset C {0, d}"
        unfolding C_def D_decomp by (simp add: sumset_assoc)
      have D_nonempty: "?D \<noteq> {}"
      proof
        assume "?D = {}"
        have "0 \<in> ?D"
        proof (unfold ap_segment_def, rule image_eqI[where x = 0])
          show "0 \<in> {..<Suc (Suc k)}"
            by simp
          show "0 = 0 + of_nat 0 * d"
            by simp
        qed
        then show False
          using \<open>?D = {}\<close> by simp
      qed
      have C_nonempty: "C \<noteq> {}"
        unfolding C_def using X_nonempty D_nonempty by auto
      have cardD: "card ?D = Suc (Suc k)"
      proof -
        have "Suc (Suc k) \<le> ?p"
          using X_eq sumset_small X_ge2 by linarith
        then show ?thesis
          by (rule card_ap_segment[OF prime_card d_nonzero])
      qed
      have C_lb: "card C \<ge> card X + Suc k"
      proof -
        have cdC: "card C \<ge> min ?p (card X + card ?D - 1)"
          unfolding C_def
          using cauchy_davenport_prime_field[OF prime_card X_nonempty D_nonempty]
          by simp
        have "card X + card ?D - 1 < ?p"
          using X_eq sumset_small cardD by simp
        then show ?thesis
          using cdC cardD by simp
      qed
      have final_eq': "card (sumset C {0, d}) = card X + Suc (Suc k)"
        using X_eq final_as_C by simp
      have C_upper: "card C \<le> card X + Suc k"
      proof -
        have cd_pair0: "card (sumset C {0, d}) \<ge> min ?p (card C + card {0, d} - 1)"
          by (rule cauchy_davenport_prime_field[OF prime_card C_nonempty]) simp
        have cd_pair: "card (sumset C {0, d}) \<ge> min ?p (card C + 1)"
          using cd_pair0 d_nonzero by simp
        have C_small: "card C + 1 < ?p"
        proof (rule ccontr)
          assume "\<not> card C + 1 < ?p"
          then have "min ?p (card C + 1) = ?p"
            by simp
          with cd_pair have "card (sumset C {0, d}) \<ge> ?p"
            by simp
          moreover have "card (sumset C {0, d}) < ?p"
            using final_as_C sumset_small by simp
          ultimately show False
            by linarith
        qed
        from cd_pair C_small have "card (sumset C {0, d}) \<ge> card C + 1"
          by simp
        then show ?thesis
          using final_eq' by linarith
      qed
      have eqC: "card C = card X + Suc k"
        using C_lb C_upper by linarith
      have D_subset: "?D \<subseteq> ap_segment 0 d ?n"
        by (auto simp: ap_segment_def)
      have C_subset: "C \<subseteq> sumset X (ap_segment 0 d ?n)"
        unfolding C_def by (rule sumset_mono_right[OF D_subset])
      have compC_ge2: "2 \<le> card (UNIV - C)"
      proof -
        have "UNIV - sumset X (ap_segment 0 d ?n) \<subseteq> UNIV - C"
          using C_subset by auto
        then have "card (UNIV - sumset X (ap_segment 0 d ?n)) \<le> card (UNIV - C)"
          by (intro card_mono) auto
        with X_comp show ?thesis
          by linarith
      qed
      show "\<exists>a. X = ap_segment a d (card X)"
        using Suc.IH[of X] X_ge2 compC_ge2 eqC
        unfolding C_def by simp
    qed
  qed
  show ?thesis
    using aux[of A m] A_ge2 comp_ge2 eq by simp
qed

theorem vosper_left_with_right_ap_zero:
  fixes A :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes A_ge2: "2 \<le> card A"
  assumes d_nonzero: "d \<noteq> 0"
  assumes n_ge2: "2 \<le> n"
  assumes comp_ge2: "2 \<le> card (UNIV - sumset A (ap_segment 0 d n))"
  assumes eq: "card (sumset A (ap_segment 0 d n)) = card A + n - 1"
  shows "\<exists>a. A = ap_segment a d (card A)"
proof -
  obtain n' where n'_eq: "n = Suc n'"
    using n_ge2 by (cases n) auto
  then obtain m where m_eq: "n' = Suc m"
    using n_ge2 by (cases n') auto
  have n_eq: "n = Suc (Suc m)"
    using n'_eq m_eq by simp
  show ?thesis
    using vosper_left_with_right_ap_zero_aux[OF prime_card A_ge2 d_nonzero, of m] comp_ge2 eq n_eq
    by simp
qed

subsection \<open>The full Vosper theorem\<close>

text \<open>
  After normalizing one side by translation and propagating the common
  difference through an explicit arithmetic progression on the other side, we
  recover the classical prime-field conclusion: both extremal sets are
  arithmetic progressions with the same nonzero step.
\<close>

theorem vosper_prime_field:
  fixes A B :: "'a::finite_field set"
  assumes prime_card: "prime (card (UNIV :: 'a set))"
  assumes A_ge2: "2 \<le> card A"
  assumes B_ge2: "2 \<le> card B"
  assumes comp_ge2: "2 \<le> card (UNIV - sumset A B)"
  assumes eq: "card (sumset A B) = card A + card B - 1"
  shows "\<exists>a b d. d \<noteq> 0 \<and> A = ap_segment a d (card A) \<and> B = ap_segment b d (card B)"
proof -
  have A_nonempty: "A \<noteq> {}"
    using A_ge2 by auto
  then obtain a0 where a0_in: "a0 \<in> A"
    by blast
  let ?A0 = "translate (- a0) A"
  have zero_in_A0: "0 \<in> ?A0"
    using a0_in by (auto simp: translate_def)
  have A0_ge2: "2 \<le> card ?A0"
    using A_ge2 by (simp add: card_translate_eq)
  have sumset_A0: "sumset ?A0 B = translate (- a0) (sumset A B)"
    by (simp add: sumset_translate_left)
  have comp_A0: "2 \<le> card (UNIV - sumset ?A0 B)"
    using comp_ge2 sumset_A0 by (simp add: card_complement_translate_eq)
  have eq_A0: "card (sumset ?A0 B) = card ?A0 + card B - 1"
  proof -
    have "card (sumset ?A0 B) = card (sumset A B)"
      using sumset_A0 by (simp add: card_translate_eq)
    also have "\<dots> = card A + card B - 1"
      using eq by simp
    also have "\<dots> = card ?A0 + card B - 1"
      by (simp add: card_translate_eq)
    finally show ?thesis .
  qed
  have apB: "arithmetic_progression B"
    using vosper_progression_right_zero[OF prime_card zero_in_A0 A0_ge2 comp_A0 eq_A0] .

  have sumset_A0_small: "card (sumset ?A0 B) < card (UNIV :: 'a set)"
  proof (rule ccontr)
    let ?p = "card (UNIV :: 'a set)"
    assume "\<not> card (sumset ?A0 B) < ?p"
    moreover have "card (sumset ?A0 B) \<le> ?p"
      using finite_UNIV finite_sumset[of ?A0 B] by (intro card_mono) auto
    ultimately have "card (sumset ?A0 B) = ?p"
      by linarith
    then have "sumset ?A0 B = UNIV"
      using finite_UNIV by (intro card_subset_eq) auto
    with comp_A0 show False
      by simp
  qed
  have B_subset_sumset: "B \<subseteq> sumset ?A0 B"
  proof
    fix x
    assume x_in: "x \<in> B"
    have "0 + x \<in> sumset ?A0 B"
      using zero_in_A0 x_in by (rule sumsetI)
    then show "x \<in> sumset ?A0 B"
      by simp
  qed
  have B_small: "card B < card (UNIV :: 'a set)"
  proof -
    have "card B \<le> card (sumset ?A0 B)"
      using B_subset_sumset finite_sumset[of ?A0 B] by (intro card_mono) auto
    with sumset_A0_small show ?thesis
      by linarith
  qed
  obtain b d where d_nonzero: "d \<noteq> 0" and B_eq: "B = ap_segment b d (card B)"
    by (rule arithmetic_progression_obtain_card[OF prime_card apB B_ge2 B_small])

  let ?B0 = "translate (- b) B"
  have B0_eq: "?B0 = ap_segment 0 d (card B)"
  proof -
    have "?B0 = translate (- b) (ap_segment b d (card B))"
      using B_eq by simp
    also have "\<dots> = ap_segment ((- b) + b) d (card B)"
      by (simp add: ap_segment_translate)
    finally show ?thesis
      by simp
  qed
  have sumset_B0: "sumset A ?B0 = translate (- b) (sumset A B)"
    by (simp add: sumset_translate_right)
  have comp_B0: "2 \<le> card (UNIV - sumset A ?B0)"
    using comp_ge2 sumset_B0 by (simp add: card_complement_translate_eq)
  have eq_B0: "card (sumset A ?B0) = card A + card B - 1"
  proof -
    have "card (sumset A ?B0) = card (sumset A B)"
      using sumset_B0 by (simp add: card_translate_eq)
    also have "\<dots> = card A + card B - 1"
      using eq by simp
    finally show ?thesis .
  qed
  have comp_B0': "2 \<le> card (UNIV - sumset A (ap_segment 0 d (card B)))"
    using comp_B0 B0_eq by simp
  have eq_B0': "card (sumset A (ap_segment 0 d (card B))) = card A + card B - 1"
    using eq_B0 B0_eq by simp
  then obtain a where A_eq: "A = ap_segment a d (card A)"
    using vosper_left_with_right_ap_zero[OF prime_card A_ge2 d_nonzero B_ge2 comp_B0'] by blast

  show ?thesis
    using d_nonzero A_eq B_eq by blast
qed

end
