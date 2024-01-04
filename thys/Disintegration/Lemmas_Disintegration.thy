(*  Title:   Lemmas_Disintegration.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)
section \<open> Lemmas \<close>

theory Lemmas_Disintegration
  imports "Standard_Borel_Spaces.StandardBorel"
begin

subsection \<open> Lemmas \<close>

lemma semiring_of_sets_binary_product_sets[simp]:
 "semiring_of_sets (space X \<times> space Y) {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
proof
  show "{a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y} \<subseteq> Pow (space X \<times> space Y)"
    using pair_measure_closed by blast
next
  fix c d
  assume "c \<in> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}" "d \<in> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
  then obtain ac bc ad bd where
   "c = ac \<times> bc" "ac \<in> sets X" "bc \<in> sets Y" "d = ad \<times> bd" "ad \<in> sets X" "bd \<in> sets Y"
    by auto
  thus "c \<inter> d \<in> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
    by(auto intro!: exI[where x="ac \<inter> ad"] exI[where x="bc \<inter> bd"])
next
  fix c d
  assume "c \<in> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}" "d \<in> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
  then obtain ac bc ad bd where cd:
   "c = ac \<times> bc" "ac \<in> sets X" "bc \<in> sets Y" "d = ad \<times> bd" "ad \<in> sets X" "bd \<in> sets Y"
    by auto
  then have eq1:"c - d = ((ac - ad) \<times> (bc - bd)) \<union> ((ac - ad) \<times> (bc \<inter> bd)) \<union> ((ac \<inter> ad) \<times> (bc - bd))"
    by blast
  obtain a1 where a1: "a1\<subseteq>sets X" "finite a1" "disjoint a1" "ac - ad = \<Union> a1"
    using cd sets.Diff_cover[of ac X ad] by auto
  obtain a2 where a2 : "a2\<subseteq>sets Y" "finite a2" "disjoint a2" "bc - bd = \<Union> a2"
    using cd sets.Diff_cover[of bc Y bd] by auto
  define A1 A2 A3
    where A1_def:"A1 \<equiv> {a \<times> b|a b. a \<in> a1 \<and> b \<in> a2}"
      and A2_def:"A2 \<equiv> {a \<times> (bc \<inter> bd)|a . a \<in> a1}"
      and A3_def:"A3 \<equiv> {(ac \<inter> ad) \<times> b|b. b \<in> a2}"
  have disj:"disjoint (A1 \<union> A2 \<union> A3)"
  proof -
    have [simp]: "disjoint A1"
    proof
      fix x y
      assume "x \<in> A1" "y \<in> A1" "x \<noteq> y"
      then obtain xa xb ya yb where xy: "x = xa \<times> xb" "xa \<in> a1" "xb \<in> a2" "y = ya \<times> yb" "ya \<in> a1" "yb \<in> a2"
        by(auto simp: A1_def)
      with \<open>x \<noteq> y\<close> consider "xa \<noteq> ya" | "xb \<noteq> yb" by auto
      thus "disjnt x y"
      proof cases
        case 1
        then have "xa \<inter> ya = {}"
          using a1(3) xy by(auto simp: disjoint_def)
        thus ?thesis
          by(auto simp: xy disjnt_def)
      next
        case 2
        then have "xb \<inter> yb = {}"
          using a2(3) xy by(auto simp: disjoint_def)
        thus ?thesis
          by(auto simp: xy disjnt_def)
      qed
    qed
    have [simp]: "disjoint A2"
    proof
      fix x y
      assume "x \<in> A2" "y \<in> A2" "x \<noteq> y"
      then obtain xa ya where xy: "x = xa \<times> (bc \<inter> bd)" "xa \<in> a1" "y = ya \<times> (bc \<inter> bd)" "ya \<in> a1"
        by(auto simp: A2_def)
      with a1(3) \<open>x \<noteq> y\<close> have "xa \<inter> ya = {}"
        by(auto simp: disjoint_def)
      thus "disjnt x y"
        by(auto simp: xy disjnt_def)
    qed
    have [simp]: "disjoint A3"
    proof
      fix x y
      assume "x \<in> A3" "y \<in> A3" "x \<noteq> y"
      then obtain xb yb where xy:"x = (ac \<inter> ad) \<times> xb" "xb \<in> a2" "y = (ac \<inter> ad) \<times> yb" "yb \<in> a2"
        by(auto simp: A3_def)
      with a2(3) \<open>x \<noteq> y\<close> have "xb \<inter> yb = {}"
        by(auto simp: disjoint_def)
      thus "disjnt x y"
        by(auto simp: xy disjnt_def)
    qed
    show ?thesis
      by(auto intro!: disjoint_union) (insert a1 a2,auto simp: A1_def A2_def A3_def)
  qed
  have fin: "finite (A1 \<union> A2 \<union> A3)"
    using a1 a2 by (auto simp: A1_def A2_def A3_def finite_image_set2)
  have cdeq:"c - d = \<Union> (A1 \<union> A2 \<union> A3)"
  proof -
    have [simp]:"\<Union> a1 \<times> \<Union> a2 =  \<Union> A1" "\<Union> a1 \<times> (bc \<inter> bd) = \<Union> A2" "(ac \<inter> ad) \<times> \<Union> a2 = \<Union> A3"
      by (auto simp: A1_def A2_def A3_def)
    show ?thesis
      using a1(4) a2(4) by(simp add: eq1)
  qed
  have "A1 \<union> A2 \<union> A3 \<subseteq> {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}"
    using a1(1) a2(1) cd by(auto simp: A1_def A2_def A3_def)
  with fin disj cdeq show "\<exists>C\<subseteq>{a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}. finite C \<and> disjoint C \<and> c - d = \<Union> C"
    by (auto intro!: exI[where x="A1 \<union> A2 \<union> A3"])
qed auto

lemma sets_pair_restrict_space:
 "sets (restrict_space X A \<Otimes>\<^sub>M restrict_space Y B) = sets (restrict_space (X \<Otimes>\<^sub>M Y) (A \<times> B))"
 (is "?lhs = ?rhs")
proof -
  have "?lhs = sigma_sets (space (restrict_space X A) \<times> space (restrict_space Y B)) {a \<times> b |a b. a \<in> sets (restrict_space X A) \<and> b \<in> sets (restrict_space Y B)}"
    by(simp add: sets_pair_measure)
  also have "... = sigma_sets (space (restrict_space X A) \<times> space (restrict_space Y B)) {a \<times> b \<inter> space (restrict_space X A) \<times> space (restrict_space Y B) |a b. a \<in> sets X \<and> b \<in> sets Y}"
  proof -
    have "{a \<times> b |a b. a \<in> sets (restrict_space X A) \<and> b \<in> sets (restrict_space Y B)} = {a \<times> b \<inter> space (restrict_space X A) \<times> space (restrict_space Y B) |a b. a \<in> sets X \<and> b \<in> sets Y}"
      unfolding space_restrict_space sets_restrict_space
    proof safe
      fix xa xb
      show "xa \<in> sets X \<Longrightarrow> xb \<in> sets Y \<Longrightarrow>
            \<exists>a b. (A \<inter> xa) \<times> (B \<inter> xb) = a \<times> b \<inter> (A \<inter> space X) \<times> (B \<inter> space Y) \<and> a \<in> sets X \<and> b \<in> sets Y"
        by(auto intro!: exI[where x=xa] exI[where x=xb] dest:sets.sets_into_space)
    next
      fix a b
      show "a \<in> sets X \<Longrightarrow> b \<in> sets Y \<Longrightarrow>
       \<exists>aa ba. a \<times> b \<inter> (A \<inter> space X) \<times> (B \<inter> space Y) = aa \<times> ba \<and> aa \<in> sets.restricted_space X A \<and> ba \<in> sets.restricted_space Y B"
        by(auto intro!: exI[where x="a \<inter> A"] exI[where x="b \<inter> B"] dest:sets.sets_into_space)
    qed
    thus ?thesis by simp
  qed
  also have "... = sigma_sets (space (restrict_space X A) \<times> space (restrict_space Y B)) {(\<lambda>x. x) -` c \<inter> space (restrict_space X A) \<times> space (restrict_space Y B) |c. c \<in> {a \<times> b| a b. a \<in> sets X \<and> b \<in> sets Y}}"
  proof -
    have "{a \<times> b \<inter> space (restrict_space X A) \<times> space (restrict_space Y B) |a b. a \<in> sets X \<and> b \<in> sets Y} = {(\<lambda>x. x) -` c \<inter> space (restrict_space X A) \<times> space (restrict_space Y B) |c. c \<in> {a \<times> b| a b. a \<in> sets X \<and> b \<in> sets Y}}"
      by auto
    thus ?thesis by simp
  qed
  also have "... = {(\<lambda>x. x) -` c \<inter> space (restrict_space X A) \<times> space (restrict_space Y B) |c. c \<in> sigma_sets (space X \<times> space Y) {a \<times> b |a b. a \<in> sets X \<and> b \<in> sets Y}}"
    by(rule sigma_sets_vimage_commute[symmetric]) (auto simp: space_restrict_space)
  also have "... = {c \<inter>  (A \<inter> space X) \<times> (B \<inter> space Y) |c. c \<in> sets (X \<Otimes>\<^sub>M Y)}"
    by(simp add: space_restrict_space sets_pair_measure)
  also have "... = {c \<inter> A \<times> B |c. c \<in> sets (X \<Otimes>\<^sub>M Y)}"
    using sets.sets_into_space[of _ "X \<Otimes>\<^sub>M Y",simplified space_pair_measure] by blast
  also have "... = ?rhs"
    by(auto simp: sets_restrict_space)
  finally show ?thesis .
qed

lemma restrict_space_space[simp]: "restrict_space M (space M) = M"
  by(auto intro!: measure_eqI simp: sets_restrict_space emeasure_restrict_space sets.sets_into_space)

lemma atMostq_Int_stable:
  "Int_stable {{..r} |r::real. r \<in> \<rat>}"
  by(auto simp: Int_stable_def min_def)

lemma rborel_eq_atMostq:
 "borel = sigma UNIV { {..r} | r::real. r \<in> \<rat>}"
proof(safe intro!: borel_eq_sigmaI1[OF borel_eq_atMost,where F=id,simplified])
  fix a :: real
  interpret s: sigma_algebra UNIV "sigma_sets UNIV {{..r} |r. r \<in> \<rat>}"
    by(auto intro!: sigma_algebra_sigma_sets)
  have [simp]: "{..a} = (\<Inter> ((\<lambda>r. {..r}) ` {r. r \<in> \<rat> \<and> a \<le> r}))"
    by auto (metis Rats_dense_in_real less_le_not_le nle_le)
  show "{..a} \<in> sigma_sets UNIV {{..r} |r. r \<in> \<rat>}"
    using countable_Collect countable_rat Rats_no_top_le
    by(auto intro!: s.countable_INT')
qed auto

corollary rborel_eq_atMostq_sets:
 "sets borel = sigma_sets UNIV {{..r} |r::real. r \<in> \<rat>}"
  by(simp add: rborel_eq_atMostq)

lemma mono_absolutely_continuous:
  assumes "sets \<mu> = sets \<nu>" "\<And>A. A \<in> sets \<mu> \<Longrightarrow> \<mu> A \<le> \<nu> A"
  shows "absolutely_continuous \<nu> \<mu>"
  by(auto simp: absolutely_continuous_def) (metis assms(1) assms(2) fmeasurableD fmeasurableI_null_sets le_zero_eq null_setsD1 null_setsI)

lemma ex_measure_countable_space:
  assumes "countable (space X)"
      and "sets X = Pow (space X)"
    shows "\<exists>\<mu>. sets \<mu> = sets X \<and> (\<forall>x\<in>space X. \<mu> {x} = f x)"
proof -
  define \<mu> where "\<mu> \<equiv> extend_measure (space X) (space X) (\<lambda>x. {x}) f"
  have s:"sets \<mu> = sets X"
    using sets_extend_measure[of "\<lambda>x. {x}" "space X" "space X"] sigma_sets_singletons[OF assms(1)]
    by(auto simp add: \<mu>_def assms(2))
  show ?thesis
  proof(safe intro!: exI[where x=\<mu>])
    fix x
    assume x:"x \<in> space X"
    show "\<mu> {x} = f x"
    proof(cases "finite (space X)")
      case fin:True
      then have sets_fin:"x \<in> sets \<mu> \<Longrightarrow> finite x" for x
        by(auto intro!: rev_finite_subset[OF fin] sets.sets_into_space simp: s)
      define \<mu>' where "\<mu>' \<equiv> (\<lambda>A. \<Sum>x\<in>A. f x)"
      show ?thesis
      proof(rule emeasure_extend_measure[of \<mu> "space X" "space X" _ f \<mu>' x])
        show "countably_additive (sets \<mu>) \<mu>'"
          using fin sets_fin
          by(auto intro!: sets.countably_additiveI_finite simp: sets_eq_imp_space_eq[OF s] positive_def \<mu>'_def additive_def comm_monoid_add_class.sum.union_disjoint)
      qed(auto simp: x \<mu>_def \<mu>'_def positive_def)
    next
      case inf:False
      define \<mu>' where "\<mu>' \<equiv> (\<lambda>A. \<Sum>n. if from_nat_into (space X) n \<in> A then f (from_nat_into (space X) n) else 0)"
      show ?thesis
      proof(rule emeasure_extend_measure[of \<mu> "space X" "space X" _ f \<mu>' x])
        fix i
        assume "i \<in> space X"
        then obtain n where n:"from_nat_into (space X) n = i"
          using  bij_betw_from_nat_into[OF assms(1) inf] by (meson f_the_inv_into_f_bij_betw)
        then have "\<mu>' {i} =  (\<Sum>m. if m = n then f (from_nat_into (space X) n) else 0)"
          using from_nat_into_inj_infinite[OF assms(1) inf]
          by(auto simp: \<mu>'_def) metis
        also have "... = (\<Sum>m. if (m + (Suc n)) = n then f (from_nat_into (space X) n) else 0) + (\<Sum>m<Suc n. if m = n then f (from_nat_into (space X) n) else 0)"
          by(rule suminf_offset) auto
        also have "... = f i"
          by(auto simp: n)
        finally show "\<mu>' {i} = f i" .
      next
        show "countably_additive (sets \<mu>) \<mu>'"
        proof(rule countably_additiveI)
          fix A :: "nat \<Rightarrow> _"
          assume h:"range A \<subseteq> sets \<mu>" "disjoint_family A" "\<Union> (range A) \<in> sets \<mu>"
          show "(\<Sum>i. \<mu>' (A i)) = \<mu>' (\<Union> (range A))"
          proof -
            have "(\<Sum>i. \<mu>' (A i)) = (\<integral>\<^sup>+ i. \<mu>' (A i) \<partial>(count_space UNIV))"
              by(simp add: nn_integral_count_space_nat)
            also have "... = (\<integral>\<^sup>+ i. (\<Sum>n. if from_nat_into (space X) n \<in> A i then f (from_nat_into (space X) n) else 0) \<partial>(count_space UNIV))"
              by(simp add: \<mu>'_def)
            also have "... = (\<Sum>n. (\<integral>\<^sup>+ i. (if from_nat_into (space X) n \<in> A i then f (from_nat_into (space X) n) else 0) \<partial>(count_space UNIV)))"
              by(simp add: nn_integral_suminf)
            also have "... = (\<Sum>n. (\<integral>\<^sup>+ i. f (from_nat_into (space X) n) * indicator (A i) (from_nat_into (space X) n) \<partial>(count_space UNIV)))"
              by(auto intro!: suminf_cong nn_integral_cong)
            also have "... = (\<Sum>n. (\<Sum>i. f (from_nat_into (space X) n) * indicator (A i) (from_nat_into (space X) n)))"
              by(simp add: nn_integral_count_space_nat)
            also have "... = (\<Sum>n. f (from_nat_into (space X) n) * indicator (\<Union> (range A)) (from_nat_into (space X) n))"
              by(simp add: suminf_indicator[OF h(2)])
            also have "... = \<mu>' (\<Union> (range A))"
              by(auto simp: \<mu>'_def intro!: suminf_cong)
            finally show ?thesis .
          qed
        qed
      qed(auto simp: x \<mu>_def \<mu>'_def positive_def)
    qed
  qed(simp_all add: s)
qed

lemma ex_prob_space_countable:
  assumes "space X \<noteq> {}" "countable (space X)"
      and "sets X = Pow (space X)"
    shows "\<exists>\<mu>. sets \<mu> = sets X \<and> prob_space \<mu>"
proof(cases "finite (space X)")
  case fin:True
  define n where "n \<equiv> card (space X)"
  with fin assms(1) have n: "0 < n"
    by(simp add: card_gt_0_iff)
  obtain \<mu> where \<mu>: "sets \<mu> = sets X" "\<And>x. x \<in> space X \<Longrightarrow> \<mu> {x} = ennreal (1 / real n)"
    using ex_measure_countable_space[OF assms(2,3)] by meson
  then have sets_fin:"x \<in> sets \<mu> \<Longrightarrow> finite x" for x
     by(auto intro!: rev_finite_subset[OF fin] sets.sets_into_space)
  show ?thesis
  proof(safe intro!: exI[where x=\<mu>])
    show "prob_space \<mu>"
    proof
      have "emeasure \<mu> (space \<mu>) = (\<Sum>a\<in>space \<mu>. ennreal (1/n))"
        using emeasure_eq_sum_singleton[OF sets_fin[OF sets.top],of \<mu>] assms(3) \<mu>
        by auto
      also have "... = of_nat n * ennreal (1 / real n)"
        using \<mu>(2) sets_eq_imp_space_eq[OF \<mu>(1)] by(simp add: n_def)
      also have "... = 1"
        using n by(auto simp: ennreal_of_nat_eq_real_of_nat) (metis ennreal_1 ennreal_mult'' mult.commute nonzero_eq_divide_eq not_gr0 of_nat_0_eq_iff of_nat_0_le_iff)
      finally show "emeasure \<mu> (space \<mu>) = 1" .
    qed
  qed(use \<mu> in auto)
next
  case inf:False
  obtain \<mu> where \<mu>: "sets \<mu> = sets X" "\<And>x. x \<in> space X \<Longrightarrow> \<mu> {x} = (1/2)^(Suc (to_nat_on (space X) x))"
    using ex_measure_countable_space[OF assms(2,3),of "\<lambda>x. (1/2)^(Suc (to_nat_on (space X) x))"] by auto
  show ?thesis
  proof(safe intro!: exI[where x=\<mu>])
    show "prob_space \<mu>"
    proof
      have "emeasure \<mu> (space \<mu>) = emeasure \<mu> (\<Union>n. {from_nat_into (space X) n})"
        by(simp add: sets_eq_imp_space_eq[OF \<mu>(1)] UNION_singleton_eq_range assms(1) assms(2))
      also have "... = (\<Sum>n. \<mu> {from_nat_into (space X) n})"
        using from_nat_into_inj_infinite[OF assms(2) inf] from_nat_into[OF assms(1)] assms(3)
        by(auto intro!: suminf_emeasure[symmetric] simp: \<mu>(1) disjoint_family_on_def)
      also have "... = (\<Sum>n. (1/2)^(Suc n))"
        by(simp add: \<mu>(2)[OF from_nat_into[OF assms(1)]] to_nat_on_from_nat_into_infinite[OF assms(2) inf])
      also have "... = (\<Sum>i. ennreal ((1 / 2) ^ Suc i))"
        by (metis (mono_tags, opaque_lifting) divide_ennreal divide_pos_pos ennreal_numeral ennreal_power le_less power_0 zero_less_numeral zero_less_one)
      also have "... = 1"
        using suminf_ennreal_eq[OF _  power_half_series]
        by (metis ennreal_1 zero_le_divide_1_iff zero_le_numeral zero_le_power)
      finally show "emeasure \<mu> (space \<mu>) = 1" .
    qed
  qed(use \<mu> in auto)
qed

lemma AE_I'':
  assumes "N \<in> null_sets M"
      and "\<And>x. x \<in> space M \<Longrightarrow> x \<notin> N \<Longrightarrow> P x"
    shows "AE x in M. P x"
  by (metis (no_types, lifting) assms eventually_ae_filter mem_Collect_eq subsetI)

lemma absolutely_continuous_trans:
  assumes "absolutely_continuous L M" "absolutely_continuous M N"
  shows "absolutely_continuous L N"
  using assms by(auto simp: absolutely_continuous_def)

subsection \<open> Equivalence of Measures \<close>
abbreviation equivalence_measure :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" (infix "~\<^sub>M" 60)
  where "equivalence_measure M N \<equiv> absolutely_continuous M N \<and> absolutely_continuous N M"

lemma equivalence_measure_refl: "M ~\<^sub>M M"
  by(auto simp: absolutely_continuous_def)

lemma equivalence_measure_sym:
  assumes "M ~\<^sub>M N"
  shows "N ~\<^sub>M M"
  using assms by simp

lemma equivalence_measure_trans:
  assumes "M ~\<^sub>M N" "N ~\<^sub>M L"
  shows "M ~\<^sub>M L"
  using assms by(auto simp: absolutely_continuous_def)

lemma equivalence_measureI:
  assumes "absolutely_continuous M N" "absolutely_continuous N M"
  shows "M ~\<^sub>M N"
  by(simp add: assms)

end