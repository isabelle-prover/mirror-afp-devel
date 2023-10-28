(*  Title:   Measure_QuasiBorel_Adjunction.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open>Relation to Measurable Spaces\<close>

theory Measure_QuasiBorel_Adjunction
  imports "QuasiBorel" "QBS_Morphism" Lemmas_S_Finite_Measure_Monad
begin

text \<open> We construct the adjunction between \textbf{Meas} and \textbf{QBS},
       where \textbf{Meas} is the category of measurable spaces and measurable functions,
       and \textbf{QBS} is the category of quasi-Borel spaces and morphisms.\<close>

subsubsection \<open> The Functor $R$ \<close>
definition measure_to_qbs :: "'a measure \<Rightarrow> 'a quasi_borel" where
"measure_to_qbs X \<equiv> Abs_quasi_borel (space X, borel \<rightarrow>\<^sub>M X)"

lemma
  shows qbs_space_R: "qbs_space (measure_to_qbs X) = space X" (is ?goal1)
    and qbs_Mx_R: "qbs_Mx (measure_to_qbs X) = borel \<rightarrow>\<^sub>M X" (is ?goal2)
proof -
  have "Rep_quasi_borel (measure_to_qbs X) = (space X, borel \<rightarrow>\<^sub>M X)"
    by(auto intro!: Abs_quasi_borel_inverse is_quasi_borel_intro qbs_closed1I qbs_closed2I  simp: measure_to_qbs_def dest:measurable_space) (rule qbs_closed3I, auto)
  thus ?goal1 ?goal2
    by (simp_all add: qbs_space_def qbs_Mx_def)
qed

text \<open> The following lemma says that @{term measure_to_qbs} is a functor from \textbf{Meas} to \textbf{QBS}. \<close>
lemma r_preserves_morphisms:
   "X \<rightarrow>\<^sub>M Y \<subseteq> (measure_to_qbs X) \<rightarrow>\<^sub>Q (measure_to_qbs Y)"
  by(auto intro!: qbs_morphismI simp: qbs_Mx_R)

subsubsection \<open> The Functor $L$ \<close>
definition sigma_Mx :: "'a quasi_borel \<Rightarrow> 'a set set" where
"sigma_Mx X \<equiv> {U \<inter> qbs_space X |U. \<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` U \<in> sets borel}"

definition qbs_to_measure :: "'a quasi_borel \<Rightarrow> 'a measure" where
"qbs_to_measure X \<equiv> Abs_measure (qbs_space X, sigma_Mx X, \<lambda>A. (if A = {} then 0 else if A \<in> - sigma_Mx X then 0 else \<infinity>))"

lemma measure_space_L: "measure_space (qbs_space X) (sigma_Mx X) (\<lambda>A. (if A = {} then 0 else if A \<in> - sigma_Mx X then 0 else \<infinity>))"
  unfolding measure_space_def
proof safe

  show "sigma_algebra (qbs_space X) (sigma_Mx X)"
  proof(rule sigma_algebra.intro)
    show "algebra (qbs_space X) (sigma_Mx X)"
    proof
      have "\<forall> U \<in> sigma_Mx X. U \<subseteq> qbs_space X"
        using sigma_Mx_def subset_iff by fastforce
      thus "sigma_Mx X \<subseteq> Pow (qbs_space X)" by auto
    next
      show "{} \<in> sigma_Mx X"
        unfolding sigma_Mx_def by auto
    next
      fix A
      fix B
      assume "A \<in> sigma_Mx X"
             "B \<in> sigma_Mx X"
      then have "\<exists> Ua. A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets borel)"
        by (simp add: sigma_Mx_def)
      then obtain Ua where pa:"A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets borel)" by auto
      have "\<exists> Ub. B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets borel)"
        using \<open>B \<in> sigma_Mx X\<close> sigma_Mx_def by auto
      then obtain Ub where pb:"B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets borel)" by auto
      from pa pb have [simp]:"\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (Ua \<inter> Ub) \<in> sets borel"
        by auto
      from this pa pb sigma_Mx_def have [simp]:"(Ua \<inter> Ub) \<inter> qbs_space X \<in> sigma_Mx X" by blast
      from pa pb have [simp]:"A \<inter> B = (Ua \<inter> Ub) \<inter> qbs_space X" by auto
      thus "A \<inter> B \<in> sigma_Mx X" by simp
    next
      fix A
      fix B
      assume "A \<in> sigma_Mx X"
             "B \<in> sigma_Mx X"
      then have "\<exists> Ua. A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets borel)"
        by (simp add: sigma_Mx_def)
      then obtain Ua where pa:"A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets borel)" by auto
      have "\<exists> Ub. B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets borel)"
        using \<open>B \<in> sigma_Mx X\<close> sigma_Mx_def by auto
      then obtain Ub where pb:"B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets borel)" by auto
      from pa pb have [simp]:"A - B = (Ua \<inter> -Ub) \<inter> qbs_space X" by auto
      from pa pb have "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -`(Ua \<inter> -Ub) \<in> sets borel"
        by (metis Diff_Compl double_compl sets.Diff vimage_Compl vimage_Int)
      hence 1:"A - B \<in> sigma_Mx X"
        using sigma_Mx_def \<open>A - B = Ua \<inter> - Ub \<inter> qbs_space X\<close> by blast
      show "\<exists>C\<subseteq>sigma_Mx X. finite C \<and> disjoint C \<and> A - B = \<Union> C"
      proof
        show "{A - B} \<subseteq>sigma_Mx X \<and> finite {A-B} \<and> disjoint {A-B} \<and> A - B = \<Union> {A-B}"
          using 1 by auto
      qed
    next
      fix A
      fix B
      assume "A \<in> sigma_Mx X"
             "B \<in> sigma_Mx X"
      then have "\<exists> Ua. A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets borel)"
        by (simp add: sigma_Mx_def)
      then obtain Ua where pa:"A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets borel)" by auto
      have "\<exists> Ub. B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets borel)"
        using \<open>B \<in> sigma_Mx X\<close> sigma_Mx_def by auto
      then obtain Ub where pb:"B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets borel)" by auto
      from pa pb have "A \<union> B = (Ua \<union> Ub) \<inter> qbs_space X" by auto
      from pa pb have "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -`(Ua \<union> Ub) \<in> sets borel" by auto
      then show "A \<union> B \<in> sigma_Mx X"
        unfolding sigma_Mx_def
        using \<open>A \<union> B = (Ua \<union> Ub) \<inter> qbs_space X\<close> by blast
    next
      have "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (UNIV) \<in> sets borel"
        by simp
      thus "qbs_space X \<in> sigma_Mx X"
        unfolding sigma_Mx_def
        by blast
    qed
  next
    show "sigma_algebra_axioms (sigma_Mx X)"
      unfolding sigma_algebra_axioms_def
    proof safe
      fix A :: "nat \<Rightarrow> _"
      assume 1:"range A \<subseteq> sigma_Mx X"
      then have 2:"\<forall>i. \<exists>Ui. A i = Ui \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ui \<in> sets borel)"
        unfolding sigma_Mx_def by auto
      then have "\<exists> U :: nat \<Rightarrow> _. \<forall>i. A i = U i \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (U i) \<in> sets borel)"
        by (rule choice)
      from this obtain U where pu:"\<forall>i. A i = U i \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (U i) \<in> sets borel)"
        by auto
      hence "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (\<Union> (range U)) \<in> sets borel"
        by (simp add: countable_Un_Int(1) vimage_UN)
      from pu have "\<Union> (range A) = (\<Union>i::nat. (U i \<inter> qbs_space X))" by blast
      hence "\<Union> (range A) = \<Union> (range U) \<inter> qbs_space X" by auto
      thus "\<Union> (range A) \<in> sigma_Mx X"
        using sigma_Mx_def \<open>\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` \<Union> (range U) \<in> sets borel\<close> by blast
    qed
  qed
next
  show "countably_additive (sigma_Mx X) (\<lambda>A. if A = {} then 0 else if A \<in> - sigma_Mx X then 0 else \<infinity>)"
  proof(rule countably_additiveI)
    fix A :: "nat \<Rightarrow> _"
    assume h:"range A \<subseteq> sigma_Mx X"
             "\<Union> (range A) \<in> sigma_Mx X"
    consider "\<Union> (range A) = {}" | "\<Union> (range A) \<noteq> {}"
      by auto
    then show "(\<Sum>i. if A i = {} then 0 else if A i \<in> - sigma_Mx X then 0 else \<infinity>) =
               (if \<Union> (range A) = {} then 0 else if \<Union> (range A) \<in> - sigma_Mx X then 0 else (\<infinity> :: ennreal))"
    proof cases
      case 1
      then have "\<And>i. A i = {}"
        by simp
      thus ?thesis
        by(simp add: 1)
    next
      case 2
      then obtain j where hj:"A j \<noteq> {}"
        by auto
      have "(\<Sum>i. if A i = {} then 0  else if A i \<in> - sigma_Mx X then 0 else \<infinity>) = (\<infinity> :: ennreal)"
      proof -
        have hsum:"\<And>N f. sum f {..<N} \<le> (\<Sum>n. (f n :: ennreal))"
          by (simp add: sum_le_suminf)
        have hsum':"\<And>P f. (\<exists>j. j \<in> P \<and> f j = (\<infinity> :: ennreal)) \<Longrightarrow> finite P \<Longrightarrow> sum f P = \<infinity>"
          by auto
        have h1:"(\<Sum>i<j+1. if A i = {} then 0 else if A i \<in> - sigma_Mx X then 0 else \<infinity>) = (\<infinity> :: ennreal)"
        proof(rule hsum')
          show "\<exists>ja. ja \<in> {..<j + 1} \<and> (if A ja = {} then 0 else if A ja \<in> - sigma_Mx X then 0 else \<infinity>) = (\<infinity> :: ennreal)"
          proof(rule exI[where x=j],rule conjI)
            have "A j \<in> sigma_Mx X"
              using h(1) by auto
            then show "(if A j = {} then 0 else if A j \<in> - sigma_Mx X then 0 else \<infinity>) = (\<infinity> :: ennreal)"
              using hj by simp
          qed simp
        qed simp
        have "(\<Sum>i<j+1. if A i = {} then 0 else if A i \<in> - sigma_Mx X then 0 else \<infinity>) \<le> (\<Sum>i. if A i = {} then 0 else if A i \<in> - sigma_Mx X then 0 else (\<infinity> :: ennreal))"
          by(rule hsum)
        thus ?thesis
          by(simp only: h1) (simp add: top.extremum_unique)
      qed
      moreover have "(if \<Union> (range A) = {} then 0 else if \<Union> (range A) \<in> - sigma_Mx X then 0 else \<infinity>) = (\<infinity> :: ennreal)"
        using 2 h(2) by simp
      ultimately show ?thesis
        by simp
    qed
  qed
qed(simp add: positive_def)

lemma
  shows space_L: "space (qbs_to_measure X) = qbs_space X" (is ?goal1)
    and sets_L: "sets (qbs_to_measure X) = sigma_Mx X" (is ?goal2)
    and emeasure_L: "emeasure (qbs_to_measure X) = (\<lambda>A. if A = {} \<or> A \<notin> sigma_Mx X then 0 else \<infinity>)" (is ?goal3)
proof -
  have "Rep_measure (qbs_to_measure X) = (qbs_space X, sigma_Mx X, \<lambda>A. (if A = {} then 0 else if A \<in> - sigma_Mx X then 0 else \<infinity>))"
    unfolding qbs_to_measure_def by(auto intro!: Abs_measure_inverse simp: measure_space_L)
  thus ?goal1 ?goal2 ?goal3
    by(auto simp: sets_def space_def emeasure_def)
qed

lemma qbs_Mx_sigma_Mx_contra:
  assumes "qbs_space X = qbs_space Y"
      and "qbs_Mx X \<subseteq> qbs_Mx Y"
  shows "sigma_Mx Y \<subseteq> sigma_Mx X"
  using assms by(auto simp: sigma_Mx_def)


text \<open> The following lemma says that @{term qbs_to_measure} is a functor from \textbf{QBS} to \textbf{Meas}. \<close>
lemma l_preserves_morphisms:
  "X \<rightarrow>\<^sub>Q Y \<subseteq> (qbs_to_measure X) \<rightarrow>\<^sub>M (qbs_to_measure Y)"
proof safe
  fix f
  assume h:"f \<in> X \<rightarrow>\<^sub>Q Y"
  show "f \<in> (qbs_to_measure X) \<rightarrow>\<^sub>M (qbs_to_measure Y)"
  proof(rule measurableI)
    fix A
    assume "A \<in> sets (qbs_to_measure Y)"
    then obtain Ua where pa:"A = Ua \<inter> qbs_space Y \<and> (\<forall>\<alpha>\<in>qbs_Mx Y. \<alpha> -` Ua \<in> sets borel)"
      by (auto simp: sigma_Mx_def sets_L)
    have "\<forall>\<alpha>\<in>qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y"
         "\<forall>\<alpha>\<in> qbs_Mx X. \<alpha> -` (f -` (qbs_space Y)) = UNIV"
      using qbs_morphism_space[OF h] qbs_morphism_Mx[OF h] by (auto simp: qbs_Mx_to_X)
    hence "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (f -` A) = \<alpha> -` (f -` Ua)"
      by (simp add: pa)
    from pa this qbs_morphism_def have "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (f -` A) \<in> sets borel"
      by (simp add: vimage_comp \<open>\<forall>\<alpha>\<in>qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y\<close>)
    thus "f -` A \<inter> space (qbs_to_measure X) \<in> sets (qbs_to_measure X)"
      using sigma_Mx_def by(auto simp: sets_L space_L)
  qed (insert qbs_morphism_space[OF h], auto simp: space_L)
qed


abbreviation qbs_borel ("borel\<^sub>Q")  where "borel\<^sub>Q \<equiv> measure_to_qbs borel"
abbreviation qbs_count_space ("count'_space\<^sub>Q") where "qbs_count_space I \<equiv> measure_to_qbs (count_space I)"

declare [[coercion measure_to_qbs]]

lemma
  shows qbs_space_qbs_borel[simp]: "qbs_space borel\<^sub>Q = UNIV"
    and qbs_space_count_space[simp]: "qbs_space (qbs_count_space I) = I"
    and qbs_Mx_qbs_borel: "qbs_Mx borel\<^sub>Q = borel_measurable borel"
    and qbs_Mx_count_space: "qbs_Mx (qbs_count_space I) = borel \<rightarrow>\<^sub>M count_space I"
  by(simp_all add: qbs_space_R qbs_Mx_R)

(* Want to remove the following *)
lemma
  shows qbs_space_qbs_borel'[qbs]: "r \<in> qbs_space borel\<^sub>Q"
    and qbs_space_count_space_UNIV'[qbs]: "x \<in> qbs_space (qbs_count_space (UNIV :: (_ :: countable) set))"
  by simp_all

lemma qbs_Mx_is_morphisms: "qbs_Mx X = borel\<^sub>Q \<rightarrow>\<^sub>Q X"
proof safe
  fix \<alpha> :: "real \<Rightarrow> _"
  assume "\<alpha> \<in> borel\<^sub>Q \<rightarrow>\<^sub>Q X"
  have "id \<in> qbs_Mx borel\<^sub>Q" by (simp add: qbs_Mx_R)
  then have "\<alpha> \<circ> id \<in> qbs_Mx X"
    using qbs_morphism_Mx[OF \<open>\<alpha> \<in> borel\<^sub>Q \<rightarrow>\<^sub>Q X\<close>]
    by blast
  then show "\<alpha> \<in> qbs_Mx X" by simp
qed(auto intro!: qbs_morphismI simp: qbs_Mx_qbs_borel)

lemma exp_qbs_Mx': "qbs_Mx (exp_qbs X Y) = {g. case_prod g \<in> borel\<^sub>Q \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y}"
  by(auto simp:  qbs_Mx_qbs_borel comp_def qbs_Mx_is_morphisms split_beta' intro!:curry_preserves_morphisms)

lemma arg_swap_morphism':
  assumes "(\<lambda>g. f (\<lambda>w x. g x w)) \<in> exp_qbs X (exp_qbs W Y) \<rightarrow>\<^sub>Q Z"
  shows "f \<in> exp_qbs W (exp_qbs X Y) \<rightarrow>\<^sub>Q Z"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx (exp_qbs W (exp_qbs X Y))"
  then have "(\<lambda>((r,w),x). \<alpha> r w x) \<in> (borel\<^sub>Q \<Otimes>\<^sub>Q W) \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y"
    by(auto simp: qbs_Mx_is_morphisms dest: uncurry_preserves_morphisms)
  hence "(\<lambda>(r,w,x). \<alpha> r w x) \<in> borel\<^sub>Q \<Otimes>\<^sub>Q W \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y"
    by(auto intro!: qbs_morphism_cong'[where f="(\<lambda>((r,w),x). \<alpha> r w x) \<circ> (\<lambda>(x, y, z). ((x, y), z))" and g="\<lambda>(r,w,x). \<alpha> r w x"] qbs_morphism_comp[OF qbs_morphism_pair_assoc2])
  hence "(\<lambda>(r,x,w). \<alpha> r w x) \<in> borel\<^sub>Q \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q W \<rightarrow>\<^sub>Q Y"
    by(auto intro!: qbs_morphism_cong'[where f="(\<lambda>(r,w,x). \<alpha> r w x) \<circ> map_prod id (\<lambda>(x,y). (y,x))" and g="(\<lambda>(r,x,w). \<alpha> r w x)"] qbs_morphism_comp qbs_morphism_map_prod qbs_morphism_pair_swap)
  hence "(\<lambda>((r,x),w). \<alpha> r w x) \<in> (borel\<^sub>Q \<Otimes>\<^sub>Q X) \<Otimes>\<^sub>Q W \<rightarrow>\<^sub>Q Y"
    by(auto intro!: qbs_morphism_cong'[where f="(\<lambda>(r,x,w). \<alpha> r w x) \<circ> (\<lambda>((x, y), z). (x, y, z))" and g="\<lambda>((r,x),w). \<alpha> r w x"] qbs_morphism_comp[OF qbs_morphism_pair_assoc1])
  hence "(\<lambda>r x w. \<alpha> r w x) \<in> qbs_Mx (exp_qbs X (exp_qbs W Y))"
    by(auto simp: qbs_Mx_is_morphisms split_beta')
  from qbs_morphism_Mx[OF assms this] show "f \<circ> \<alpha> \<in> qbs_Mx Z"
    by(auto simp: comp_def)
qed

lemma qbs_Mx_subset_of_measurable: "qbs_Mx X \<subseteq> borel \<rightarrow>\<^sub>M qbs_to_measure X"
proof
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx X"
  show "\<alpha> \<in> borel \<rightarrow>\<^sub>M qbs_to_measure X"
  proof(rule measurableI)
    fix x
    show "\<alpha> x \<in> space (qbs_to_measure X)"
      using qbs_Mx_to_X \<open>\<alpha> \<in> qbs_Mx X\<close> by(simp add: space_L)
  next
    fix A
    assume "A \<in> sets (qbs_to_measure X)"
    then have "\<alpha> -`(qbs_space X) = UNIV"
      using \<open>\<alpha> \<in> qbs_Mx X\<close> qbs_Mx_to_X by(auto simp: sets_L)
    then show "\<alpha> -` A \<inter> space borel \<in> sets borel"
      using \<open>\<alpha> \<in> qbs_Mx X\<close> \<open>A \<in> sets (qbs_to_measure X)\<close>
      by(auto simp add: sigma_Mx_def sets_L)
  qed
qed

lemma L_max_of_measurables:
  assumes "space M = qbs_space X"
      and "qbs_Mx X \<subseteq> borel \<rightarrow>\<^sub>M M"
    shows "sets M \<subseteq> sets (qbs_to_measure X)"
proof
  fix U
  assume "U \<in> sets M"
  from sets.sets_into_space[OF this] in_mono[OF assms(2)] measurable_sets_borel[OF _ this]
  show "U \<in> sets (qbs_to_measure X)"
    using assms(1)
    by(auto intro!: exI[where x=U] simp: sigma_Mx_def sets_L)
qed


lemma qbs_Mx_are_measurable[simp,measurable]:
  assumes "\<alpha> \<in> qbs_Mx X"
  shows "\<alpha> \<in> borel \<rightarrow>\<^sub>M qbs_to_measure X"
  using assms qbs_Mx_subset_of_measurable by auto

lemma measure_to_qbs_cong_sets:
  assumes "sets M = sets N"
  shows "measure_to_qbs M = measure_to_qbs N"
  by(rule qbs_eqI) (simp add: qbs_Mx_R measurable_cong_sets[OF _ assms])

lemma lr_sets[simp]:
 "sets X \<subseteq> sets (qbs_to_measure (measure_to_qbs X))"
  unfolding sets_L
proof safe
  fix U
  assume "U \<in> sets X"
  then have "U \<inter> space X = U" by simp
  moreover have "\<forall>\<alpha>\<in>borel \<rightarrow>\<^sub>M X. \<alpha> -` U \<in> sets borel"
    using \<open>U \<in> sets X\<close> by(auto simp add: measurable_def)
  ultimately show "U \<in> sigma_Mx (measure_to_qbs X)"
    by(auto simp add: sigma_Mx_def qbs_Mx_R qbs_space_R)
qed

lemma(in standard_borel) lr_sets_ident[simp, measurable_cong]:
 "sets (qbs_to_measure (measure_to_qbs M)) = sets M"
  unfolding sets_L
proof safe
  fix V
  assume "V \<in> sigma_Mx (measure_to_qbs M)"
  then obtain U where H2: "V = U \<inter> space M" "\<And>\<alpha>::real \<Rightarrow> _. \<alpha>\<in>borel \<rightarrow>\<^sub>M M \<Longrightarrow> \<alpha> -` U \<in> sets borel"
    by(auto simp: sigma_Mx_def qbs_Mx_R qbs_space_R)
  consider "space M = {}" | "space M \<noteq> {}" by auto
  then show "V \<in> sets M"
  proof cases
    case 1
    then show ?thesis
      by(simp add: H2)
  next
    case 2
    have "from_real -` V = from_real -` (U \<inter> space M)" using H2 by auto
    also have "... = from_real -` U" using from_real_measurable'[OF 2] by(auto simp add: measurable_def) 
    finally have "to_real -` from_real -` U  \<inter> space M \<in> sets M"
      by (meson "2" H2(2) from_real_measurable' measurable_sets to_real_measurable)
    moreover have "to_real -` from_real -` U  \<inter> space M =  U \<inter> space M"
      by auto
    ultimately show ?thesis using H2 by simp
  qed
qed(insert lr_sets, auto simp: sets_L)

corollary sets_lr_polish_borel[simp, measurable_cong]: "sets (qbs_to_measure qbs_borel) = sets (borel :: (_ :: polish_space) measure)"
  by(auto intro!: standard_borel.lr_sets_ident standard_borel_ne.standard_borel)

corollary sets_lr_count_space[simp, measurable_cong]: "sets (qbs_to_measure (qbs_count_space (UNIV :: (_ :: countable) set))) = sets (count_space UNIV)"
  by(rule standard_borel.lr_sets_ident) (auto intro!:  standard_borel_ne.standard_borel)

subsubsection \<open> The Adjunction \<close>
lemma lr_adjunction_correspondence :
 "X \<rightarrow>\<^sub>Q (measure_to_qbs Y) = (qbs_to_measure X) \<rightarrow>\<^sub>M Y"
proof safe
(* \<subseteq> *)
  fix f
  assume "f \<in> X \<rightarrow>\<^sub>Q (measure_to_qbs Y)"
  show "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y"
  proof(rule measurableI)
    fix x
    assume "x \<in> space (qbs_to_measure X)"
    thus "f x \<in> space Y"
      using qbs_morphism_space[OF \<open>f \<in> X \<rightarrow>\<^sub>Q (measure_to_qbs Y)\<close>]
      by (auto simp: qbs_space_R space_L)
  next
    fix A
    assume "A \<in> sets Y"
    have "\<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx (measure_to_qbs Y)"
      using qbs_morphism_Mx[OF \<open>f \<in> X \<rightarrow>\<^sub>Q (measure_to_qbs Y)\<close>] by auto
    hence "\<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> borel \<rightarrow>\<^sub>M Y" by (simp add: qbs_Mx_R)
    hence "\<forall>\<alpha> \<in> qbs_Mx X. \<alpha> -` (f -` A) \<in> sets borel"
      using \<open>A\<in> sets Y\<close> measurable_sets_borel vimage_comp by metis
    thus "f -` A \<inter> space (qbs_to_measure X) \<in> sets (qbs_to_measure X)"
      using sigma_Mx_def by (auto simp: space_L sets_L)
  qed
   
(* \<supseteq> *)
next
  fix f
  assume "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y"
  show "f \<in> X \<rightarrow>\<^sub>Q measure_to_qbs Y"
  proof(rule qbs_morphismI)
    fix \<alpha>
    assume "\<alpha> \<in> qbs_Mx X"
    have "f \<circ> \<alpha> \<in> borel \<rightarrow>\<^sub>M Y"
    proof(rule measurableI)
      fix x :: real
      from \<open>\<alpha> \<in> qbs_Mx X\<close> qbs_Mx_to_X have "\<alpha> x \<in> qbs_space X" by auto
      hence "\<alpha> x \<in> space (qbs_to_measure X)" by (simp add: space_L)
      thus "(f \<circ> \<alpha>) x \<in> space Y"
        using \<open>f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y\<close>
        by (metis comp_def measurable_space)
    next
      fix A
      assume "A \<in> sets Y"
      from \<open>f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y\<close> measurable_sets this measurable_def
      have "f -` A \<inter> space (qbs_to_measure X) \<in> sets (qbs_to_measure X)"
        by blast
      hence "f -` A \<inter> qbs_space X \<in> sigma_Mx X" by (simp add: sets_L space_L)
      then have "\<exists>V. f -` A \<inter> qbs_space X = V \<inter> qbs_space X \<and> (\<forall>\<beta>\<in> qbs_Mx X. \<beta> -` V \<in> sets borel)"
        by (simp add: sigma_Mx_def)
      then obtain V where h:"f -` A \<inter> qbs_space X = V \<inter> qbs_space X \<and> (\<forall>\<beta>\<in> qbs_Mx X. \<beta> -` V \<in> sets borel)" by auto
      have 1:"\<alpha> -` (f -` A) = \<alpha> -` (f -` A \<inter> qbs_space X)"
        using \<open>\<alpha> \<in> qbs_Mx X\<close> qbs_Mx_to_X by blast
      have 2:"\<alpha> -` (V \<inter> qbs_space X) = \<alpha> -` V"
        using \<open>\<alpha> \<in> qbs_Mx X\<close> qbs_Mx_to_X by blast
      from 1 2 h have "(f \<circ> \<alpha>) -` A = \<alpha> -` V" by (simp add: vimage_comp)
      from this h \<open>\<alpha> \<in> qbs_Mx X \<close>show "(f \<circ> \<alpha>) -` A \<inter> space borel \<in> sets borel" by simp
    qed
    thus "f \<circ> \<alpha> \<in> qbs_Mx (measure_to_qbs Y)"
      by(simp add:qbs_Mx_R)
  qed
qed

lemma(in standard_borel) standard_borel_r_full_faithful:
  "M \<rightarrow>\<^sub>M Y = measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y"
proof
  have "measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y \<subseteq> qbs_to_measure (measure_to_qbs M) \<rightarrow>\<^sub>M qbs_to_measure (measure_to_qbs Y)"
    by (simp add: l_preserves_morphisms)
  also have "... = M \<rightarrow>\<^sub>M qbs_to_measure (measure_to_qbs Y)"
    using measurable_cong_sets by auto
  also have "... \<subseteq> M \<rightarrow>\<^sub>M Y"
    by(rule measurable_mono[OF lr_sets]) (simp_all add: qbs_space_R space_L)
  finally show "measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y \<subseteq> M \<rightarrow>\<^sub>M Y" .
qed(rule r_preserves_morphisms)

lemma qbs_morphism_dest:
  assumes "f \<in> X \<rightarrow>\<^sub>Q measure_to_qbs Y"
  shows "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y"
  using assms lr_adjunction_correspondence by auto

lemma(in standard_borel) qbs_morphism_dest:
  assumes "k \<in> measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y"
  shows "k \<in> M \<rightarrow>\<^sub>M Y"
  using standard_borel_r_full_faithful assms by auto

lemma qbs_morphism_measurable_intro:
  assumes "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y"
  shows "f \<in> X \<rightarrow>\<^sub>Q measure_to_qbs Y"
  using assms lr_adjunction_correspondence by auto

lemma(in standard_borel) qbs_morphism_measurable_intro:
  assumes "k \<in> M \<rightarrow>\<^sub>M Y"
  shows "k \<in> measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y"
  using standard_borel_r_full_faithful assms by auto

lemma r_preserves_product :
  "measure_to_qbs (X \<Otimes>\<^sub>M Y) = measure_to_qbs X \<Otimes>\<^sub>Q measure_to_qbs Y"
  by(auto intro!: qbs_eqI simp: measurable_pair_iff pair_qbs_Mx qbs_Mx_R)

lemma l_product_sets:
  "sets (qbs_to_measure X \<Otimes>\<^sub>M qbs_to_measure Y) \<subseteq> sets (qbs_to_measure (X \<Otimes>\<^sub>Q Y))"
proof(rule sets_pair_in_sets)
  fix A B
  assume h:"A \<in> sets (qbs_to_measure X)" "B \<in> sets (qbs_to_measure Y)"
  then obtain Ua Ub where hu:
   "A = Ua \<inter> qbs_space X" "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets borel"
   "B = Ub \<inter> qbs_space Y" "\<forall>\<alpha>\<in>qbs_Mx Y. \<alpha> -` Ub \<in> sets borel"
    by(auto simp add: sigma_Mx_def sets_L)
  show "A \<times> B \<in> sets (qbs_to_measure (X \<Otimes>\<^sub>Q Y))"
  proof -
    have "A \<times> B = Ua \<times> Ub \<inter> qbs_space (X \<Otimes>\<^sub>Q Y) \<and> (\<forall>\<alpha>\<in>qbs_Mx (X \<Otimes>\<^sub>Q Y). \<alpha> -` (Ua \<times> Ub) \<in> sets borel)"
      using hu by(auto simp add: vimage_Times pair_qbs_space pair_qbs_Mx)
    thus ?thesis
      by(auto simp add: sigma_Mx_def sets_L intro!: exI[where x="Ua \<times> Ub"])
  qed
qed

corollary qbs_borel_prod: "qbs_borel \<Otimes>\<^sub>Q qbs_borel = (qbs_borel :: ('a::second_countable_topology \<times> 'b::second_countable_topology) quasi_borel)"
  by(simp add: r_preserves_product[symmetric] borel_prod)

corollary qbs_count_space_prod: "qbs_count_space (UNIV :: ('a :: countable) set) \<Otimes>\<^sub>Q qbs_count_space (UNIV :: ('b :: countable) set) = qbs_count_space UNIV"
  by(auto simp: r_preserves_product[symmetric] count_space_prod)

lemma r_preserves_product': "measure_to_qbs (\<Pi>\<^sub>M i\<in>I. M i) = (\<Pi>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
proof(rule qbs_eqI)
  show "qbs_Mx (measure_to_qbs (Pi\<^sub>M I M)) = qbs_Mx (\<Pi>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
  proof safe
    fix f :: "real \<Rightarrow> _"
    assume "f \<in> qbs_Mx (measure_to_qbs (Pi\<^sub>M I M))"
    with measurable_space[of f borel "Pi\<^sub>M I M"] show "f \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
      by(auto simp: qbs_Mx_R PiQ_Mx space_PiM  intro!:ext[of "\<lambda>r. f r _"])
  next
    fix f :: "real \<Rightarrow> _"
    assume "f \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
    then have "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>r. f r i) \<in> borel \<rightarrow>\<^sub>M M i" "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>r. f r i) = (\<lambda>r. undefined)"
      by (auto simp: qbs_Mx_R PiQ_Mx)
    with measurable_space[OF this(1)] fun_cong[OF this(2)] show "f \<in> qbs_Mx (measure_to_qbs (Pi\<^sub>M I M))"
      by(auto intro!: measurable_PiM_single' simp: qbs_Mx_R)
  qed
qed

lemma PiQ_qbs_borel:
  "(\<Pi>\<^sub>Q i::('a:: countable)\<in>UNIV. (qbs_borel :: ('b::second_countable_topology quasi_borel))) = qbs_borel"
  by(simp add: r_preserves_product'[symmetric] measure_to_qbs_cong_sets[OF sets_PiM_equal_borel])

lemma qbs_morphism_from_countable:
  fixes X :: "'a quasi_borel"
  assumes "countable (qbs_space X)"
          "qbs_Mx X \<subseteq> borel \<rightarrow>\<^sub>M count_space (qbs_space X)"
      and "\<And>i. i \<in> qbs_space X \<Longrightarrow> f i \<in> qbs_space Y"
    shows "f \<in> X \<rightarrow>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx X"
  then have [measurable]: "\<alpha> \<in> borel \<rightarrow>\<^sub>M count_space (qbs_space X)"
    using assms(2) ..
  define k :: "'a \<Rightarrow> real \<Rightarrow> _"
    where "k \<equiv> (\<lambda>i _. f i)"
  have "f \<circ> \<alpha> = (\<lambda>r. k (\<alpha> r) r)"
    by(auto simp add: k_def)
  also have "... \<in> qbs_Mx Y"
    by(rule qbs_closed3_dest2[OF assms(1)]) (use assms(3) k_def in simp_all)
  finally show "f \<circ> \<alpha> \<in> qbs_Mx Y" .
qed

corollary qbs_morphism_count_space':
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> qbs_space Y" "countable I"
  shows "f \<in> qbs_count_space I \<rightarrow>\<^sub>Q Y"
  using assms by(auto intro!: qbs_morphism_from_countable simp: qbs_Mx_R)

corollary qbs_morphism_count_space:
  assumes "\<And>i. f i \<in> qbs_space Y"
  shows "f \<in> qbs_count_space (UNIV :: (_ :: countable) set) \<rightarrow>\<^sub>Q Y"
  using assms by(auto intro!: qbs_morphism_from_countable simp: qbs_Mx_R)

lemma [qbs]:
  shows not_qbs_pred: "Not \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q qbs_count_space UNIV"
    and or_qbs_pred: "(\<or>) \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and and_qbs_pred: "(\<and>) \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and implies_qbs_pred: "(\<longrightarrow>) \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and iff_qbs_pred: "(\<longleftrightarrow>) \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
  by(auto intro!: qbs_morphism_count_space)

lemma [qbs]:
  shows less_count_qbs_pred: "(<) \<in> qbs_count_space (UNIV :: (_ :: countable) set) \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and le_count_qbs_pred: "(\<le>) \<in> qbs_count_space (UNIV :: (_ :: countable) set) \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and eq_count_qbs_pred: "(=) \<in> qbs_count_space (UNIV :: (_ :: countable) set) \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and plus_count_qbs_morphism: "(+) \<in> qbs_count_space (UNIV :: (_ :: countable) set) \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and minus_count_qbs_morphism: "(-) \<in> qbs_count_space (UNIV :: (_ :: countable) set) \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and mult_count_qbs_morphism: "(*) \<in> qbs_count_space (UNIV :: (_ :: countable) set) \<rightarrow>\<^sub>Q exp_qbs (qbs_count_space UNIV) (qbs_count_space UNIV)"
    and Suc_qbs_morphism: "Suc \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q qbs_count_space UNIV"
  by(auto intro!: qbs_morphism_count_space)

lemma qbs_morphism_product_iff:
 "f \<in> X \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i :: (_ :: countable)\<in>UNIV. Y) \<longleftrightarrow> f \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV \<Rightarrow>\<^sub>Q Y"
proof
  assume h:"f \<in> X \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>UNIV. Y)"
  show "f \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV \<Rightarrow>\<^sub>Q Y"
    by(rule arg_swap_morphism, rule  qbs_morphism_count_space) (simp add: qbs_morphism_component_singleton'[OF h qbs_morphism_ident'])
next
  assume "f \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV \<Rightarrow>\<^sub>Q Y"
  from qbs_morphism_space[OF arg_swap_morphism[OF this]]
  show "f \<in> X \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>UNIV. Y)"
    by(auto intro!: product_qbs_canonical1[where f="(\<lambda>i x. f x i)"])
qed

lemma qbs_morphism_pair_countable1:
  assumes "countable (qbs_space X)"
          "qbs_Mx X \<subseteq> borel \<rightarrow>\<^sub>M count_space (qbs_space X)"
      and "\<And>i. i \<in> qbs_space X \<Longrightarrow> f i \<in> Y \<rightarrow>\<^sub>Q Z"
    shows "(\<lambda>(x,y). f x y) \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  by(auto intro!: uncurry_preserves_morphisms qbs_morphism_from_countable[OF assms(1,2)] assms(3))

lemma qbs_morphism_pair_countable2:
  assumes "countable (qbs_space Y)"
          "qbs_Mx Y \<subseteq> borel \<rightarrow>\<^sub>M count_space (qbs_space Y)"
      and "\<And>i. i \<in> qbs_space Y \<Longrightarrow> (\<lambda>x. f x i) \<in> X \<rightarrow>\<^sub>Q Z"
    shows "(\<lambda>(x,y). f x y) \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  by(auto intro!: qbs_morphism_pair_swap[of "case_prod (\<lambda>x y. f y x)",simplified] qbs_morphism_pair_countable1 assms)

corollary qbs_morphism_pair_count_space1:
  assumes "\<And>i. f i \<in> Y \<rightarrow>\<^sub>Q Z"
  shows "(\<lambda>(x,y). f x y) \<in> qbs_count_space (UNIV :: ('a :: countable) set) \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  by(auto intro!: qbs_morphism_pair_countable1 simp: qbs_Mx_R assms)

corollary qbs_morphism_pair_count_space2:
  assumes "\<And>i. (\<lambda>x. f x i) \<in> X \<rightarrow>\<^sub>Q Z"
  shows "(\<lambda>(x,y). f x y) \<in> X \<Otimes>\<^sub>Q qbs_count_space (UNIV :: ('a :: countable) set) \<rightarrow>\<^sub>Q Z"
  by(auto intro!: qbs_morphism_pair_countable2 simp: qbs_Mx_R assms)

lemma qbs_morphism_compose_countable':
  assumes [qbs]:"\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. f i x) \<in> X \<rightarrow>\<^sub>Q Y" "g \<in> X \<rightarrow>\<^sub>Q qbs_count_space I" "countable I"
  shows "(\<lambda>x. f (g x) x) \<in> X \<rightarrow>\<^sub>Q Y"
proof -
  have [qbs]:"f \<in> qbs_count_space I \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q Y"
    by(auto intro!: qbs_morphism_count_space' simp: assms(3))
  show ?thesis
    by simp
qed

lemma qbs_morphism_compose_countable:
  assumes [simp]:"\<And>i::'i::countable. (\<lambda>x. f i x) \<in> X \<rightarrow>\<^sub>Q Y" "g \<in> X \<rightarrow>\<^sub>Q (qbs_count_space UNIV)"
  shows "(\<lambda>x. f (g x) x) \<in> X \<rightarrow>\<^sub>Q Y"
  by(rule qbs_morphism_compose_countable'[of UNIV f]) simp_all

lemma qbs_morphism_op:
  assumes "case_prod f \<in> X \<Otimes>\<^sub>M Y \<rightarrow>\<^sub>M Z"
  shows "f \<in> measure_to_qbs X \<rightarrow>\<^sub>Q measure_to_qbs Y \<Rightarrow>\<^sub>Q measure_to_qbs Z"
  using r_preserves_morphisms assms
  by(fastforce simp: r_preserves_product[symmetric] intro!: curry_preserves_morphisms)

lemma [qbs]:
  shows plus_qbs_morphism: "(+) \<in> (qbs_borel :: (_::{second_countable_topology, topological_monoid_add}) quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and plus_ereal_qbs_morphism: "(+) \<in> (qbs_borel :: ereal quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and diff_qbs_morphism: "(-) \<in> (qbs_borel :: (_::{second_countable_topology, real_normed_vector}) quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and diff_ennreal_qbs_morphism: "(-) \<in> (qbs_borel :: ennreal quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and diff_ereal_qbs_morphism: "(-) \<in> (qbs_borel :: ereal quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and times_qbs_morphism: "(*) \<in> (qbs_borel :: (_::{second_countable_topology, real_normed_algebra}) quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and times_ennreal_qbs_morphism: "(*) \<in> (qbs_borel :: ennreal quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and times_ereal_qbs_morphism: "(*) \<in> (qbs_borel :: ereal quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and divide_qbs_morphism: "(/) \<in> (qbs_borel :: (_::{second_countable_topology, real_normed_div_algebra}) quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and divide_ennreal_qbs_morphism: "(/) \<in> (qbs_borel :: ennreal quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and divide_ereal_qbs_morphism: "(/) \<in> (qbs_borel :: ereal quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and log_qbs_morphism: "log \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and root_qbs_morphism: "root \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and scaleR_qbs_morphism: "(*\<^sub>R) \<in> qbs_borel \<rightarrow>\<^sub>Q (qbs_borel :: (_::{second_countable_topology, real_normed_vector}) quasi_borel) \<Rightarrow>\<^sub>Q qbs_borel"
    and qbs_morphism_inner: "(\<bullet>) \<in> qbs_borel \<rightarrow>\<^sub>Q (qbs_borel :: (_::{second_countable_topology, real_inner}) quasi_borel) \<Rightarrow>\<^sub>Q qbs_borel"
    and dist_qbs_morphism: "dist \<in> (qbs_borel :: (_::{second_countable_topology, metric_space}) quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and powr_qbs_morphism: "(powr) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q (qbs_borel :: real quasi_borel)"
    and max_qbs_morphism: "(max :: (_ :: {second_countable_topology, linorder_topology}) \<Rightarrow> _ \<Rightarrow> _) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and min_qbs_morphism: "(min :: (_ :: {second_countable_topology, linorder_topology}) \<Rightarrow> _ \<Rightarrow> _) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and sup_qbs_morphism: "(sup :: (_ :: {lattice,second_countable_topology, linorder_topology}) \<Rightarrow> _ \<Rightarrow> _) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and inf_qbs_morphism: "(inf :: (_ :: {lattice,second_countable_topology, linorder_topology}) \<Rightarrow> _ \<Rightarrow> _) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
    and less_qbs_pred: "(<) \<in> (qbs_borel :: _ ::{second_countable_topology, linorder_topology} quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_count_space UNIV"
    and eq_qbs_pred: "(=) \<in> (qbs_borel :: _ ::{second_countable_topology, linorder_topology} quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_count_space UNIV"
    and le_qbs_pred: "(\<le>) \<in> (qbs_borel :: _ ::{second_countable_topology, linorder_topology} quasi_borel) \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_count_space UNIV"
  by(auto intro!: qbs_morphism_op)

lemma [qbs]:
  shows abs_real_qbs_morphism: "abs \<in> (qbs_borel :: real quasi_borel) \<rightarrow>\<^sub>Q qbs_borel"
    and abs_ereal_qbs_morphism: "abs \<in> (qbs_borel :: ereal quasi_borel) \<rightarrow>\<^sub>Q qbs_borel"
    and real_floor_qbs_morphism: "(floor :: real \<Rightarrow> int) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_count_space UNIV"
    and real_ceiling_qbs_morphism: "(ceiling :: real \<Rightarrow> int) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_count_space UNIV"
    and exp_qbs_morphism: "(exp::'a::{real_normed_field,banach}\<Rightarrow>'a) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and ln_qbs_morphism: "ln \<in> (qbs_borel :: real quasi_borel) \<rightarrow>\<^sub>Q qbs_borel"
    and sqrt_qbs_morphism: "sqrt \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and of_real_qbs_morphism: "(of_real :: _ \<Rightarrow> (_::real_normed_algebra)) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and sin_qbs_morphism: "(sin :: _ \<Rightarrow> (_::{real_normed_field,banach})) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and cos_qbs_morphism: "(cos :: _ \<Rightarrow> (_::{real_normed_field,banach})) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and arctan_qbs_morphism: "arctan \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and Re_qbs_morphism: "Re \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and Im_qbs_morphism: "Im \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and sgn_qbs_morphism: "(sgn::_::real_normed_vector \<Rightarrow> _) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and norm_qbs_morphism: "norm \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and invers_qbs_morphism: "(inverse :: _ \<Rightarrow> (_ ::real_normed_div_algebra)) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and invers_ennreal_qbs_morphism: "(inverse :: _ \<Rightarrow> ennreal) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and invers_ereal_qbs_morphism: "(inverse :: _ \<Rightarrow> ereal) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and uminus_qbs_morphism: "(uminus :: _ \<Rightarrow> (_::{second_countable_topology, real_normed_vector})) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and ereal_qbs_morphism: "ereal \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and real_of_ereal_qbs_morphism: "real_of_ereal \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and enn2ereal_qbs_morphism: "enn2ereal \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and e2ennreal_qbs_morphism: "e2ennreal \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and ennreal_qbs_morphism: "ennreal \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and qbs_morphism_nth: "(\<lambda>x::real^'n. x $ i) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and qbs_morphism_product_candidate: "\<And>i. (\<lambda>x. x i) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
    and uminus_ereal_qbs_morphism: "(uminus :: _ \<Rightarrow> ereal) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
  by(auto intro!: set_mp[OF r_preserves_morphisms])

lemma qbs_morphism_sum:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology, topological_comm_monoid_add}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_suminf_order:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{complete_linorder, second_countable_topology, linorder_topology, topological_comm_monoid_add}"
  assumes "\<And>i. f i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows " (\<lambda>x. \<Sum>i. f i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_prod:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology, real_normed_field}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_Min:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i \<in> X \<rightarrow>\<^sub>Q qbs_borel) \<Longrightarrow> (\<lambda>x. Min ((\<lambda>i. f i x)`I) :: 'b::{second_countable_topology, linorder_topology}) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_Max:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i \<in> X \<rightarrow>\<^sub>Q qbs_borel) \<Longrightarrow> (\<lambda>x. Max ((\<lambda>i. f i x)`I) :: 'b::{second_countable_topology, linorder_topology}) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_Max2:
  fixes f::"_ \<Rightarrow> _ \<Rightarrow> 'a::{second_countable_topology, dense_linorder, linorder_topology}"
  shows "finite I \<Longrightarrow> (\<And>i. f i \<in> X \<rightarrow>\<^sub>Q qbs_borel) \<Longrightarrow> (\<lambda>x. Max{f i x |i. i \<in> I}) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  by(simp add: lr_adjunction_correspondence)

lemma [qbs]:
  shows qbs_morphism_liminf: "liminf \<in> (qbs_count_space UNIV \<Rightarrow>\<^sub>Q qbs_borel) \<Rightarrow>\<^sub>Q (qbs_borel :: 'a :: {complete_linorder, second_countable_topology, linorder_topology} quasi_borel)"
    and qbs_morphism_limsup: "limsup \<in> (qbs_count_space UNIV \<Rightarrow>\<^sub>Q qbs_borel) \<Rightarrow>\<^sub>Q (qbs_borel :: 'a :: {complete_linorder, second_countable_topology, linorder_topology} quasi_borel)"
    and qbs_morphism_lim: "lim \<in> (qbs_count_space UNIV \<Rightarrow>\<^sub>Q qbs_borel) \<Rightarrow>\<^sub>Q (qbs_borel :: 'a :: {complete_linorder, second_countable_topology, linorder_topology} quasi_borel)"
proof(safe intro!: qbs_morphismI)
  fix f :: "real \<Rightarrow> nat \<Rightarrow> 'a"
  assume "f \<in> qbs_Mx (count_space\<^sub>Q UNIV \<Rightarrow>\<^sub>Q borel\<^sub>Q)"
  then have [measurable]:"\<And>i. (\<lambda>r. f r i) \<in> borel_measurable borel"
    by(auto simp: qbs_Mx_is_morphisms) (metis PiQ_qbs_borel measurable_product_then_coordinatewise qbs_Mx_is_morphisms qbs_Mx_qbs_borel qbs_morphism_product_iff)
  show "liminf \<circ> f \<in> qbs_Mx borel\<^sub>Q" "limsup \<circ> f \<in> qbs_Mx borel\<^sub>Q" "lim \<circ> f \<in> qbs_Mx borel\<^sub>Q"
    by(auto simp: qbs_Mx_is_morphisms lr_adjunction_correspondence comp_def)
qed

lemma qbs_morphism_SUP:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> _::{complete_linorder, linorder_topology, second_countable_topology}"
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> F i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. \<Squnion> i\<in>I. F i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_INF:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> _::{complete_linorder, linorder_topology, second_countable_topology}"
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> F i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. \<Sqinter> i\<in>I. F i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_cSUP:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> 'a::{conditionally_complete_linorder, linorder_topology, second_countable_topology}"
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> F i \<in> X \<rightarrow>\<^sub>Q qbs_borel" "\<And>x. x \<in> qbs_space X \<Longrightarrow> bdd_above ((\<lambda>i. F i x) ` I)"
  shows "(\<lambda>x. \<Squnion> i\<in>I. F i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence space_L)

lemma qbs_morphism_cINF:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> 'a::{conditionally_complete_linorder, linorder_topology, second_countable_topology}"
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> F i \<in> X \<rightarrow>\<^sub>Q qbs_borel" "\<And>x. x \<in> qbs_space X \<Longrightarrow> bdd_below ((\<lambda>i. F i x) ` I)"
  shows "(\<lambda>x. \<Sqinter> i\<in>I. F i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence space_L)

lemma qbs_morphism_lim_metric:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "\<And>i. f i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. lim (\<lambda>i. f i x)) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_LIMSEQ_metric:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: metric_space"
  assumes "\<And>i. f i \<in> X \<rightarrow>\<^sub>Q qbs_borel" "\<And>x. x \<in> qbs_space X \<Longrightarrow> (\<lambda>i. f i x) \<longlonglongrightarrow> g x"
  shows "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using borel_measurable_LIMSEQ_metric[where M="qbs_to_measure X"] assms
  by(auto simp add: lr_adjunction_correspondence space_L)

lemma power_qbs_morphism[qbs]:
 "(power :: (_ ::{power,real_normed_algebra}) \<Rightarrow> nat \<Rightarrow> _) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_count_space UNIV \<Rightarrow>\<^sub>Q qbs_borel"
  by(rule arg_swap_morphism) (auto intro!: qbs_morphism_count_space set_mp[OF r_preserves_morphisms])

lemma power_ennreal_qbs_morphism[qbs]:
 "(power :: ennreal \<Rightarrow> nat \<Rightarrow> _) \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_count_space UNIV \<Rightarrow>\<^sub>Q qbs_borel"
  by(rule arg_swap_morphism) (auto intro!: qbs_morphism_count_space set_mp[OF r_preserves_morphisms])

lemma qbs_morphism_compw: "(^^) \<in> (X \<Rightarrow>\<^sub>Q X) \<rightarrow>\<^sub>Q  qbs_count_space UNIV \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q X)"
proof(rule arg_swap_morphism,rule qbs_morphism_count_space)
  fix n
  show "(\<lambda>y. y ^^ n) \<in> X \<Rightarrow>\<^sub>Q X \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q X"
    by(induction n) simp_all
qed

lemma qbs_morphism_compose_n[qbs]:
  assumes [qbs]: "f \<in> X \<rightarrow>\<^sub>Q X"
  shows "(\<lambda>n. f^^n) \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q X"
proof(intro qbs_morphism_count_space)
  fix n
  show "f ^^ n \<in> X \<rightarrow>\<^sub>Q X"
    by (induction n) simp_all
qed

lemma qbs_morphism_compose_n':
  assumes "f \<in> X \<rightarrow>\<^sub>Q X"
  shows "f^^n \<in> X \<rightarrow>\<^sub>Q X"
  using qbs_morphism_space[OF qbs_morphism_compose_n[OF assms]] by(simp add: exp_qbs_space qbs_space_R)

lemma qbs_morphism_uminus_eq_ereal[simp]:
  "(\<lambda>x. - f x :: ereal) \<in> X \<rightarrow>\<^sub>Q qbs_borel \<longleftrightarrow> f \<in> X \<rightarrow>\<^sub>Q qbs_borel" (is "?l = ?r")
  by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_ereal_iff:
  shows "(\<lambda>x. ereal (f x)) \<in> X \<rightarrow>\<^sub>Q qbs_borel\<longleftrightarrow> f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  by(simp add: borel_measurable_ereal_iff lr_adjunction_correspondence)

lemma qbs_morphism_ereal_sum:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_ereal_prod:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_extreal_suminf:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. f i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. (\<Sum>i. f i x)) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_ennreal_iff:
  assumes "\<And>x. x \<in> qbs_space X \<Longrightarrow> 0 \<le> f x"
  shows "(\<lambda>x. ennreal (f x)) \<in> X \<rightarrow>\<^sub>Q qbs_borel \<longleftrightarrow> f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using borel_measurable_ennreal_iff[where M="qbs_to_measure X"] assms
  by(simp add: space_L lr_adjunction_correspondence)

lemma qbs_morphism_prod_ennreal:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(simp add: space_L lr_adjunction_correspondence)

lemma count_space_qbs_morphism:
 "f \<in> qbs_count_space (UNIV :: 'a set) \<rightarrow>\<^sub>Q qbs_borel"
  by(auto intro!: set_mp[OF r_preserves_morphisms])

declare count_space_qbs_morphism[where 'a="_ :: countable",qbs]

lemma count_space_count_space_qbs_morphism:
 "f \<in> qbs_count_space (UNIV :: (_ :: countable) set) \<rightarrow>\<^sub>Q  qbs_count_space (UNIV :: (_ :: countable) set)"
  by(auto intro!: set_mp[OF r_preserves_morphisms])

lemma qbs_morphism_case_nat':
  assumes [qbs]: "i = 0 \<Longrightarrow> f \<in> X \<rightarrow>\<^sub>Q Y"
    "\<And>j. i = Suc j \<Longrightarrow> (\<lambda>x. g x j) \<in> X \<rightarrow>\<^sub>Q Y"
  shows "(\<lambda>x. case_nat (f x) (g x) i) \<in> X \<rightarrow>\<^sub>Q Y"
  by (cases i) simp_all

lemma qbs_morphism_case_nat[qbs]:
  "case_nat \<in> X \<rightarrow>\<^sub>Q (qbs_count_space UNIV \<Rightarrow>\<^sub>Q X) \<Rightarrow>\<^sub>Q qbs_count_space UNIV \<Rightarrow>\<^sub>Q X"
  by(rule curry_preserves_morphisms, rule arg_swap_morphism) (auto intro!: qbs_morphism_count_space qbs_morphism_case_nat')


lemma qbs_morphism_case_nat'':
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y" "g \<in> X \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>UNIV. Y)"
  shows "(\<lambda>x. case_nat (f x) (g x)) \<in> X \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>UNIV. Y)"
  using assms by (simp add: qbs_morphism_product_iff)

lemma qbs_morphism_rec_nat[qbs]: "rec_nat \<in> X \<rightarrow>\<^sub>Q (count_space UNIV \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q X) \<Rightarrow>\<^sub>Q count_space UNIV \<Rightarrow>\<^sub>Q X"
proof(rule curry_preserves_morphisms,rule arg_swap_morphism,rule qbs_morphism_count_space)
  fix n
  show "(\<lambda>y. rec_nat (fst y) (snd y) n) \<in> X \<Otimes>\<^sub>Q (qbs_count_space UNIV \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q X) \<rightarrow>\<^sub>Q X"
    by (induction n) simp_all
qed

lemma qbs_morphism_Max_nat:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "\<And>i. P i \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV"
  shows "(\<lambda>x. Max {i. P i x}) \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_Min_nat:
  fixes P :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "\<And>i. P i \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV"
  shows "(\<lambda>x. Min {i. P i x}) \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV"
  using assms by(simp add: lr_adjunction_correspondence)

lemma qbs_morphism_sum_nat:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> nat"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in>X \<rightarrow>\<^sub>Q qbs_count_space UNIV"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV"
  using assms by(simp add: lr_adjunction_correspondence)


lemma qbs_morphism_case_enat':
  assumes f[qbs]: "f \<in> X \<rightarrow>\<^sub>Q qbs_count_space UNIV" and [qbs]: "\<And>i. g i \<in> X \<rightarrow>\<^sub>Q Y" "h \<in> X \<rightarrow>\<^sub>Q Y"
  shows "(\<lambda>x. case f x of enat i \<Rightarrow> g i x | \<infinity> \<Rightarrow> h x) \<in> X \<rightarrow>\<^sub>Q Y"
proof (rule qbs_morphism_compose_countable[OF _ f])
  fix i                 
  show "(\<lambda>x. case i of enat i \<Rightarrow> g i x | \<infinity> \<Rightarrow> h x) \<in> X \<rightarrow>\<^sub>Q Y"
    by (cases i) simp_all
qed

lemma qbs_morphism_case_enat[qbs]: "case_enat \<in> qbs_space ((qbs_count_space UNIV \<Rightarrow>\<^sub>Q X) \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q qbs_count_space UNIV \<Rightarrow>\<^sub>Q X)"
proof -
  note qbs_morphism_case_enat'[qbs]
  show ?thesis
  by(auto intro!: curry_preserves_morphisms,rule qbs_morphismI) (simp add: qbs_Mx_is_morphisms comp_def, qbs, simp_all)
qed

lemma qbs_morphism_restrict[qbs]:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> X \<rightarrow>\<^sub>Q (Y i)"
  shows "(\<lambda>x. \<lambda>i\<in>I. f i x) \<in> X \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>I. Y i)"
  using assms by(auto intro!: product_qbs_canonical1)

lemma If_qbs_morphism[qbs]: "If \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q X"
proof(rule qbs_morphismI)
  show "\<alpha> \<in> qbs_Mx (count_space\<^sub>Q UNIV) \<Longrightarrow> If \<circ> \<alpha> \<in> qbs_Mx (X \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q X)" for \<alpha>
    by(auto intro!: qbs_Mx_indicat[where S="{r. \<alpha> (_ (_ r))}",simplified] simp: qbs_Mx_count_space exp_qbs_Mx)
qed

lemma normal_density_qbs[qbs]: "normal_density \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
proof -
  have [simp]:"normal_density = (\<lambda>\<mu> \<sigma> x. 1 / sqrt (2 * pi * \<sigma>\<^sup>2) * exp (-(x - \<mu>)\<^sup>2/ (2 * \<sigma>\<^sup>2)))"
    by standard+ (auto simp: normal_density_def)
  show ?thesis
    by simp
qed

lemma erlang_density_qbs[qbs]: "erlang_density \<in> qbs_count_space UNIV \<rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q qbs_borel"
proof -
  have [simp]: "erlang_density = (\<lambda>k l x. (if x < 0 then 0 else (l^(Suc k) * x^k * exp (- l * x)) / fact k))"
    by standard+ (auto simp: erlang_density_def)
  show ?thesis
    by simp
qed

lemma list_nil_qbs[qbs]: "[] \<in> qbs_space (list_qbs X)"
  by(simp add: list_qbs_space)

lemma list_cons_qbs_morphism: "list_cons \<in> X \<rightarrow>\<^sub>Q (list_of X) \<Rightarrow>\<^sub>Q (list_of X)"
proof(intro curry_preserves_morphisms pair_qbs_morphismI)
  fix \<alpha> \<beta>
  assume h:"\<alpha> \<in> qbs_Mx X"
           "\<beta> \<in> qbs_Mx (list_of X)"
  then obtain \<gamma> f where hf:
   "\<beta> = (\<lambda>r. (f r, \<gamma> (f r) r))" "f \<in> borel \<rightarrow>\<^sub>M count_space UNIV" "\<And>i. i \<in> range f \<Longrightarrow> \<gamma> i \<in> qbs_Mx (\<Pi>\<^sub>Q j\<in>{..<i}. X)"
    by(auto simp: coprod_qbs_Mx_def list_of_def coprod_qbs_Mx)
  define f' \<beta>'
    where "f' \<equiv> (\<lambda>r. Suc (f r))" "\<beta>' \<equiv> (\<lambda>i r n. if n = 0 then \<alpha> r else \<gamma> (i - 1) r (n - 1))"
  then have "(\<lambda>r. list_cons (fst (\<alpha> r, \<beta> r)) (snd (\<alpha> r, \<beta> r))) = (\<lambda>r. (f' r, \<beta>' (f' r) r))"
    by(auto simp: comp_def hf(1) ext list_cons_def)
  also have "... \<in> qbs_Mx (list_of X)"
    unfolding list_of_def
  proof(rule coprod_qbs_MxI)
    show "f' \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
      using hf by(simp add: f'_\<beta>'_def(1))
  next
    fix j
    assume hj:"j \<in> range f'"
    then have hj':"j - 1 \<in> range f"
      by(auto simp: f'_\<beta>'_def(1))
    show "\<beta>' j \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>{..<j}. X)"   
    proof(rule prod_qbs_MxI)
      fix i
      assume hi:"i \<in> {..<j}"
      then consider "i = 0" | "0 < i" "i < j"
        by auto
      then show "(\<lambda>r. \<beta>' j r i) \<in> qbs_Mx X"
      proof cases
        case 1
        then show ?thesis by(simp add: h(1) f'_\<beta>'_def(2))
      next
        case 2
        then have "i - 1 \<in> {..<j - 1}" by simp
        from prod_qbs_MxD(1)[OF hf(3)[OF hj'] this] 2
        show ?thesis
          by(simp add: f'_\<beta>'_def(2))
      qed
    next
      fix i
      assume hi:"i \<notin> {..<j}"
      then have "i \<noteq> 0" "i - Suc 0 \<notin> {..<j - Suc 0}"
        using f'_\<beta>'_def(1) hj by fastforce+
      with prod_qbs_MxD(2)[OF hf(3)[OF hj']]
      show "(\<lambda>r. \<beta>' j r i) = (\<lambda>r. undefined)"
        by(simp add: f'_\<beta>'_def(2))
    qed
  qed
  finally show "(\<lambda>r. list_cons (fst (\<alpha> r, \<beta> r)) (snd (\<alpha> r, \<beta> r))) \<in> qbs_Mx (list_of X)" .
qed

corollary cons_qbs_morphism[qbs]: "Cons \<in> X \<rightarrow>\<^sub>Q (list_qbs X) \<Rightarrow>\<^sub>Q list_qbs X"
proof(rule arg_swap_morphism)
  show "(\<lambda>x y. y # x) \<in> list_qbs X \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q list_qbs X"
  proof(rule qbs_morphism_cong'[where f="(\<lambda>l x. x # (to_list l)) \<circ> from_list"])
    show " (\<lambda>l x. x # to_list l) \<circ> from_list \<in> list_qbs X \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q list_qbs X"
    proof(rule qbs_morphism_comp[where Y="list_of X"])
      show " (\<lambda>l x. x # to_list l) \<in> list_of X \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q list_qbs X"
      proof(rule curry_preserves_morphisms)
        show "(\<lambda>lx. snd lx # to_list (fst lx)) \<in> list_of X \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q list_qbs X"
        proof(rule qbs_morphism_cong'[where f="to_list \<circ> (\<lambda>(l,x). from_list (x # to_list l))"])
          show "to_list \<circ> (\<lambda>(l, x). from_list (x # to_list l)) \<in> list_of X \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q list_qbs X"
          proof(rule qbs_morphism_comp[where Y="list_of X"])
            show "(\<lambda>(l, x). from_list (x # to_list l)) \<in> list_of X \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q list_of X"
              by(rule qbs_morphism_cong'[where f="(\<lambda>(l,x). list_cons x l)",OF _ uncurry_preserves_morphisms[of "\<lambda>(l,x). list_cons x l",simplified,OF arg_swap_morphism[OF list_cons_qbs_morphism]]]) (auto simp: pair_qbs_space to_list_from_list_ident)
          qed(simp add: list_qbs_def map_qbs_morphism_f)
        qed(auto simp: pair_qbs_space to_list_from_list_ident to_list_simp2)
      qed
    qed(auto simp: list_qbs_def to_list_from_list_ident intro!: map_qbs_morphism_inverse_f)
  qed(simp add: from_list_to_list_ident)
qed

lemma rec_list_morphism':
 "rec_list' \<in> qbs_space (Y \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q list_of X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q list_of X \<Rightarrow>\<^sub>Q Y)"
  unfolding list_of_def
proof(intro curry_preserves_morphisms[OF arg_swap_morphism] coprod_qbs_canonical1')
  fix n
  show "(\<lambda>x y. rec_list' (fst y) (snd y) (n, x)) \<in> (\<Pi>\<^sub>Q i\<in>{..<n}. X) \<rightarrow>\<^sub>Q exp_qbs (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (\<amalg>\<^sub>Q n\<in>UNIV. \<Pi>\<^sub>Q i\<in>{..<n}. X) (exp_qbs Y Y))) Y"
  proof(induction n)
    case 0
    show ?case
    proof(rule curry_preserves_morphisms[OF qbs_morphismI])
      fix \<alpha>
      assume h:"\<alpha> \<in> qbs_Mx ((\<Pi>\<^sub>Q i\<in>{..<0::nat}. X) \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (\<amalg>\<^sub>Q n\<in>UNIV. \<Pi>\<^sub>Q i\<in>{..<n::nat}. X) (exp_qbs Y Y)))"
      have "\<And>r. fst (\<alpha> r) = (\<lambda>n. undefined)"
      proof -
        fix r
        have "\<And>i. (\<lambda>r. fst (\<alpha> r) i) = (\<lambda>r. undefined)"
          using h by(auto simp: exp_qbs_Mx PiQ_Mx  pair_qbs_Mx comp_def split_beta')
        thus "fst (\<alpha> r) = (\<lambda>n. undefined)"
          by(fastforce dest: fun_cong)
      qed
      hence "(\<lambda>xy. rec_list' (fst (snd xy)) (snd (snd xy)) (0, fst xy)) \<circ> \<alpha> = (\<lambda>x. fst (snd (\<alpha> x)))"
        by(auto simp: rec_list'_simp1[simplified list_nil_def] comp_def split_beta')
      also have "... \<in> qbs_Mx Y"
        using h by(auto simp: pair_qbs_Mx comp_def)
      finally show "(\<lambda>xy. rec_list' (fst (snd xy)) (snd (snd xy)) (0, fst xy)) \<circ> \<alpha> \<in> qbs_Mx Y" .
    qed
  next
    case ih:(Suc n)
    show ?case
    proof(rule qbs_morphismI)
      fix \<alpha>
      assume h:"\<alpha> \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>{..<Suc n}. X)"
      define \<alpha>' where "\<alpha>' \<equiv> (\<lambda>r. snd (list_tail (Suc n, \<alpha> r)))"
      define a where "a \<equiv> (\<lambda>r. \<alpha> r 0)"
      then have ha:"a \<in> qbs_Mx X"
        using h by(auto simp: PiQ_Mx)
      have 1:"\<alpha>' \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>{..<n}. X)"
        using h by(fastforce simp: PiQ_Mx list_tail_def \<alpha>'_def)
      hence 2: "\<And>r. (n, \<alpha>' r) \<in> qbs_space (list_of X)"
        using qbs_Mx_to_X[of \<alpha>'] by (fastforce simp: PiQ_space coprod_qbs_space list_of_def)
      have 3: "\<And>r. (Suc n, \<alpha> r) \<in> qbs_space (list_of X)"
        using qbs_Mx_to_X[of \<alpha>] h by (fastforce simp: PiQ_space coprod_qbs_space list_of_def)
      have 4: "\<And>r. (n, \<alpha>' r) = list_tail (Suc n, \<alpha> r)"
        by(simp add: list_tail_def \<alpha>'_def)
      have 5: "\<And>r. (Suc n, \<alpha> r) = list_cons (a r) (n, \<alpha>' r)"
        unfolding a_def by(simp add: list_simp5[OF 3,simplified 4[symmetric],simplified list_head_def list_cons_def list_nil_def] list_cons_def) auto
      have 6: "(\<lambda>r. (n, \<alpha>' r)) \<in> qbs_Mx (list_of X)"
        using 1 by(auto intro!: coprod_qbs_MxI simp: PiQ_space coprod_qbs_space list_of_def)

      have "(\<lambda>x y. rec_list' (fst y) (snd y) (Suc n, x)) \<circ> \<alpha> = (\<lambda>r y. rec_list' (fst y) (snd y) (Suc n, \<alpha> r))"
        by auto
      also have "... = (\<lambda>r y. snd y (a r) (n, \<alpha>' r) (rec_list' (fst y) (snd y) (n, \<alpha>' r)))"
        by(simp only: 5 rec_list'_simp2[OF 2])
      also have "... \<in> qbs_Mx (exp_qbs (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) Y)"
      proof -
        have "(\<lambda>(r,y). snd y (a r) (n, \<alpha>' r) (rec_list' (fst y) (snd y) (n, \<alpha>' r))) = (\<lambda>(y,x1,x2,x3). y x1 x2 x3) \<circ> (\<lambda>(r,y). (snd y, a r, (n, \<alpha>' r), rec_list' (fst y) (snd y) (n, \<alpha>' r)))"
          by auto
        also have "... \<in> qbs_borel \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) \<rightarrow>\<^sub>Q Y"
        proof(rule qbs_morphism_comp[where Y="exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q list_of X \<Otimes>\<^sub>Q Y"])
          show "(\<lambda>(r, y). (snd y, a r, (n, \<alpha>' r), rec_list' (fst y) (snd y) (n, \<alpha>' r))) \<in> qbs_borel \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<rightarrow>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q list_of X \<Otimes>\<^sub>Q Y"
            unfolding split_beta'
          proof(safe intro!: qbs_morphism_Pair)
            show "(\<lambda>x. a (fst x)) \<in> qbs_borel \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<rightarrow>\<^sub>Q X"
              using ha qbs_Mx_is_morphisms[of X] ha by auto
          next
            show "(\<lambda>x. (n, \<alpha>' (fst x))) \<in> qbs_borel \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<rightarrow>\<^sub>Q list_of X"
              using 6 by(simp add: qbs_Mx_is_morphisms) (use fst_qbs_morphism qbs_morphism_compose in blast)
          next
            show "(\<lambda>x. rec_list' (fst (snd x)) (snd (snd x)) (n, \<alpha>' (fst x))) \<in> qbs_borel \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<rightarrow>\<^sub>Q Y"
              using qbs_morphism_Mx[OF ih 1, simplified comp_def]  uncurry_preserves_morphisms[of "(\<lambda>(x,y). rec_list' (fst y) (snd y) (n, \<alpha>' x))" qbs_borel "Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))" Y] qbs_Mx_is_morphisms[of "exp_qbs (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) Y"]
              by(fastforce simp: split_beta' list_of_def)
          qed qbs
        next
          show "(\<lambda>(y, x1, x2, x3). y x1 x2 x3) \<in> exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q list_of X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Y"
            by simp
        qed
        finally show ?thesis
          by(simp add: exp_qbs_Mx')
      qed
      finally show "(\<lambda>x y. rec_list' (fst y) (snd y) (Suc n, x)) \<circ> \<alpha> \<in> qbs_Mx (exp_qbs (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (\<amalg>\<^sub>Q n\<in>UNIV. \<Pi>\<^sub>Q i\<in>{..<n}. X) (exp_qbs Y Y))) Y)"
        by(simp add: list_of_def)
    qed
  qed
qed simp

lemma rec_list_morphism[qbs]: "rec_list \<in> qbs_space (Y \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q Y)"
proof(rule curry_preserves_morphisms[OF arg_swap_morphism])
  show "(\<lambda>l yf. rec_list (fst yf) (snd yf) l) \<in> list_qbs X \<rightarrow>\<^sub>Q Y \<Otimes>\<^sub>Q (X \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q Y"
  proof(rule qbs_morphism_cong'[where f="(\<lambda>l' (y,f). rec_list y f (to_list l')) \<circ> from_list",OF _ qbs_morphism_comp[where Y="list_of X"]])
    show "(\<lambda>l' (y,f). rec_list y f (to_list l')) \<in> list_of X \<rightarrow>\<^sub>Q Y \<Otimes>\<^sub>Q (X \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q Y"
      apply(rule arg_swap_morphism,simp only: split_beta' list_qbs_def)
      apply(rule uncurry_preserves_morphisms)
      apply(rule arg_swap_morphism)
      apply(rule arg_swap_morphism')
      apply(rule qbs_morphism_cong'[OF _  arg_swap_morphism_map_qbs1[OF arg_swap_morphism'[OF arg_swap_morphism[OF rec_list_morphism']]]])
      apply(auto simp: rec_list'_def from_list_to_list_ident)
      done
  qed(auto simp: from_list_to_list_ident list_qbs_def to_list_from_list_ident intro!: map_qbs_morphism_inverse_f)
qed

hide_const (open) list_nil list_cons list_head list_tail from_list rec_list' to_list'

hide_fact (open) list_simp1 list_simp2 list_simp3 list_simp4 list_simp5 list_simp6 list_simp7 from_list_in_list_of' list_cons_qbs_morphism rec_list'_simp1
          to_list_from_list_ident from_list_in_list_of to_list_set to_list_simp1 to_list_simp2 list_head_def list_tail_def from_list_length
          list_cons_in_list_of rec_list_morphism' rec_list'_simp2 list_decomp1 list_destruct_rule list_induct_rule from_list_to_list_ident

corollary case_list_morphism[qbs]: "case_list \<in> qbs_space ((Y :: 'b quasi_borel) \<Rightarrow>\<^sub>Q ((X :: 'a quasi_borel) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q Y)"
proof -
  have [simp]:"case_list = (\<lambda>y (f :: 'a \<Rightarrow> 'a list \<Rightarrow> 'b) l. rec_list y (\<lambda>x l' y. f x l') l)"
  proof standard+
    fix y :: 'b and f :: "'a \<Rightarrow> 'a list \<Rightarrow> 'b" and l :: "'a list"
    show "(case l of [] \<Rightarrow> y | x # xa \<Rightarrow> f x xa) = rec_list y (\<lambda>x l' y. f x l') l"
      by (cases l) auto
  qed
  show ?thesis
    by simp
qed

lemma fold_qbs_morphism[qbs]: "fold \<in> qbs_space ((X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Y)"
proof -
  have [simp]:"fold = (\<lambda>f l. rec_list id (\<lambda>x xs l. l \<circ> f x) l)"
    apply standard+
    subgoal for f l x
      by(induction l arbitrary: x) simp_all
    done
  show ?thesis
    by simp
qed

lemma [qbs]:
  shows foldr_qbs_morphism: "foldr \<in> qbs_space ((X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q Y)"
    and foldl_qbs_morphism: "foldl \<in> qbs_space ((X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q X) \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q list_qbs Y \<Rightarrow>\<^sub>Q X)"
    and zip_qbs_morphism: "zip \<in> qbs_space (list_qbs X \<Rightarrow>\<^sub>Q list_qbs Y \<Rightarrow>\<^sub>Q list_qbs (pair_qbs X Y))"
    and append_qbs_morphism: "append \<in> qbs_space (list_qbs X \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)"
    and concat_qbs_morphism: "concat \<in> qbs_space (list_qbs (list_qbs X) \<Rightarrow>\<^sub>Q list_qbs X)"
    and drop_qbs_morphism: "drop \<in> qbs_space (qbs_count_space UNIV \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)"
    and take_qbs_morphism: "take \<in> qbs_space (qbs_count_space UNIV \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)"
    and rev_qbs_morphism: "rev \<in> qbs_space (list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)"
  by(auto simp: foldr_def foldl_def zip_def append_def concat_def drop_def take_def rev_def)

lemma [qbs]:
  fixes X :: "'a quasi_borel" and Y :: "'b quasi_borel"
  shows map_qbs_morphism: "map \<in> qbs_space ((X \<Rightarrow>\<^sub>Q Y) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs Y)" (is ?map)
    and fileter_qbs_morphism: "filter \<in> qbs_space ((X \<Rightarrow>\<^sub>Q count_space\<^sub>Q UNIV) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)" (is ?filter)
    and length_qbs_morphism: "length \<in> qbs_space (list_qbs X \<Rightarrow>\<^sub>Q qbs_count_space UNIV)" (is ?length)
    and tl_qbs_morphism: "tl \<in> qbs_space (list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)" (is ?tl)
    and list_all_qbs_morphism: "list_all \<in> qbs_space ((X \<Rightarrow>\<^sub>Q qbs_count_space UNIV) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q qbs_count_space UNIV)" (is ?list_all)
    and bind_list_qbs_morphism: "(\<bind>) \<in> qbs_space (list_qbs X \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q list_qbs Y) \<Rightarrow>\<^sub>Q list_qbs Y)" (is ?bind)
proof -
  have [simp]: "map = (\<lambda>f. rec_list [] (\<lambda>x xs l. f x # l))"
    apply standard+
    subgoal for f l
      by(induction l) simp_all
    done
  have [simp]: "filter = (\<lambda>P. rec_list [] (\<lambda>x xs l. if P x then x # l else l))"
    apply standard+
    subgoal for f l
      by(induction l) simp_all
    done
  have [simp]: "length = (\<lambda>l. foldr (\<lambda>_ n. Suc n) l 0)"
    apply standard
    subgoal for l
      by (induction l) simp_all
    done
  have [simp]: "tl = (\<lambda>l. case l of [] \<Rightarrow> [] | _ # xs \<Rightarrow> xs)"
    by standard (simp add: tl_def)
  have [simp]: "list_all = (\<lambda>P xs. foldr (\<lambda>x b. b \<and> P x) xs True)"
    apply (standard,standard)
    subgoal for P xs
      by(induction xs arbitrary: P) auto
    done
  have [simp]: "List.bind = (\<lambda>xs f. concat (map f xs))"
    by standard+ (simp add: List.bind_def)
  show ?map  ?filter ?length ?tl ?list_all ?bind
    by simp_all
qed

lemma list_eq_qbs_morphism[qbs]:
  assumes [qbs]: "(=) \<in> qbs_space (X \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q count_space UNIV)"
  shows "(=) \<in> qbs_space (list_qbs X \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q count_space UNIV)"
proof -
  have [simp]:"(=) = (\<lambda>xs ys. length xs = length ys \<and> list_all (case_prod (=)) (zip xs ys))"
    using Ball_set list_eq_iff_zip_eq by fastforce
  show ?thesis
    by simp
qed

lemma insort_key_qbs_morphism[qbs]:
  shows "insort_key \<in> qbs_space ((X \<Rightarrow>\<^sub>Q (borel\<^sub>Q ::'b :: {second_countable_topology, linorder_topology} quasi_borel)) \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)" (is ?g1)
    and "insort_key \<in> qbs_space ((X \<Rightarrow>\<^sub>Q count_space\<^sub>Q (UNIV :: (_ :: countable) set)) \<Rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)" (is ?g2)
proof -
  have [simp]:"insort_key = (\<lambda>f x. rec_list [x] (\<lambda>y ys l. if f x \<le> f y then x#y#ys else y#l))"
    apply standard+
    subgoal for f x l
      by(induction l) simp_all
    done
  show ?g1 ?g2
    by simp_all
qed

lemma sort_key_qbs_morphism[qbs]:
  shows "sort_key \<in> qbs_space ((X \<Rightarrow>\<^sub>Q (borel\<^sub>Q ::'b :: {second_countable_topology, linorder_topology} quasi_borel)) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)"
    and "sort_key \<in> qbs_space ((X \<Rightarrow>\<^sub>Q count_space\<^sub>Q (UNIV :: (_ :: countable) set)) \<Rightarrow>\<^sub>Q list_qbs X \<Rightarrow>\<^sub>Q list_qbs X)"
  unfolding sort_key_def by simp_all

lemma sort_qbs_morphism[qbs]:
  shows "sort \<in> list_qbs (borel\<^sub>Q ::'b :: {second_countable_topology, linorder_topology} quasi_borel) \<rightarrow>\<^sub>Q list_qbs borel\<^sub>Q"
    and "sort \<in> list_qbs (count_space\<^sub>Q (UNIV :: (_ :: countable) set)) \<rightarrow>\<^sub>Q list_qbs (count_space\<^sub>Q UNIV)"
  by simp_all

subsubsection \<open> Morphism Pred\<close>
abbreviation "qbs_pred X P \<equiv> P \<in> X \<rightarrow>\<^sub>Q qbs_count_space (UNIV :: bool set)"

lemma qbs_pred_iff_measurable_pred:
 "qbs_pred X P = Measurable.pred (qbs_to_measure X) P"
  by(simp add: lr_adjunction_correspondence)

lemma(in standard_borel) qbs_pred_iff_measurable_pred:
 "qbs_pred (measure_to_qbs M) P = Measurable.pred M P"
  by(simp add: qbs_pred_iff_measurable_pred measurable_cong_sets[OF lr_sets_ident refl])

lemma qbs_pred_iff_sets:
"{x \<in>space (qbs_to_measure X). P x} \<in> sets (qbs_to_measure X) \<longleftrightarrow> qbs_pred X P"
  by (simp add: Measurable.pred_def lr_adjunction_correspondence space_L)

lemma
  assumes [qbs]:"P \<in> X \<rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q qbs_count_space UNIV" "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows indicator_qbs_morphism''': "(\<lambda>x. indicator {y. P x y} (f x)) \<in> X \<rightarrow>\<^sub>Q qbs_borel" (is ?g1)
    and indicator_qbs_morphism'': "(\<lambda>x. indicator {y\<in>qbs_space Y. P x y} (f x)) \<in> X \<rightarrow>\<^sub>Q qbs_borel" (is ?g2)
proof -
  have [simp]:"{x \<in> qbs_space X. P x (f x)} = {x \<in> qbs_space X. f x \<in> qbs_space Y \<and> P x (f x)}"
    using qbs_morphism_space[OF assms(2)] by blast
  show ?g1 ?g2
    using qbs_morphism_app[OF assms,simplified qbs_pred_iff_sets[symmetric]] qbs_morphism_space[OF assms(2)]
    by(auto intro!: borel_measurable_indicator' simp: lr_adjunction_correspondence space_L)
qed

lemma
  assumes [qbs]:"P \<in> X \<rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q qbs_count_space UNIV"
  shows indicator_qbs_morphism[qbs]:"(\<lambda>x. indicator {y \<in> qbs_space Y. P x y}) \<in> X \<rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q qbs_borel" (is ?g1)
    and indicator_qbs_morphism':"(\<lambda>x. indicator {y. P x y}) \<in> X \<rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q qbs_borel" (is ?g2)
proof -
  note indicator_qbs_morphism''[qbs] indicator_qbs_morphism'''[qbs]
  show ?g1 ?g2
    by(auto intro!: curry_preserves_morphisms[OF pair_qbs_morphismI] simp: qbs_Mx_is_morphisms)
qed

lemma indicator_qbs[qbs]:
  assumes "qbs_pred X P"
  shows "indicator {x. P x} \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  using assms by(auto simp: lr_adjunction_correspondence)

lemma All_qbs_pred[qbs]: "qbs_pred (count_space\<^sub>Q (UNIV :: ('a :: countable) set) \<Rightarrow>\<^sub>Q count_space\<^sub>Q UNIV) All"
proof(rule qbs_morphismI)
  fix a :: "real \<Rightarrow> 'a \<Rightarrow> bool"
  assume "a \<in> qbs_Mx (count_space\<^sub>Q UNIV \<Rightarrow>\<^sub>Q count_space\<^sub>Q UNIV)"
  hence [measurable]: "\<And>f g. f \<in> borel_measurable borel \<Longrightarrow> g \<in> borel \<rightarrow>\<^sub>M count_space UNIV \<Longrightarrow> (\<lambda>x::real. a (f x) (g x)) \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
    by(auto simp add: exp_qbs_Mx qbs_Mx_R)
  show " All \<circ> a \<in> qbs_Mx (count_space\<^sub>Q UNIV)"
    by(simp add: comp_def qbs_Mx_R)
qed

lemma Ex_qbs_pred[qbs]: "qbs_pred (count_space\<^sub>Q (UNIV :: ('a :: countable) set) \<Rightarrow>\<^sub>Q count_space\<^sub>Q UNIV) Ex"
proof(rule qbs_morphismI)
  fix a :: "real \<Rightarrow> 'a \<Rightarrow> bool"
  assume "a \<in> qbs_Mx (count_space\<^sub>Q UNIV \<Rightarrow>\<^sub>Q count_space\<^sub>Q UNIV)"
  hence [measurable]: "\<And>f g. f \<in> borel_measurable borel \<Longrightarrow> g \<in> borel \<rightarrow>\<^sub>M count_space UNIV \<Longrightarrow> (\<lambda>x::real. a (f x) (g x)) \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
    by(auto simp add: exp_qbs_Mx qbs_Mx_R)
  show "Ex \<circ> a \<in> qbs_Mx (count_space\<^sub>Q UNIV)"
    by(simp add: comp_def qbs_Mx_R)
qed

lemma Ball_qbs_pred_countable:
  assumes "\<And>i::'a :: countable. i \<in> I \<Longrightarrow> qbs_pred X (P i)"
  shows "qbs_pred X (\<lambda>x. \<forall>x\<in>I. P i x)"
  using assms by(simp add: qbs_pred_iff_measurable_pred)

lemma Ball_qbs_pred:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> qbs_pred X (P i)"
  shows "qbs_pred X (\<lambda>x. \<forall>x\<in>I. P i x)"
  using assms by(simp add: qbs_pred_iff_measurable_pred)

lemma Bex_qbs_pred_countable:
  assumes "\<And>i::'a :: countable. i \<in> I \<Longrightarrow> qbs_pred X (P i)"
  shows "qbs_pred X (\<lambda>x. \<exists>x\<in>I. P i x)"
  using assms by(simp add: qbs_pred_iff_measurable_pred)

lemma Bex_qbs_pred:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> qbs_pred X (P i)"
  shows "qbs_pred X (\<lambda>x. \<exists>x\<in>I. P i x)"
  using assms by(simp add: qbs_pred_iff_measurable_pred)

lemma qbs_morphism_If_sub_qbs:
  assumes [qbs]: "qbs_pred X P"
      and [qbs]: "f \<in> sub_qbs X {x\<in>qbs_space X. P x} \<rightarrow>\<^sub>Q Y" "g \<in> sub_qbs X {x\<in>qbs_space X. \<not> P x} \<rightarrow>\<^sub>Q Y"
    shows "(\<lambda>x. if P x then f x else g x) \<in> X \<rightarrow>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume h:"\<alpha> \<in> qbs_Mx X"
  interpret standard_borel_ne "borel :: real measure" by simp
  have [measurable]: "Measurable.pred borel (\<lambda>x. P (\<alpha> x))"
    using h by(simp add: qbs_pred_iff_measurable_pred[symmetric] qbs_Mx_is_morphisms)
  consider "qbs_space X = {}" 
    | "{x\<in>qbs_space X. \<not> P x} = qbs_space X"
    | "{x\<in>qbs_space X. P x} = qbs_space X"
    | "{x\<in>qbs_space X. P x} \<noteq> {}" "{x\<in>qbs_space X. \<not> P x} \<noteq> {}" by blast
  then show "(\<lambda>x. if P x then f x else g x) \<circ> \<alpha> \<in> qbs_Mx Y" (is "?f \<in> _")
  proof cases
    case 1
    with h show ?thesis
      by(simp add: qbs_empty_equiv)
  next
    case 2
    have [simp]:"(\<lambda>x. if P x then f x else g x) \<circ> \<alpha> = g \<circ> \<alpha>"
      by standard (use qbs_Mx_to_X[OF h] 2 in auto)
    show ?thesis
      using 2 qbs_morphism_Mx[OF assms(3)] h by(simp add: sub_qbs_ident)
  next
    case 3
    have [simp]:"(\<lambda>x. if P x then f x else g x) \<circ> \<alpha> = f \<circ> \<alpha>"
      by standard (use qbs_Mx_to_X[OF h] 3 in auto)
    show ?thesis
      using 3 qbs_morphism_Mx[OF assms(2)] h by(simp add: sub_qbs_ident)
  next
    case 4
    then obtain x0 x1 where
     x0:"x0 \<in> qbs_space X" "P x0" and x1:"x1 \<in> qbs_space X" "\<not> P x1"
      by blast
    define a0 where "a0 = (\<lambda>r. if P (\<alpha> r) then \<alpha> r else x0)"
    define a1 where "a1 = (\<lambda>r. if \<not> P (\<alpha> r) then \<alpha> r else x1)"
    have "a0 \<in> qbs_Mx (sub_qbs X {x\<in>qbs_space X. P x})" "a1 \<in> qbs_Mx (sub_qbs X {x\<in>qbs_space X. \<not> P x})"
      using x0 x1 qbs_Mx_to_X[OF h] h
      by(auto simp: sub_qbs_Mx a0_def a1_def intro!: qbs_closed3_dest2'[of UNIV "\<lambda>r. P (\<alpha> r)" "\<lambda>b r. if b then \<alpha> r else x0"]) (simp_all add: qbs_Mx_is_morphisms)
    from qbs_morphism_Mx[OF assms(2) this(1)] qbs_morphism_Mx[OF assms(3) this(2)]
    have h0:"(\<lambda>r. f (a0 r)) \<in> qbs_Mx Y" "(\<lambda>r. g (a1 r)) \<in> qbs_Mx Y"
      by (simp_all add: comp_def)
    have [simp]:"(\<lambda>x. if P x then f x else g x) \<circ> \<alpha> = (\<lambda>r. if P (\<alpha> r) then f (a0 r) else g (a1 r))"
      by standard (auto simp: comp_def a0_def a1_def)
    show "(\<lambda>x. if P x then f x else g x) \<circ> \<alpha> \<in> qbs_Mx Y"
      using h h0 by(simp add: qbs_Mx_is_morphisms)
  qed
qed

subsubsection \<open> The Adjunction w.r.t. Ordering\<close>
lemma l_mono: "mono qbs_to_measure"
proof
  fix X Y :: "'a quasi_borel"
  show "X \<le> Y \<Longrightarrow> qbs_to_measure X \<le> qbs_to_measure Y"
  proof(induction rule: less_eq_quasi_borel.induct)
    case (1 X Y)
    then show ?case
      by(simp add: less_eq_measure.intros(1) space_L)
  next
    case (2 X Y)
    then have "sigma_Mx X \<subseteq> sigma_Mx Y"
      by(auto simp add: sigma_Mx_def)
    then consider "sigma_Mx X \<subset> sigma_Mx Y" | "sigma_Mx X = sigma_Mx Y"
      by auto
    then show ?case
      apply(cases)
       apply(rule less_eq_measure.intros(2))
        apply(simp_all add: 2 space_L sets_L)
      by(rule less_eq_measure.intros(3),simp_all add: 2 sets_L space_L emeasure_L)
  qed
qed

lemma r_mono: "mono measure_to_qbs"
proof
  fix M N :: "'a measure"
  show "M \<le> N \<Longrightarrow> measure_to_qbs M \<le> measure_to_qbs N"
  proof(induction rule: less_eq_measure.inducts)
    case (1 M N)
    then show ?case
      by(simp add: less_eq_quasi_borel.intros(1) qbs_space_R)
  next
    case (2 M N)
    then have "(borel :: real measure) \<rightarrow>\<^sub>M N \<subseteq> borel \<rightarrow>\<^sub>M M"
      by(simp add: measurable_mono)
    then consider "(borel :: real measure) \<rightarrow>\<^sub>M N \<subset> borel \<rightarrow>\<^sub>M M" | "(borel :: real measure) \<rightarrow>\<^sub>M N = borel \<rightarrow>\<^sub>M M"
      by auto
    then show ?case
      by cases (rule less_eq_quasi_borel.intros(2),simp_all add: 2 qbs_space_R qbs_Mx_R)+
  next
    case (3 M N)
    then show ?case
      apply -
      by(rule less_eq_quasi_borel.intros(2)) (simp_all add: measurable_mono qbs_space_R qbs_Mx_R)
  qed
qed

lemma rl_order_adjunction:
  "X \<le> qbs_to_measure Y \<longleftrightarrow> measure_to_qbs X \<le> Y"
proof
  assume 1: "X \<le> qbs_to_measure Y"
  then show "measure_to_qbs X \<le> Y"
  proof(induction rule: less_eq_measure.cases)
    case (1 M N)
    then have [simp]:"qbs_space Y = space N"
      by(simp add: 1(2)[symmetric] space_L)
    show ?case
      by(rule less_eq_quasi_borel.intros(1),simp add: 1 qbs_space_R)
  next
    case (2 M N)
    then have [simp]:"qbs_space Y = space N"
      by(simp add: 2(2)[symmetric] space_L)
    show ?case
    proof(rule less_eq_quasi_borel.intros(2))
      show "qbs_Mx Y \<subseteq> qbs_Mx (measure_to_qbs X)"
        unfolding qbs_Mx_R
      proof
        fix \<alpha>
        assume h:"\<alpha> \<in> qbs_Mx Y"
        show "\<alpha> \<in> borel \<rightarrow>\<^sub>M X"
        proof(rule measurableI)
          show "\<And>x. \<alpha> x \<in> space X"
            using qbs_Mx_to_X[OF h] by (auto simp add: 2)
        next
          fix A
          assume "A \<in> sets X"
          then have "A \<in> sets (qbs_to_measure Y)"
            using 2 by auto
          then obtain U where
            hu:"A = U \<inter> space N" "(\<forall>\<alpha>\<in>qbs_Mx Y. \<alpha> -` U \<in> sets borel)"
            by(auto simp add: sigma_Mx_def sets_L)
          have "\<alpha> -` A  = \<alpha> -` U"
            using qbs_Mx_to_X[OF h] by(auto simp add: hu)
          thus "\<alpha> -` A \<inter> space borel \<in> sets borel"
            using h hu(2) by simp
        qed
      qed
    qed(auto simp: 2 qbs_space_R)
  next
    case (3 M N)
    then have [simp]:"qbs_space Y = space N"
      by(simp add: 3(2)[symmetric] space_L)
    show ?case
    proof(rule less_eq_quasi_borel.intros(2))
      show "qbs_Mx Y \<subseteq> qbs_Mx (measure_to_qbs X)"
        unfolding qbs_Mx_R
      proof
        fix \<alpha>
        assume h:"\<alpha> \<in> qbs_Mx Y"
        show "\<alpha> \<in> borel \<rightarrow>\<^sub>M X"
        proof(rule measurableI)
          show "\<And>x. \<alpha> x \<in> space X"
            using qbs_Mx_to_X[OF h] by(auto simp: 3)
        next
          fix A
          assume "A \<in> sets X"
          then have "A \<in> sets (qbs_to_measure Y)"
            using 3 by auto
          then obtain U where
            hu:"A = U \<inter> space N" "(\<forall>\<alpha>\<in>qbs_Mx Y. \<alpha> -` U \<in> sets borel)"
            by(auto simp add: sigma_Mx_def sets_L)
          have "\<alpha> -` A  = \<alpha> -` U"
            using qbs_Mx_to_X[OF h] by(auto simp add: hu)
          thus "\<alpha> -` A \<inter> space borel \<in> sets borel"
            using h hu(2) by simp
        qed
      qed
    qed(auto simp: 3 qbs_space_R)
  qed
next
  assume "measure_to_qbs X \<le> Y"
  then show "X \<le> qbs_to_measure Y"
  proof(induction rule: less_eq_quasi_borel.cases)
    case (1 A B)
    have [simp]: "space X = qbs_space A"
      by(simp add: 1(1)[symmetric] qbs_space_R)
    show ?case
      by(rule less_eq_measure.intros(1)) (simp add: 1 space_L)
  next
    case (2 A B)
    then have hmy:"qbs_Mx Y \<subseteq> borel \<rightarrow>\<^sub>M X"
      using qbs_Mx_R by blast  
    have [simp]: "space X = qbs_space A"
      by(simp add: 2(1)[symmetric] qbs_space_R)
    have "sets X \<subseteq> sigma_Mx Y"
    proof
      fix U
      assume hu:"U \<in> sets X"
      show "U \<in> sigma_Mx Y"
        unfolding sigma_Mx_def
      proof(safe intro!: exI[where x=U])
        show "\<And>x. x \<in> U \<Longrightarrow> x \<in> qbs_space Y"
          using sets.sets_into_space[OF hu]
          by(auto simp add: 2)
      next
        fix \<alpha>
        assume "\<alpha> \<in> qbs_Mx Y"
        then have "\<alpha> \<in> borel \<rightarrow>\<^sub>M X"
          using hmy by(auto)
        thus "\<alpha> -` U \<in> sets borel"
          using hu by(simp add: measurable_sets_borel)
      qed
    qed
    then consider "sets X = sigma_Mx Y" | "sets X \<subset> sigma_Mx Y"
      by auto
    then show ?case
    proof cases
      case 1
      show ?thesis
      proof(rule less_eq_measure.intros(3))
        show "emeasure X \<le> emeasure (qbs_to_measure Y)"
          unfolding emeasure_L
        proof(rule le_funI)
          fix U
          consider "U = {}" | "U \<notin> sigma_Mx Y" | "U \<noteq> {} \<and> U \<in> sigma_Mx Y"
            by auto
          then show "emeasure X U \<le> (if U = {} \<or> U \<notin> sigma_Mx Y then 0 else \<infinity>)"
          proof cases
            case 1
            then show ?thesis by simp
          next
            case h:2
            then have "U \<notin> sigma_Mx A"
              using qbs_Mx_sigma_Mx_contra[OF 2(3)[symmetric] 2(4)] 2(2) by auto
            hence "U \<notin> sets X"
              using lr_sets 2(1) sets_L by blast
            thus ?thesis
              by(simp add: h emeasure_notin_sets)
          next
            case 3
            then show ?thesis
            by simp
        qed
      qed
    qed(simp_all add: 1 2 space_L sets_L)
    next
      case h2:2
      show ?thesis
        by(rule less_eq_measure.intros(2)) (simp add: space_L 2, simp add: h2 sets_L)
    qed
  qed
qed

end