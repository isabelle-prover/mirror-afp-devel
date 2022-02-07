(*  Title:   Measure_QuasiBorel_Adjunction.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open>Relation to Measurable Spaces\<close>

theory Measure_QuasiBorel_Adjunction
  imports "QuasiBorel"
begin

text \<open> We construct the adjunction between \textbf{Meas} and \textbf{QBS},
       where \textbf{Meas} is the category of measurable spaces and measurable functions
       and \textbf{QBS} is the category of quasi-Borel spaces and morphisms.\<close>

subsubsection \<open> The Functor $R$ \<close>
definition measure_to_qbs :: "'a measure \<Rightarrow> 'a quasi_borel" where
"measure_to_qbs X \<equiv> Abs_quasi_borel (space X, real_borel \<rightarrow>\<^sub>M X)"

lemma R_Mx_correct: "real_borel \<rightarrow>\<^sub>M X \<subseteq> UNIV \<rightarrow> space X"
  by (simp add: measurable_space subsetI)

lemma R_qbs_closed1: "qbs_closed1 (real_borel \<rightarrow>\<^sub>M X)"
  by (simp add: qbs_closed1_def)

lemma R_qbs_closed2: "qbs_closed2 (space X) (real_borel \<rightarrow>\<^sub>M X)"
  by (simp add: qbs_closed2_def)

lemma R_qbs_closed3: "qbs_closed3 (real_borel \<rightarrow>\<^sub>M (X :: 'a measure))"
proof(rule qbs_closed3I)
  fix P::"real \<Rightarrow> nat"
  fix Fi::"nat \<Rightarrow> real \<Rightarrow> 'a"
  assume h:"\<And>i. P -` {i} \<in> sets real_borel"
           "\<And>i. Fi i \<in> real_borel \<rightarrow>\<^sub>M X"
  show "(\<lambda>r. Fi (P r) r) \<in> real_borel \<rightarrow>\<^sub>M X"
  proof(rule measurableI)
    fix x
    assume "x \<in> space real_borel"
    then show "Fi (P x) x \<in> space X"
      using h(2) measurable_space[of "Fi (P x)" real_borel X x]
      by auto
  next
    fix A
    assume h':"A \<in> sets X"
    have "(\<lambda>r. Fi (P r) r) -` A = (\<Union>i::nat. ((Fi i -` A) \<inter> (P -` {i})))"
      by auto
    also have "... \<in> sets real_borel"
      using sets.Int measurable_sets[OF h(2) h'] h(1)
      by(auto intro!: countable_Un_Int(1))
    finally show "(\<lambda>r. Fi (P r) r) -` A \<inter> space real_borel \<in> sets real_borel"
      by simp
  qed
qed

lemma R_correct[simp]: "Rep_quasi_borel (measure_to_qbs X) = (space X, real_borel \<rightarrow>\<^sub>M X)"
  unfolding measure_to_qbs_def
  by (rule Abs_quasi_borel_inverse) (simp add: R_Mx_correct R_qbs_closed1 R_qbs_closed2 R_qbs_closed3)

lemma qbs_space_R[simp]: "qbs_space (measure_to_qbs X) = space X"
  by (simp add: qbs_space_def)

lemma qbs_Mx_R[simp]: "qbs_Mx (measure_to_qbs X) = real_borel \<rightarrow>\<^sub>M X"
  by (simp add: qbs_Mx_def)


text \<open> The following lemma says that @{term measure_to_qbs} is a functor from \textbf{Meas} to \textbf{QBS}. \<close>
lemma r_preserves_morphisms:
   "X \<rightarrow>\<^sub>M Y \<subseteq> (measure_to_qbs X) \<rightarrow>\<^sub>Q (measure_to_qbs Y)"
  by(auto intro!: qbs_morphismI)

subsubsection \<open> The Functor $L$ \<close>
definition sigma_Mx :: "'a quasi_borel \<Rightarrow> 'a set set" where
"sigma_Mx X \<equiv> {U \<inter> qbs_space X |U. \<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` U \<in> sets real_borel}"

definition qbs_to_measure :: "'a quasi_borel \<Rightarrow> 'a measure" where
"qbs_to_measure X \<equiv> Abs_measure (qbs_space X, sigma_Mx X, \<lambda>A. (if A = {} then 0 else if A \<in> - sigma_Mx X then 0 else \<infinity>))"

lemma measure_space_L: "measure_space (qbs_space X) (sigma_Mx X) (\<lambda>A. (if A = {} then 0 else if A \<in> - sigma_Mx X then 0 else \<infinity>))"
  unfolding measure_space_def
proof auto

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
      then have "\<exists> Ua. A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets real_borel)"
        by (simp add: sigma_Mx_def)
      then obtain Ua where pa:"A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets real_borel)" by auto
      have "\<exists> Ub. B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets real_borel)"
        using \<open>B \<in> sigma_Mx X\<close> sigma_Mx_def by auto
      then obtain Ub where pb:"B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets real_borel)" by auto
      from pa pb have [simp]:"\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (Ua \<inter> Ub) \<in> sets real_borel"
        by auto
      from this pa pb sigma_Mx_def have [simp]:"(Ua \<inter> Ub) \<inter> qbs_space X \<in> sigma_Mx X" by blast
      from pa pb have [simp]:"A \<inter> B = (Ua \<inter> Ub) \<inter> qbs_space X" by auto
      thus "A \<inter> B \<in> sigma_Mx X" by simp
    next
      fix A
      fix B
      assume "A \<in> sigma_Mx X"
             "B \<in> sigma_Mx X"
      then have "\<exists> Ua. A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets real_borel)"
        by (simp add: sigma_Mx_def)
      then obtain Ua where pa:"A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets real_borel)" by auto
      have "\<exists> Ub. B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets real_borel)"
        using \<open>B \<in> sigma_Mx X\<close> sigma_Mx_def by auto
      then obtain Ub where pb:"B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets real_borel)" by auto
      from pa pb have [simp]:"A - B = (Ua \<inter> -Ub) \<inter> qbs_space X" by auto
      from pa pb have "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -`(Ua \<inter> -Ub) \<in> sets real_borel"
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
      then have "\<exists> Ua. A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets real_borel)"
        by (simp add: sigma_Mx_def)
      then obtain Ua where pa:"A = Ua \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ua \<in> sets real_borel)" by auto
      have "\<exists> Ub. B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets real_borel)"
        using \<open>B \<in> sigma_Mx X\<close> sigma_Mx_def by auto
      then obtain Ub where pb:"B = Ub \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ub \<in> sets real_borel)" by auto
      from pa pb have "A \<union> B = (Ua \<union> Ub) \<inter> qbs_space X" by auto
      from pa pb have "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -`(Ua \<union> Ub) \<in> sets real_borel" by auto
      then show "A \<union> B \<in> sigma_Mx X"
        unfolding sigma_Mx_def
        using \<open>A \<union> B = (Ua \<union> Ub) \<inter> qbs_space X\<close> by blast
    next
      have "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (UNIV) \<in> sets real_borel"
        by simp
      thus "qbs_space X \<in> sigma_Mx X"
        unfolding sigma_Mx_def
        by blast
    qed
  next
    show "sigma_algebra_axioms (sigma_Mx X)"
      unfolding sigma_algebra_axioms_def
    proof(auto)
      fix A :: "nat \<Rightarrow> _"
      assume 1:"range A \<subseteq> sigma_Mx X"
      then have 2:"\<forall>i. \<exists>Ui. A i = Ui \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` Ui \<in> sets real_borel)"
        unfolding sigma_Mx_def by auto
      then have "\<exists> U :: nat \<Rightarrow> _. \<forall>i. A i = U i \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (U i) \<in> sets real_borel)"
        by (rule choice)
      from this obtain U where pu:"\<forall>i. A i = U i \<inter> qbs_space X \<and> (\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (U i) \<in> sets real_borel)"
        by auto
      hence "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (\<Union> (range U)) \<in> sets real_borel"
        by (simp add: countable_Un_Int(1) vimage_UN)
      from pu have "\<Union> (range A) = (\<Union>i::nat. (U i \<inter> qbs_space X))" by blast
      hence "\<Union> (range A) = \<Union> (range U) \<inter> qbs_space X" by auto
      thus "\<Union> (range A) \<in> sigma_Mx X"
        using sigma_Mx_def \<open>\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` \<Union> (range U) \<in> sets real_borel\<close> by blast
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


lemma L_correct[simp]:"Rep_measure (qbs_to_measure X) = (qbs_space X, sigma_Mx X, \<lambda>A. (if A = {} then 0 else if A \<in> - sigma_Mx X then 0 else \<infinity>))"
  unfolding qbs_to_measure_def
  by(auto intro!: Abs_measure_inverse simp: measure_space_L)

lemma space_L[simp]: "space (qbs_to_measure X) = qbs_space X"
  by (simp add: space_def)

lemma sets_L[simp]: "sets (qbs_to_measure X) = sigma_Mx X"
  by (simp add: sets_def)

lemma emeasure_L[simp]: "emeasure (qbs_to_measure X) = (\<lambda>A. if A = {} \<or> A \<notin> sigma_Mx X then 0 else \<infinity>)"
  by(auto simp: emeasure_def)

lemma qbs_Mx_sigma_Mx_contra:
  assumes "qbs_space X = qbs_space Y"
      and "qbs_Mx X \<subseteq> qbs_Mx Y"
  shows "sigma_Mx Y \<subseteq> sigma_Mx X"
  using assms by(auto simp: sigma_Mx_def)


text \<open> The following lemma says that @{term qbs_to_measure} is a functor from \textbf{QBS} to \textbf{Meas}. \<close>
lemma l_preserves_morphisms:
  "X \<rightarrow>\<^sub>Q Y \<subseteq> (qbs_to_measure X) \<rightarrow>\<^sub>M (qbs_to_measure Y)"
proof(auto)
  fix f
  assume h:"f \<in> X \<rightarrow>\<^sub>Q Y"
  show "f \<in> (qbs_to_measure X) \<rightarrow>\<^sub>M (qbs_to_measure Y)"
  proof(rule measurableI)
    fix x
    assume "x \<in> space (qbs_to_measure X)"
    then show "f x \<in> space (qbs_to_measure Y)"
      using h by auto
  next
    fix A
    assume "A \<in> sets (qbs_to_measure Y)"
    then obtain Ua where pa:"A = Ua \<inter> qbs_space Y \<and> (\<forall>\<alpha>\<in>qbs_Mx Y. \<alpha> -` Ua \<in> sets real_borel)"
      by (auto simp: sigma_Mx_def)
    have "\<forall>\<alpha>\<in>qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y"
         "\<forall>\<alpha>\<in> qbs_Mx X. \<alpha> -` (f -` (qbs_space Y)) = UNIV"
      using h by auto
    hence "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (f -` A) = \<alpha> -` (f -` Ua)"
      by (simp add: pa)
    from pa this qbs_morphism_def have "\<forall>\<alpha>\<in>qbs_Mx X. \<alpha> -` (f -` A) \<in> sets real_borel"
      by (simp add: vimage_comp \<open>\<forall>\<alpha>\<in>qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y\<close>)
    thus "f -` A \<inter> space (qbs_to_measure X) \<in> sets (qbs_to_measure X)"
      using sigma_Mx_def by auto
  qed
qed


abbreviation "qbs_borel \<equiv> measure_to_qbs borel"

declare [[coercion measure_to_qbs]]

abbreviation real_quasi_borel :: "real quasi_borel" ("\<real>\<^sub>Q") where
"real_quasi_borel \<equiv> qbs_borel"
abbreviation nat_quasi_borel :: "nat quasi_borel" ("\<nat>\<^sub>Q") where
"nat_quasi_borel \<equiv> qbs_borel"
abbreviation ennreal_quasi_borel :: "ennreal quasi_borel" ("\<real>\<^sub>Q\<^sub>\<ge>\<^sub>0") where
"ennreal_quasi_borel \<equiv> qbs_borel"
abbreviation bool_quasi_borel :: "bool quasi_borel" ("\<bool>\<^sub>Q") where
"bool_quasi_borel \<equiv> qbs_borel"


lemma qbs_Mx_is_morphisms:
 "qbs_Mx X = real_quasi_borel \<rightarrow>\<^sub>Q X"
proof(auto)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx X"
  then have "\<alpha> \<in> UNIV \<rightarrow> qbs_space X \<and> (\<forall> f \<in> real_borel \<rightarrow>\<^sub>M real_borel. \<alpha> \<circ> f \<in> qbs_Mx X)"
    by fastforce
  thus "\<alpha> \<in> real_quasi_borel \<rightarrow>\<^sub>Q X"
    by(simp add: qbs_morphism_def)
next
  fix \<alpha>
  assume "\<alpha> \<in> real_quasi_borel \<rightarrow>\<^sub>Q X"
  have "id \<in> qbs_Mx real_quasi_borel" by simp
  then have "\<alpha> \<circ> id \<in> qbs_Mx X"
    using \<open>\<alpha> \<in> real_quasi_borel \<rightarrow>\<^sub>Q X\<close> qbs_morphism_def[of real_quasi_borel X]
    by blast
  then show "\<alpha> \<in> qbs_Mx X" by simp
qed

lemma qbs_Mx_subset_of_measurable:
  "qbs_Mx X \<subseteq> real_borel \<rightarrow>\<^sub>M qbs_to_measure X"
proof
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx X"
  show "\<alpha> \<in> real_borel \<rightarrow>\<^sub>M qbs_to_measure X"
  proof(rule measurableI)
    fix x
    show "\<alpha> x \<in> space (qbs_to_measure X)"
      using qbs_decomp \<open>\<alpha> \<in> qbs_Mx X\<close> by auto
  next
    fix A
    assume "A \<in> sets (qbs_to_measure X)"
    then have "\<alpha> -`(qbs_space X) = UNIV"
      using \<open>\<alpha> \<in> qbs_Mx X\<close> qbs_decomp by auto
    then show "\<alpha> -` A \<inter> space real_borel \<in> sets real_borel"
      using \<open>\<alpha> \<in> qbs_Mx X\<close> \<open>A \<in> sets (qbs_to_measure X)\<close>
      by(auto simp add: sigma_Mx_def)
  qed
qed

lemma L_max_of_measurables:
  assumes "space M = qbs_space X"
      and "qbs_Mx X \<subseteq> real_borel \<rightarrow>\<^sub>M M"
    shows "sets M \<subseteq> sets (qbs_to_measure X)"
proof
  fix U
  assume "U \<in> sets M"
  from sets.sets_into_space[OF this] in_mono[OF assms(2)] measurable_sets_borel[OF _ this]
  show "U \<in> sets (qbs_to_measure X)"
    using assms(1)
    by(auto intro!: exI[where x=U] simp: sigma_Mx_def)
qed


lemma qbs_Mx_are_measurable[simp,measurable]:
  assumes "\<alpha> \<in> qbs_Mx X"
  shows "\<alpha> \<in> real_borel \<rightarrow>\<^sub>M qbs_to_measure X"
  using assms qbs_Mx_subset_of_measurable by auto

lemma measure_to_qbs_cong_sets:
  assumes "sets M = sets N"
  shows "measure_to_qbs M = measure_to_qbs N"
  by(rule qbs_eqI) (simp add: measurable_cong_sets[OF _ assms])

lemma lr_sets[simp,measurable_cong]:
 "sets X \<subseteq> sets (qbs_to_measure (measure_to_qbs X))"
proof auto
  fix U
  assume "U \<in> sets X"
  then have "U \<inter> space X = U" by simp
  moreover have "\<forall>\<alpha>\<in>real_borel \<rightarrow>\<^sub>M X. \<alpha> -` U \<in> sets real_borel"
    using \<open>U \<in> sets X\<close> by(auto simp add: measurable_def)
  ultimately show "U \<in> sigma_Mx (measure_to_qbs X)"
    by(auto simp add: sigma_Mx_def)
qed

lemma(in standard_borel) standard_borel_lr_sets_ident[simp, measurable_cong]:
 "sets (qbs_to_measure (measure_to_qbs M)) = sets M"
proof auto
  fix V
  assume "V \<in> sigma_Mx (measure_to_qbs M)"
  then obtain U where H2: "V = U \<inter> space M \<and> (\<forall>\<alpha>\<in>real_borel \<rightarrow>\<^sub>M M. \<alpha> -` U \<in> sets real_borel)"
    by(auto simp: sigma_Mx_def)
  hence "g -` V = g -` (U \<inter> space M)" by auto
  have "... = g -` U" using g_meas by(auto simp add: measurable_def) 
  hence "f -` g -` U  \<inter> space M \<in> sets M"
    by (meson f_meas g_meas measurable_sets H2)
  moreover have "f -` g -` U  \<inter> space M  =  U \<inter> space M"
    by auto
  ultimately show "V \<in> sets M" using H2 by simp
next
  fix U
  assume "U \<in> sets M"
  then show "U \<in> sigma_Mx (measure_to_qbs M)"
    using lr_sets by auto
qed


subsubsection \<open> The Adjunction \<close>
lemma  lr_adjunction_correspondence :
 "X \<rightarrow>\<^sub>Q (measure_to_qbs Y) = (qbs_to_measure X) \<rightarrow>\<^sub>M Y"
proof(auto)
(* \<subseteq> *)
  fix f
  assume "f \<in> X \<rightarrow>\<^sub>Q (measure_to_qbs Y)"
  show "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y"
  proof(rule measurableI)
    fix x
    assume "x \<in> space (qbs_to_measure X)"
    hence "x \<in> qbs_space X" by simp
    thus "f x \<in> space Y"
      using \<open>f \<in> X \<rightarrow>\<^sub>Q (measure_to_qbs Y)\<close> qbs_morphismE[of f X "measure_to_qbs Y"]
      by auto
  next
    fix A
    assume "A \<in> sets Y"
    have "\<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx (measure_to_qbs Y)"
      using \<open>f \<in> X \<rightarrow>\<^sub>Q (measure_to_qbs Y)\<close> by auto
    hence "\<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> real_borel \<rightarrow>\<^sub>M Y" by simp
    hence "\<forall>\<alpha> \<in> qbs_Mx X. \<alpha> -` (f -` A) \<in> sets real_borel"
      using \<open>A\<in> sets Y\<close> measurable_sets_borel vimage_comp by metis
    thus "f -` A \<inter> space (qbs_to_measure X) \<in> sets (qbs_to_measure X)"
      using sigma_Mx_def by auto
  qed
   
(* \<supseteq> *)
next
  fix f
  assume "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y"
  show "f \<in> X \<rightarrow>\<^sub>Q measure_to_qbs Y"
  proof(rule qbs_morphismI,simp)
    fix \<alpha>
    assume "\<alpha> \<in> qbs_Mx X"
    show "f \<circ> \<alpha> \<in> real_borel \<rightarrow>\<^sub>M Y"
    proof(rule measurableI)
      fix x
      assume "x \<in> space real_borel"
      from this \<open>\<alpha> \<in> qbs_Mx X \<close>qbs_decomp have "\<alpha> x \<in> qbs_space X" by auto
      hence "\<alpha> x \<in> space (qbs_to_measure X)" by simp
      thus "(f \<circ> \<alpha>) x \<in> space Y"
        using \<open>f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y\<close>
        by (metis comp_def measurable_space)
    next
      fix A
      assume "A \<in> sets Y"
      from \<open>f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y\<close> measurable_sets this measurable_def
      have "f -` A \<inter> space (qbs_to_measure X) \<in> sets (qbs_to_measure X)"
        by blast
      hence "f -` A \<inter> qbs_space X \<in> sigma_Mx X" by simp
      then have "\<exists> V. f -` A \<inter> qbs_space X = V \<inter> qbs_space X \<and> (\<forall>\<beta>\<in> qbs_Mx X. \<beta> -` V \<in> sets real_borel)"
        by (simp add:sigma_Mx_def)
      then obtain V where h:"f -` A \<inter> qbs_space X = V \<inter> qbs_space X \<and> (\<forall>\<beta>\<in> qbs_Mx X. \<beta> -` V \<in> sets real_borel)" by auto
      have 1:"\<alpha> -` (f -` A) = \<alpha> -` (f -` A \<inter> qbs_space X)"
        using \<open>\<alpha> \<in> qbs_Mx X\<close> by blast
      have 2:"\<alpha> -` (V \<inter> qbs_space X) = \<alpha> -` V"
        using \<open>\<alpha> \<in> qbs_Mx X\<close> by blast
      from 1 2 h have "(f \<circ> \<alpha>) -` A = \<alpha> -` V" by (simp add: vimage_comp)
      from this h \<open>\<alpha> \<in> qbs_Mx X \<close>show "(f \<circ> \<alpha>) -` A \<inter> space real_borel \<in> sets real_borel" by simp
    qed
  qed
qed

lemma(in standard_borel) standard_borel_r_full_faithful:
  "M \<rightarrow>\<^sub>M Y = measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y"
proof(standard;standard)
  fix h
  assume "h \<in> M \<rightarrow>\<^sub>M Y"
  then show "h \<in> measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y"
    using r_preserves_morphisms by auto
next
  fix h
  assume h:"h \<in> measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y"
  show "h \<in> M \<rightarrow>\<^sub>M Y"
  proof(rule measurableI)
    fix x
    assume "x \<in> space M"
    then show "h x \<in> space Y"
      using h by auto
  next
    fix U
    assume "U \<in> sets Y"
    have "h \<circ> g \<in> real_borel \<rightarrow>\<^sub>M Y"
      using \<open>h \<in> measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y\<close>
      by(simp add: qbs_morphism_def)
    hence "(h \<circ> g) -` U \<in> sets real_borel"
      by (simp add: \<open>U \<in> sets Y\<close> measurable_sets_borel)
    hence "f -` ((h \<circ> g) -` U) \<inter> space M \<in> sets M"
      using f_meas in_borel_measurable_borel by blast
    moreover have "f -` ((h \<circ> g) -` U) \<inter> space M = h -` U \<inter> space M"
      using f_meas by auto
    ultimately show "h -` U \<inter> space M \<in> sets M" by simp
  qed
qed

lemma qbs_morphism_dest[dest]:
  assumes "f \<in> X \<rightarrow>\<^sub>Q measure_to_qbs Y"
  shows "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y"
  using assms lr_adjunction_correspondence by auto

lemma(in standard_borel) qbs_morphism_dest[dest]:
  assumes "k \<in> measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y"
  shows "k \<in> M \<rightarrow>\<^sub>M Y"
  using standard_borel_r_full_faithful assms by auto

lemma qbs_morphism_measurable_intro[intro!]:
  assumes "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M Y"
  shows "f \<in> X \<rightarrow>\<^sub>Q measure_to_qbs Y"
  using assms lr_adjunction_correspondence by auto

lemma(in standard_borel) qbs_morphism_measurable_intro[intro!]:
  assumes "k \<in> M \<rightarrow>\<^sub>M Y"
  shows "k \<in> measure_to_qbs M \<rightarrow>\<^sub>Q measure_to_qbs Y"
  using standard_borel_r_full_faithful assms by auto

text \<open> We can use the measurability prover when we reason about morphisms. \<close>
lemma
  assumes "f \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  shows "(\<lambda>x. 2 * f x + (f x)^2) \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  using assms by auto

lemma
  assumes "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
      and "\<alpha> \<in> qbs_Mx X"
    shows "(\<lambda>x. 2 * f (\<alpha> x) + (f (\<alpha> x))^2) \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  using assms by auto


lemma qbs_morphisn_from_countable:
  fixes X :: "'a quasi_borel"
  assumes "countable (qbs_space X)"
          "qbs_Mx X \<subseteq> real_borel \<rightarrow>\<^sub>M count_space (qbs_space X)"
      and "\<And>i. i \<in> qbs_space X \<Longrightarrow> f i \<in> qbs_space Y"
    shows "f \<in> X \<rightarrow>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx X"
  then have [measurable]: "\<alpha> \<in> real_borel \<rightarrow>\<^sub>M count_space (qbs_space X)"
    using assms(2) ..
  define k :: "'a \<Rightarrow> real \<Rightarrow> _"
    where "k \<equiv> (\<lambda>i _. f i)"
  have "f \<circ> \<alpha> = (\<lambda>r. k (\<alpha> r) r)"
    by(auto simp add: k_def)
  also have "... \<in> qbs_Mx Y"
    by(rule qbs_closed3_dest2[OF assms(1)]) (use assms(3) k_def in simp_all)
  finally show "f \<circ> \<alpha> \<in> qbs_Mx Y" .
qed

corollary nat_qbs_morphism:
  assumes "\<And>n. f n \<in> qbs_space Y"
  shows "f \<in> \<nat>\<^sub>Q \<rightarrow>\<^sub>Q Y"
  using assms measurable_cong_sets[OF refl sets_borel_eq_count_space,of real_borel]
  by(auto intro!: qbs_morphisn_from_countable)

corollary bool_qbs_morphism:
  assumes "\<And>b. f b \<in> qbs_space Y"
  shows "f \<in> \<bool>\<^sub>Q \<rightarrow>\<^sub>Q Y"
  using assms measurable_cong_sets[OF refl sets_borel_eq_count_space,of real_borel]
  by(auto intro!: qbs_morphisn_from_countable)


subsubsection \<open> The Adjunction w.r.t. Ordering\<close>
lemma l_mono:
 "mono qbs_to_measure"
  apply standard
  subgoal for X Y
  proof(induction rule: less_eq_quasi_borel.induct)
    case (1 X Y)
    then show ?case
      by(simp add: less_eq_measure.intros(1))
  next
    case (2 X Y)
    then have "sigma_Mx X \<subseteq> sigma_Mx Y"
      by(auto simp add: sigma_Mx_def)
    then consider "sigma_Mx X \<subset> sigma_Mx Y" | "sigma_Mx X = sigma_Mx Y"
      by auto
    then show ?case
      apply(cases)
       apply(rule less_eq_measure.intros(2))
        apply(simp_all add: 2)
      by(rule less_eq_measure.intros(3),simp_all add: 2)
  qed
  done

lemma r_mono:
 "mono measure_to_qbs"
  apply standard
  subgoal for M N
  proof(induction rule: less_eq_measure.inducts)
    case (1 M N)
    then show ?case
      by(simp add: less_eq_quasi_borel.intros(1))
  next
    case (2 M N)
    then have "real_borel \<rightarrow>\<^sub>M N \<subseteq> real_borel \<rightarrow>\<^sub>M M"
      by(simp add: measurable_mono)
    then consider "real_borel \<rightarrow>\<^sub>M N \<subset> real_borel \<rightarrow>\<^sub>M M" | "real_borel \<rightarrow>\<^sub>M N = real_borel \<rightarrow>\<^sub>M M"
      by auto
    then show ?case
      by cases (rule less_eq_quasi_borel.intros(2),simp_all add: 2)+
  next
    case (3 M N)
    then show ?case
      apply -
      by(rule less_eq_quasi_borel.intros(2)) (simp_all add: measurable_mono)
  qed
  done

lemma rl_order_adjunction:
  "X \<le> qbs_to_measure Y \<longleftrightarrow> measure_to_qbs X \<le> Y"
proof
  assume 1: "X \<le> qbs_to_measure Y"
  then show "measure_to_qbs X \<le> Y"
  proof(induction rule: less_eq_measure.cases)
    case (1 M N)
    then have [simp]:"qbs_space Y = space N"
      by(simp add: 1(2)[symmetric])
    show ?case
      by(rule less_eq_quasi_borel.intros(1),simp add: 1)
  next
    case (2 M N)
    then have [simp]:"qbs_space Y = space N"
      by(simp add: 2(2)[symmetric])
    show ?case
    proof(rule less_eq_quasi_borel.intros(2),simp add:2,auto)
      fix \<alpha>
      assume h:"\<alpha> \<in> qbs_Mx Y"
      show "\<alpha> \<in> real_borel \<rightarrow>\<^sub>M X"
      proof(rule measurableI,simp_all)
        show "\<And>x. \<alpha> x \<in> space X"
          using h by (auto simp add: 2)
      next
        fix A
        assume "A \<in> sets X"
        then have "A \<in> sets (qbs_to_measure Y)"
          using 2 by auto
        then obtain U where
          hu:"A = U \<inter> space N"
             "(\<forall>\<alpha>\<in>qbs_Mx Y. \<alpha> -` U \<in> sets real_borel)"
          by(auto simp add: sigma_Mx_def)
        have "\<alpha> -` A  = \<alpha> -` U"
          using h qbs_decomp[of Y]
          by(auto simp add: hu)
        thus "\<alpha> -` A \<in> sets borel"
          using h hu(2) by simp
      qed
    qed
  next
    case (3 M N)
    then have [simp]:"qbs_space Y = space N"
      by(simp add: 3(2)[symmetric])
    show ?case
    proof(rule less_eq_quasi_borel.intros(2),simp add: 3,auto)
      fix \<alpha>
      assume h:"\<alpha> \<in> qbs_Mx Y"
      show "\<alpha> \<in> real_borel \<rightarrow>\<^sub>M X"
      proof(rule measurableI,simp_all)
        show "\<And>x. \<alpha> x \<in> space X"
          using h by(auto simp: 3)
      next
        fix A
        assume "A \<in> sets X"
        then have "A \<in> sets (qbs_to_measure Y)"
          using 3 by auto
        then obtain U where
          hu:"A = U \<inter> space N"
             "(\<forall>\<alpha>\<in>qbs_Mx Y. \<alpha> -` U \<in> sets real_borel)"
          by(auto simp add: sigma_Mx_def)
        have "\<alpha> -` A  = \<alpha> -` U"
          using h qbs_decomp[of Y]
          by(auto simp add: hu)
        thus "\<alpha> -` A \<in> sets borel"
          using h hu(2) by simp
      qed
    qed
  qed
next
  assume "measure_to_qbs X \<le> Y"
  then show "X \<le> qbs_to_measure Y"
  proof(induction rule: less_eq_quasi_borel.cases)
    case (1 A B)
    have [simp]: "space X = qbs_space A"
      by(simp add: 1(1)[symmetric])
    show ?case
      by(rule less_eq_measure.intros(1)) (simp add: 1)
  next
    case (2 A B)
    then have hmy:"qbs_Mx Y \<subseteq> real_borel \<rightarrow>\<^sub>M X"
      by auto
    have [simp]: "space X = qbs_space A"
      by(simp add: 2(1)[symmetric])
    have "sets X \<subseteq> sigma_Mx Y"
    proof
      fix U
      assume hu:"U \<in> sets X"
      show "U \<in> sigma_Mx Y"
      proof(simp add: sigma_Mx_def,rule exI[where x=U],auto)
        show "\<And>x. x \<in> U \<Longrightarrow> x \<in> qbs_space Y"
          using sets.sets_into_space[OF hu]
          by(auto simp add: 2)
      next
        fix \<alpha>
        assume "\<alpha> \<in> qbs_Mx Y"
        then have "\<alpha> \<in> real_borel \<rightarrow>\<^sub>M X"
          using hmy by(auto)
        thus "\<alpha> -` U \<in> sets real_borel"
          using hu by(simp add: measurable_sets_borel)
      qed
    qed
    then consider "sets X = sigma_Mx Y" | "sets X \<subset> sigma_Mx Y"
      by auto
    then show ?case
    proof cases
      case 1
      show ?thesis
        apply(rule less_eq_measure.intros(3),simp_all add: 1 2)
      proof(rule le_funI)
        fix U
        consider "U = {}" | "U \<notin> sigma_Mx B" | "U \<noteq> {} \<and> U \<in> sigma_Mx B"
          by auto
        then show "emeasure X U \<le> (if U = {} \<or> U \<notin> sigma_Mx B then 0 else \<infinity>)"
        proof cases
          case 1
          then show ?thesis by simp
        next
          case h:2
          then have "U \<notin> sigma_Mx A"
            using qbs_Mx_sigma_Mx_contra[OF 2(3)[symmetric] 2(4)]
            by auto
          hence "U \<notin> sets X"
            using lr_sets 2(1) by auto
          thus ?thesis
            by(simp add: h emeasure_notin_sets)
        next
          case 3
          then show ?thesis
            by simp
        qed
      qed
    next
      case h2:2
      show ?thesis
        by(rule less_eq_measure.intros(2)) (simp add: 2,simp add: h2)
    qed
  qed
qed

end