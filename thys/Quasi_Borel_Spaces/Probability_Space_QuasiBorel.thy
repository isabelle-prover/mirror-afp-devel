(*  Title:   Probability_Space_QuasiBorel.thy
    Author:  Michikazu Hirata, Yasuhiko Minamide, Tokyo Institute of Technology
*)

section \<open>Probability Spaces\<close>

subsection \<open>Probability Measures \<close>

theory Probability_Space_QuasiBorel
  imports Exponent_QuasiBorel
begin

subsubsection \<open> Probability Measures \<close>
type_synonym 'a qbs_prob_t = "'a quasi_borel * (real \<Rightarrow> 'a) * real measure"

locale in_Mx =
  fixes X :: "'a quasi_borel"
    and \<alpha> :: "real \<Rightarrow> 'a"
  assumes in_Mx[simp]:"\<alpha> \<in> qbs_Mx X"

locale qbs_prob = in_Mx X \<alpha> + real_distribution \<mu>
  for X :: "'a quasi_borel" and \<alpha> and \<mu>
begin
declare prob_space_axioms[simp]

lemma m_in_space_prob_algebra[simp]:
 "\<mu> \<in> space (prob_algebra real_borel)"
  using space_prob_algebra[of real_borel] by simp
end

locale pair_qbs_probs = qp1:qbs_prob X \<alpha> \<mu> + qp2:qbs_prob Y \<beta> \<nu>
  for X :: "'a quasi_borel"and \<alpha> \<mu> and Y :: "'b quasi_borel" and \<beta> \<nu>
begin

sublocale pair_prob_space \<mu> \<nu>
  by standard

lemma ab_measurable[measurable]:
 "map_prod \<alpha> \<beta> \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
  using qbs_morphism_map_prod[of \<alpha> "\<real>\<^sub>Q" X \<beta> "\<real>\<^sub>Q" Y] qp1.in_Mx qp2.in_Mx l_preserves_morphisms[of "\<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q" "X \<Otimes>\<^sub>Q Y"]
  by(auto simp: qbs_Mx_is_morphisms)

lemma ab_g_in_Mx[simp]:
 "map_prod \<alpha> \<beta> \<circ> real_real.g \<in> pair_qbs_Mx X Y"
  using qbs_closed1_dest[OF qp1.in_Mx] qbs_closed1_dest[OF qp2.in_Mx]
  by(auto simp add: pair_qbs_Mx_def comp_def)

sublocale qbs_prob "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<beta> \<circ> real_real.g" "distr (\<mu> \<Otimes>\<^sub>M \<nu>) real_borel real_real.f"
  by(auto simp: qbs_prob_def in_Mx_def)

end

locale pair_qbs_prob = qp1:qbs_prob X \<alpha> \<mu> + qp2:qbs_prob Y \<beta> \<nu>
  for X :: "'a quasi_borel"and \<alpha> \<mu> and Y :: "'a quasi_borel" and \<beta> \<nu>
begin

sublocale pair_qbs_probs
  by standard

lemma same_spaces[simp]:
  assumes "Y = X"
  shows "\<beta> \<in> qbs_Mx X"
  by(simp add: assms[symmetric])

end

lemma prob_algebra_real_prob_measure:
  "p \<in> space (prob_algebra (real_borel)) = real_distribution p"
proof
  assume "p \<in> space (prob_algebra real_borel)"
  then show "real_distribution p"
    unfolding real_distribution_def real_distribution_axioms_def
    by(simp add: space_prob_algebra sets_eq_imp_space_eq)
next
  assume "real_distribution p"
  then interpret rd: real_distribution p .
  show "p \<in> space (prob_algebra real_borel)"
    by (simp add: space_prob_algebra rd.prob_space_axioms)
qed

lemma qbs_probI:
  assumes "\<alpha> \<in> qbs_Mx X"
      and "sets \<mu> = sets borel"
      and "prob_space \<mu>"
    shows "qbs_prob X \<alpha> \<mu>"
  using assms
  by(auto intro!: qbs_prob.intro simp: in_Mx_def real_distribution_def real_distribution_axioms_def)

lemma qbs_empty_not_qbs_prob :"\<not> qbs_prob (empty_quasi_borel) f M"
  by(simp add: qbs_prob_def in_Mx_def)

definition qbs_prob_eq :: "['a qbs_prob_t, 'a qbs_prob_t] \<Rightarrow> bool" where
  "qbs_prob_eq p1 p2 \<equiv>
   (let (qbs1, a1, m1) = p1;
        (qbs2, a2, m2) = p2 in
    qbs_prob qbs1 a1 m1 \<and> qbs_prob qbs2 a2 m2 \<and> qbs1 = qbs2 \<and>
      distr m1 (qbs_to_measure qbs1) a1 = distr m2 (qbs_to_measure qbs2) a2)"

definition qbs_prob_eq2 :: "['a qbs_prob_t, 'a qbs_prob_t] \<Rightarrow> bool" where
  "qbs_prob_eq2 p1 p2 \<equiv>
   (let (qbs1, a1, m1) = p1;
        (qbs2, a2, m2) = p2 in
    qbs_prob qbs1 a1 m1 \<and> qbs_prob qbs2 a2 m2 \<and> qbs1 = qbs2 \<and>
      (\<forall>f \<in> qbs1 \<rightarrow>\<^sub>Q real_quasi_borel.
           (\<integral>x. f (a1 x) \<partial> m1) = (\<integral>x. f (a2 x) \<partial> m2)))"

definition qbs_prob_eq3 :: "['a qbs_prob_t, 'a qbs_prob_t] \<Rightarrow> bool" where
  "qbs_prob_eq3 p1 p2 \<equiv>
     (let (qbs1, a1, m1) = p1;
          (qbs2, a2, m2) = p2 in
     (qbs_prob qbs1 a1 m1 \<and> qbs_prob qbs2 a2 m2 \<and> qbs1 = qbs2 \<and>
      (\<forall>f \<in> qbs1 \<rightarrow>\<^sub>Q real_quasi_borel.
         (\<forall> k \<in> qbs_space qbs1. 0 \<le> f k) \<longrightarrow>
           (\<integral>x. f (a1 x) \<partial> m1) = (\<integral>x. f (a2 x) \<partial> m2))))"

definition qbs_prob_eq4 :: "['a qbs_prob_t, 'a qbs_prob_t] \<Rightarrow> bool" where
  "qbs_prob_eq4 p1 p2 \<equiv>
     (let (qbs1, a1, m1) = p1;
          (qbs2, a2, m2) = p2 in
     (qbs_prob qbs1 a1 m1 \<and> qbs_prob qbs2 a2 m2 \<and> qbs1 = qbs2 \<and>
      (\<forall>f \<in> qbs1 \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0.
           (\<integral>\<^sup>+x. f (a1 x) \<partial> m1) = (\<integral>\<^sup>+x. f (a2 x) \<partial> m2))))"

lemma(in qbs_prob) qbs_prob_eq_refl[simp]:
 "qbs_prob_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
  by(simp add: qbs_prob_eq_def qbs_prob_axioms)

lemma(in qbs_prob) qbs_prob_eq2_refl[simp]:
 "qbs_prob_eq2 (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
  by(simp add: qbs_prob_eq2_def qbs_prob_axioms)

lemma(in qbs_prob) qbs_prob_eq3_refl[simp]:
 "qbs_prob_eq3 (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
  by(simp add: qbs_prob_eq3_def qbs_prob_axioms)

lemma(in qbs_prob) qbs_prob_eq4_refl[simp]:
 "qbs_prob_eq4 (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
  by(simp add: qbs_prob_eq4_def qbs_prob_axioms)

lemma(in pair_qbs_prob) qbs_prob_eq_intro:
  assumes "X = Y"
      and "distr \<mu> (qbs_to_measure X) \<alpha> = distr \<nu> (qbs_to_measure X) \<beta>"
    shows "qbs_prob_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  using assms qp1.qbs_prob_axioms qp2.qbs_prob_axioms
  by(auto simp add: qbs_prob_eq_def)

lemma(in pair_qbs_prob) qbs_prob_eq2_intro:
  assumes "X = Y"
      and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M real_borel
                 \<Longrightarrow> (\<integral>x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>x. f (\<beta> x) \<partial> \<nu>)"
    shows "qbs_prob_eq2 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  using assms qp1.qbs_prob_axioms qp2.qbs_prob_axioms
  by(auto simp add: qbs_prob_eq2_def)

lemma(in pair_qbs_prob) qbs_prob_eq3_intro:
  assumes "X = Y"
      and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M real_borel \<Longrightarrow> (\<forall> k \<in> qbs_space X. 0 \<le> f k)
                \<Longrightarrow> (\<integral>x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>x. f (\<beta> x) \<partial> \<nu>)"
    shows "qbs_prob_eq3 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  using assms qp1.qbs_prob_axioms qp2.qbs_prob_axioms
  by(auto simp add: qbs_prob_eq3_def)

lemma(in pair_qbs_prob) qbs_prob_eq4_intro:
  assumes "X = Y"
      and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M ennreal_borel
                 \<Longrightarrow> (\<integral>\<^sup>+x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>\<^sup>+x. f (\<beta> x) \<partial> \<nu>)"
    shows "qbs_prob_eq4 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  using assms qp1.qbs_prob_axioms qp2.qbs_prob_axioms
  by(auto simp add: qbs_prob_eq4_def)


lemma qbs_prob_eq_dest:
  assumes "qbs_prob_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  shows "qbs_prob X \<alpha> \<mu>"
        "qbs_prob Y \<beta> \<nu>"
        "Y = X"
    and "distr \<mu> (qbs_to_measure X) \<alpha> = distr \<nu> (qbs_to_measure X) \<beta>"
  using assms by(auto simp: qbs_prob_eq_def)

lemma qbs_prob_eq2_dest:
  assumes "qbs_prob_eq2 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  shows "qbs_prob X \<alpha> \<mu>"
        "qbs_prob Y \<beta> \<nu>"
        "Y = X"
    and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M real_borel
        \<Longrightarrow> (\<integral>x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>x. f (\<beta> x) \<partial> \<nu>)"
  using assms by(auto simp: qbs_prob_eq2_def)

lemma qbs_prob_eq3_dest:
  assumes "qbs_prob_eq3 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  shows "qbs_prob X \<alpha> \<mu>"
        "qbs_prob Y \<beta> \<nu>"
        "Y = X"
    and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M real_borel \<Longrightarrow> (\<forall> k \<in> qbs_space X. 0 \<le> f k)
        \<Longrightarrow> (\<integral>x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>x. f (\<beta> x) \<partial> \<nu>)"
  using assms by(auto simp: qbs_prob_eq3_def)

lemma qbs_prob_eq4_dest:
  assumes "qbs_prob_eq4 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  shows "qbs_prob X \<alpha> \<mu>"
        "qbs_prob Y \<beta> \<nu>"
        "Y = X"
    and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M ennreal_borel
        \<Longrightarrow> (\<integral>\<^sup>+x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>\<^sup>+x. f (\<beta> x) \<partial> \<nu>)"
  using assms by(auto simp: qbs_prob_eq4_def)

definition qbs_prob_t_ennintegral :: "['a qbs_prob_t, 'a \<Rightarrow> ennreal] \<Rightarrow> ennreal" where
"qbs_prob_t_ennintegral p f \<equiv>
  (if f \<in> (fst p) \<rightarrow>\<^sub>Q ennreal_quasi_borel
   then (\<integral>\<^sup>+x. f (fst (snd p) x) \<partial> (snd (snd p))) else 0)"

definition qbs_prob_t_integral :: "['a qbs_prob_t, 'a \<Rightarrow> real] \<Rightarrow> real" where
"qbs_prob_t_integral p f \<equiv>
  (if f \<in> (fst p) \<rightarrow>\<^sub>Q \<real>\<^sub>Q
   then (\<integral>x. f (fst (snd p) x) \<partial> (snd (snd p)))
   else 0)"

definition qbs_prob_t_integrable :: "['a qbs_prob_t, 'a \<Rightarrow> real] \<Rightarrow> bool" where
"qbs_prob_t_integrable p f \<equiv> f \<in> fst p \<rightarrow>\<^sub>Q real_quasi_borel \<and> integrable (snd (snd p)) (f \<circ> (fst (snd p)))"

definition qbs_prob_t_measure :: "'a qbs_prob_t \<Rightarrow> 'a measure" where
"qbs_prob_t_measure p \<equiv> distr (snd (snd p)) (qbs_to_measure (fst p)) (fst (snd p))"

lemma qbs_prob_eq_symp:
 "symp qbs_prob_eq"
  by(simp add: symp_def qbs_prob_eq_def)

lemma qbs_prob_eq_transp:
 "transp qbs_prob_eq"
  by(simp add: transp_def qbs_prob_eq_def)

quotient_type 'a qbs_prob_space = "'a qbs_prob_t" / partial: qbs_prob_eq
  morphisms rep_qbs_prob_space qbs_prob_space
proof(rule part_equivpI)
  let ?U = "UNIV :: 'a set"
  let ?Uf = "UNIV :: (real \<Rightarrow> 'a) set"
  let ?f = "(\<lambda>_. undefined) :: real \<Rightarrow> 'a"
  have "qbs_prob (Abs_quasi_borel (?U,?Uf)) ?f (return borel 0)"
  proof(auto simp add: qbs_prob_def in_Mx_def)
    have "Rep_quasi_borel (Abs_quasi_borel (?U,?Uf)) = (?U, ?Uf)"
      using Abs_quasi_borel_inverse
      by (auto simp add: qbs_closed1_def qbs_closed2_def qbs_closed3_def is_quasi_borel_def)
    thus "(\<lambda>_. undefined) \<in> qbs_Mx (Abs_quasi_borel (?U, ?Uf))"
      by(simp add: qbs_Mx_def)
  next
    show "real_distribution (return borel 0)"
      by (simp add: prob_space_return real_distribution_axioms_def real_distribution_def)
  qed
  thus "\<exists>x :: 'a qbs_prob_t . qbs_prob_eq x x"
    unfolding qbs_prob_eq_def
    by(auto intro!: exI[where x="(Abs_quasi_borel (?U,?Uf), ?f, return borel 0)"])
qed (simp_all add: qbs_prob_eq_symp qbs_prob_eq_transp)

interpretation qbs_prob_space : quot_type "qbs_prob_eq" "Abs_qbs_prob_space" "Rep_qbs_prob_space"
  using Abs_qbs_prob_space_inverse Rep_qbs_prob_space
  by(simp add: quot_type_def equivp_implies_part_equivp qbs_prob_space_equivp Rep_qbs_prob_space_inverse Rep_qbs_prob_space_inject) blast

lemma qbs_prob_space_induct:
  assumes "\<And>X \<alpha> \<mu>. qbs_prob X \<alpha> \<mu> \<Longrightarrow> P (qbs_prob_space (X,\<alpha>,\<mu>))"
  shows "P s"
  apply(rule qbs_prob_space.abs_induct)
  using assms by(auto simp: qbs_prob_eq_def)

lemma qbs_prob_space_induct':
  assumes "\<And>X \<alpha> \<mu>. qbs_prob X \<alpha> \<mu> \<Longrightarrow> s = qbs_prob_space (X,\<alpha>,\<mu>)\<Longrightarrow> P (qbs_prob_space (X,\<alpha>,\<mu>))"
  shows "P s"
  by (metis (no_types, lifting) Rep_qbs_prob_space_inverse assms case_prodE qbs_prob_eq_def qbs_prob_space.abs_def qbs_prob_space.rep_prop qbs_prob_space_def)

lemma rep_qbs_prob_space:
 "\<exists>X \<alpha> \<mu>. p = qbs_prob_space (X, \<alpha>, \<mu>) \<and> qbs_prob X \<alpha> \<mu>"
  by(rule qbs_prob_space.abs_induct,auto simp add: qbs_prob_eq_def)

lemma(in qbs_prob) in_Rep:
  "(X, \<alpha>, \<mu>) \<in> Rep_qbs_prob_space (qbs_prob_space (X,\<alpha>,\<mu>))"
  by (metis mem_Collect_eq qbs_prob_eq_refl qbs_prob_space.abs_def qbs_prob_space.abs_inverse qbs_prob_space_def)

lemma(in qbs_prob) if_in_Rep:
  assumes "(X',\<alpha>',\<mu>') \<in> Rep_qbs_prob_space (qbs_prob_space (X,\<alpha>,\<mu>))"
  shows "X' = X"
        "qbs_prob X' \<alpha>' \<mu>'"
        "qbs_prob_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
proof -
  have h:"X' = X"
    by (metis assms mem_Collect_eq qbs_prob_eq_dest(3) qbs_prob_eq_refl qbs_prob_space.abs_def qbs_prob_space.abs_inverse qbs_prob_space_def)
  have [simp]:"qbs_prob X' \<alpha>' \<mu>'"
    by (metis assms mem_Collect_eq prod_cases3 qbs_prob_eq_dest(2) qbs_prob_space.rep_prop)
  have [simp]:"qbs_prob_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
    by (metis assms mem_Collect_eq qbs_prob_eq_refl qbs_prob_space.abs_def qbs_prob_space.abs_inverse qbs_prob_space_def)
  show "X' = X"
       "qbs_prob X' \<alpha>' \<mu>'"
       "qbs_prob_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
    by simp_all (simp add: h)
qed

lemma(in qbs_prob) in_Rep_induct:
  assumes "\<And>Y \<beta> \<nu>. (Y,\<beta>,\<nu>) \<in> Rep_qbs_prob_space (qbs_prob_space (X,\<alpha>,\<mu>)) \<Longrightarrow> P (Y,\<beta>,\<nu>)"
  shows "P (rep_qbs_prob_space (qbs_prob_space (X,\<alpha>,\<mu>)))"
  unfolding rep_qbs_prob_space_def qbs_prob_space.rep_def
  by(rule someI2[where a="(X,\<alpha>,\<mu>)"]) (use in_Rep assms in auto)

(* qbs_prob_eq[1-4] are equivalent. *)
lemma qbs_prob_eq_2_implies_3 :
  assumes "qbs_prob_eq2 p1 p2"
  shows "qbs_prob_eq3 p1 p2"
  using assms by(auto simp: qbs_prob_eq2_def qbs_prob_eq3_def)

lemma qbs_prob_eq_3_implies_1 :
  assumes "qbs_prob_eq3 (p1 :: 'a qbs_prob_t) p2"
  shows "qbs_prob_eq p1 p2"
proof(rule prod_cases3[where y=p1],rule prod_cases3[where y=p2],simp)
  fix X Y :: "'a quasi_borel"
  fix \<alpha> \<beta> \<mu> \<nu>
  assume "p1 = (X,\<alpha>,\<mu>)" "p2 = (Y,\<beta>,\<nu>)"
  then have h:"qbs_prob_eq3 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
    using assms by simp
  then interpret qp : pair_qbs_prob X \<alpha> \<mu> Y \<beta> \<nu>
    by(auto intro!: pair_qbs_prob.intro simp: qbs_prob_eq3_def)
  note [simp] = qbs_prob_eq3_dest(3)[OF h]

  show "qbs_prob_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  proof(rule qp.qbs_prob_eq_intro)
   show "distr \<mu> (qbs_to_measure X) \<alpha> = distr \<nu> (qbs_to_measure X) \<beta>"
    proof(rule measure_eqI)
      fix U
      assume hu:"U \<in> sets (distr \<mu> (qbs_to_measure X) \<alpha>)"
      have "measure (distr \<mu> (qbs_to_measure X) \<alpha>) U = measure (distr \<nu> (qbs_to_measure X) \<beta>) U"
            (is "?lhs = ?rhs")
      proof -
        have "?lhs = measure \<mu> (\<alpha> -` U \<inter> space \<mu>)"
          by(rule measure_distr) (use hu in simp_all)
        also have "... = integral\<^sup>L \<mu> (indicat_real (\<alpha> -` U))"
          by simp
        also have "... = (\<integral>x. indicat_real U (\<alpha> x) \<partial>\<mu>)"
          using indicator_vimage[of \<alpha> U] Bochner_Integration.integral_cong[of \<mu> _ "indicat_real (\<alpha> -` U)" "\<lambda>x. indicat_real U (\<alpha> x)"]
          by auto
        also have "... = (\<integral>x. indicat_real U (\<beta> x) \<partial>\<nu>)"
          using qbs_prob_eq3_dest(4)[OF h,of "indicat_real U"] hu
          by simp
        also have "... = integral\<^sup>L \<nu> (indicat_real (\<beta> -` U))"
          using indicator_vimage[of \<beta> U,symmetric] Bochner_Integration.integral_cong[of \<nu> _ "\<lambda>x. indicat_real U (\<beta> x)" "indicat_real (\<beta> -` U)"]
          by blast
        also have "... = measure \<nu> (\<beta> -` U \<inter> space \<nu>)"
          by simp
        also have "... = ?rhs"
          by(rule measure_distr[symmetric]) (use hu in simp_all)
        finally show ?thesis .
      qed
      thus "emeasure (distr \<mu> (qbs_to_measure X) \<alpha>) U = emeasure (distr \<nu> (qbs_to_measure X) \<beta>) U"
        using qp.qp2.finite_measure_distr[of \<beta>] qp.qp1.finite_measure_distr[of \<alpha>]
        by(simp add: finite_measure.emeasure_eq_measure)
    qed simp
  qed simp
qed

lemma qbs_prob_eq_1_implies_2 :
  assumes "qbs_prob_eq p1 (p2 :: 'a qbs_prob_t)"
  shows "qbs_prob_eq2 p1 p2"
proof(rule prod_cases3[where y=p1],rule prod_cases3[where y=p2],simp)
  fix X Y :: "'a quasi_borel"
  fix \<alpha> \<beta> \<mu> \<nu>
  assume "p1 = (X,\<alpha>,\<mu>)" "p2 = (Y,\<beta>,\<nu>)"
  then have h:"qbs_prob_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
    using assms by simp
  then interpret qp : pair_qbs_prob X \<alpha> \<mu> Y \<beta> \<nu>
    by(auto intro!: pair_qbs_prob.intro simp: qbs_prob_eq_def)
  note [simp] = qbs_prob_eq_dest(3)[OF h]

  show "qbs_prob_eq2 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  proof(rule qp.qbs_prob_eq2_intro)
    fix f :: "'a \<Rightarrow> real"
    assume [measurable]:"f \<in> borel_measurable (qbs_to_measure X)"
    show "(\<integral>r. f (\<alpha> r) \<partial> \<mu>) = (\<integral>r. f (\<beta> r) \<partial> \<nu>)"
         (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<integral>x. f x \<partial>(distr \<mu> (qbs_to_measure X) \<alpha>))"
        by(simp add: Bochner_Integration.integral_distr[symmetric])
      also have "... = (\<integral>x. f x \<partial>(distr \<nu> (qbs_to_measure X) \<beta>))"
        by(simp add: qbs_prob_eq_dest(4)[OF h])
      also have "... = ?rhs"
        by(simp add: Bochner_Integration.integral_distr)
      finally show ?thesis .
    qed
  qed simp
qed

lemma qbs_prob_eq_1_implies_4 :
  assumes "qbs_prob_eq p1 p2"
  shows "qbs_prob_eq4 p1 p2"
proof(rule prod_cases3[where y=p1],rule prod_cases3[where y=p2],simp)
  fix X Y :: "'a quasi_borel"
  fix \<alpha> \<beta> \<mu> \<nu>
  assume "p1 = (X,\<alpha>,\<mu>)" "p2 = (Y,\<beta>,\<nu>)"
  then have h:"qbs_prob_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
    using assms by simp
  then interpret qp : pair_qbs_prob X \<alpha> \<mu> Y \<beta> \<nu>
    by(auto intro!: pair_qbs_prob.intro simp: qbs_prob_eq_def)
  note [simp] = qbs_prob_eq_dest(3)[OF h]

  show "qbs_prob_eq4 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  proof(rule qp.qbs_prob_eq4_intro)
    fix f ::"'a \<Rightarrow> ennreal"
    assume [measurable]:"f \<in> borel_measurable (qbs_to_measure X)"
    show "(\<integral>\<^sup>+ x. f (\<alpha> x) \<partial>\<mu>) = (\<integral>\<^sup>+ x. f (\<beta> x) \<partial>\<nu>)"
         (is "?lhs = ?rhs")
    proof -
      have "?lhs = integral\<^sup>N (distr \<mu> (qbs_to_measure X) \<alpha>) f"
        by(simp add: nn_integral_distr)
      also have "... = integral\<^sup>N (distr \<nu> (qbs_to_measure X) \<beta>) f"
        by(simp add: qbs_prob_eq_dest(4)[OF h])
      also have "... = ?rhs"
        by(simp add: nn_integral_distr)
      finally show ?thesis .
    qed
  qed simp
qed

lemma qbs_prob_eq_4_implies_3 :
  assumes "qbs_prob_eq4 p1 p2"
  shows "qbs_prob_eq3 p1 p2"
proof(rule prod_cases3[where y=p1],rule prod_cases3[where y=p2],simp)
  fix X Y :: "'a quasi_borel"
  fix \<alpha> \<beta> \<mu> \<nu>
  assume "p1 = (X,\<alpha>,\<mu>)" "p2 = (Y,\<beta>,\<nu>)"
  then have h:"qbs_prob_eq4 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
    using assms by simp
  then interpret qp : pair_qbs_prob X \<alpha> \<mu> Y \<beta> \<nu>
    by(auto intro!: pair_qbs_prob.intro simp: qbs_prob_eq4_def)
  note [simp] = qbs_prob_eq4_dest(3)[OF h]

  show "qbs_prob_eq3 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  proof(rule qp.qbs_prob_eq3_intro)
    fix f :: "'a \<Rightarrow> real"
    assume [measurable]:"f \<in> borel_measurable (qbs_to_measure X)"
       and h': "\<forall>k\<in>qbs_space X. 0 \<le> f k"
    show "(\<integral> x. f (\<alpha> x) \<partial>\<mu>) = (\<integral> x. f (\<beta> x) \<partial>\<nu>)"
         (is "?lhs = ?rhs")
    proof -
      have "?lhs = enn2real (\<integral>\<^sup>+ x. ennreal (f (\<alpha> x)) \<partial>\<mu>)"
        using h' by(auto simp: integral_eq_nn_integral[where f="(\<lambda>x. f (\<alpha> x))"] qbs_Mx_to_X(2))
      also have "... = enn2real (\<integral>\<^sup>+ x. (ennreal \<circ> f) (\<alpha> x) \<partial>\<mu>)"
        by simp
      also have "... = enn2real (\<integral>\<^sup>+ x. (ennreal \<circ> f) (\<beta> x) \<partial>\<nu>)"
        using qbs_prob_eq4_dest(4)[OF h,of "ennreal \<circ> f"] by simp
      also have "... = enn2real (\<integral>\<^sup>+ x. ennreal (f (\<beta> x)) \<partial>\<nu>)"
        by simp
      also have "... = ?rhs"
        using h' by(auto simp: integral_eq_nn_integral[where f="(\<lambda>x. f (\<beta> x))"] qbs_Mx_to_X(2))
      finally show ?thesis .
    qed
  qed simp
qed

lemma qbs_prob_eq_equiv12 :
 "qbs_prob_eq = qbs_prob_eq2"
  using qbs_prob_eq_1_implies_2 qbs_prob_eq_2_implies_3 qbs_prob_eq_3_implies_1
  by blast

lemma qbs_prob_eq_equiv13 :
 "qbs_prob_eq = qbs_prob_eq3"
  using qbs_prob_eq_1_implies_2 qbs_prob_eq_2_implies_3 qbs_prob_eq_3_implies_1
  by blast

lemma qbs_prob_eq_equiv14 :
 "qbs_prob_eq = qbs_prob_eq4"
  using qbs_prob_eq_2_implies_3 qbs_prob_eq_3_implies_1 qbs_prob_eq_1_implies_4 qbs_prob_eq_4_implies_3 qbs_prob_eq_1_implies_2
  by blast

lemma qbs_prob_eq_equiv23 :
 "qbs_prob_eq2 = qbs_prob_eq3"
  using qbs_prob_eq_1_implies_2 qbs_prob_eq_2_implies_3 qbs_prob_eq_3_implies_1
  by blast

lemma qbs_prob_eq_equiv24 :
 "qbs_prob_eq2 = qbs_prob_eq4"
  using qbs_prob_eq_2_implies_3 qbs_prob_eq_4_implies_3 qbs_prob_eq_3_implies_1 qbs_prob_eq_1_implies_4 qbs_prob_eq_1_implies_2
  by blast

lemma qbs_prob_eq_equiv34:
 "qbs_prob_eq3 = qbs_prob_eq4"
  using qbs_prob_eq_3_implies_1 qbs_prob_eq_1_implies_4 qbs_prob_eq_4_implies_3
  by blast

lemma qbs_prob_eq_equiv31 :
 "qbs_prob_eq = qbs_prob_eq3"
  using qbs_prob_eq_1_implies_2 qbs_prob_eq_2_implies_3 qbs_prob_eq_3_implies_1
  by blast

lemma qbs_prob_space_eq:
  assumes "qbs_prob_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  shows "qbs_prob_space (X,\<alpha>,\<mu>) = qbs_prob_space (Y,\<beta>,\<nu>)"
  using Quotient3_rel[OF Quotient3_qbs_prob_space] assms
  by blast

lemma(in pair_qbs_prob) qbs_prob_space_eq:
  assumes "Y = X"
      and "distr \<mu> (qbs_to_measure X) \<alpha> = distr \<nu> (qbs_to_measure X) \<beta>"
    shows "qbs_prob_space (X,\<alpha>,\<mu>) = qbs_prob_space (Y,\<beta>,\<nu>)"
  using assms qbs_prob_eq_intro qbs_prob_space_eq by auto

lemma(in pair_qbs_prob) qbs_prob_space_eq2:
  assumes "Y = X"
      and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M real_borel
                 \<Longrightarrow> (\<integral>x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>x. f (\<beta> x) \<partial> \<nu>)"
    shows "qbs_prob_space (X,\<alpha>,\<mu>) = qbs_prob_space (Y,\<beta>,\<nu>)"
  using qbs_prob_space_eq assms qbs_prob_eq_2_implies_3[of "(X,\<alpha>,\<mu>)" "(Y,\<beta>,\<nu>)"] qbs_prob_eq_3_implies_1[of "(X,\<alpha>,\<mu>)" "(Y,\<beta>,\<nu>)"] qbs_prob_eq2_intro qbs_prob_eq_dest(4)
  by blast

lemma(in pair_qbs_prob) qbs_prob_space_eq3:
  assumes "Y = X"
      and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M real_borel \<Longrightarrow> (\<forall>k\<in> qbs_space X. 0 \<le> f k)
                 \<Longrightarrow> (\<integral>x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>x. f (\<beta> x) \<partial> \<nu>)"
    shows "qbs_prob_space (X,\<alpha>,\<mu>) = qbs_prob_space (Y,\<beta>,\<nu>)"
  using assms qbs_prob_eq_3_implies_1[of "(X,\<alpha>,\<mu>)" "(Y,\<beta>,\<nu>)"] qbs_prob_eq3_intro qbs_prob_space_eq qbs_prob_eq_dest(4)
  by blast

lemma(in pair_qbs_prob) qbs_prob_space_eq4:
  assumes "Y = X"
      and "\<And>f. f \<in> qbs_to_measure X \<rightarrow>\<^sub>M ennreal_borel
                 \<Longrightarrow> (\<integral>\<^sup>+x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>\<^sup>+x. f (\<beta> x) \<partial> \<nu>)"
    shows "qbs_prob_space (X,\<alpha>,\<mu>) = qbs_prob_space (Y,\<beta>,\<nu>)"
  using assms qbs_prob_eq_4_implies_3[of "(X,\<alpha>,\<mu>)" "(Y,\<beta>,\<nu>)"] qbs_prob_space_eq3[OF assms(1)] qbs_prob_eq3_dest(4) qbs_prob_eq4_intro
  by blast

lemma(in pair_qbs_prob) qbs_prob_space_eq_inverse:
  assumes "qbs_prob_space (X,\<alpha>,\<mu>) = qbs_prob_space (Y,\<beta>,\<nu>)"
    shows "qbs_prob_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
      and "qbs_prob_eq2 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
      and "qbs_prob_eq3 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
      and "qbs_prob_eq4 (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  using Quotient3_rel[OF Quotient3_qbs_prob_space,of "(X, \<alpha>, \<mu>)" "(Y,\<beta>,\<nu>)",simplified] assms qp1.qbs_prob_axioms qp2.qbs_prob_axioms
  by(simp_all add: qbs_prob_eq_equiv13[symmetric] qbs_prob_eq_equiv12[symmetric] qbs_prob_eq_equiv14[symmetric])


lift_definition qbs_prob_space_qbs :: "'a qbs_prob_space \<Rightarrow> 'a quasi_borel"
is fst by(auto simp add: qbs_prob_eq_def)

lemma(in qbs_prob) qbs_prob_space_qbs_computation[simp]:
 "qbs_prob_space_qbs (qbs_prob_space (X,\<alpha>,\<mu>)) = X"
  by(simp add: qbs_prob_space_qbs.abs_eq)

lemma rep_qbs_prob_space':
  assumes "qbs_prob_space_qbs s = X"
  shows "\<exists>\<alpha> \<mu>. s = qbs_prob_space (X,\<alpha>,\<mu>) \<and> qbs_prob X \<alpha> \<mu>"
proof -
  obtain X' \<alpha> \<mu> where hs:
   "s = qbs_prob_space (X', \<alpha>, \<mu>)" "qbs_prob X' \<alpha> \<mu>"
    using rep_qbs_prob_space[of s] by auto
  then interpret qp:qbs_prob X' \<alpha> \<mu>
    by simp
  show ?thesis
    using assms hs(2) by(auto simp add: hs(1))
qed

lift_definition qbs_prob_ennintegral :: "['a qbs_prob_space, 'a \<Rightarrow> ennreal] \<Rightarrow> ennreal"
is qbs_prob_t_ennintegral
  by(auto simp add: qbs_prob_t_ennintegral_def qbs_prob_eq_equiv14 qbs_prob_eq4_def)

lift_definition qbs_prob_integral :: "['a qbs_prob_space, 'a \<Rightarrow> real] \<Rightarrow> real"
is qbs_prob_t_integral
  by(auto simp add: qbs_prob_eq_equiv12 qbs_prob_t_integral_def qbs_prob_eq2_def)

syntax
  "_qbs_prob_ennintegral" :: "pttrn \<Rightarrow> ennreal \<Rightarrow> 'a qbs_prob_space \<Rightarrow> ennreal" ("\<integral>\<^sup>+\<^sub>Q((2 _./ _)/ \<partial>_)" [60,61] 110)

translations
 "\<integral>\<^sup>+\<^sub>Q x. f \<partial>p" \<rightleftharpoons> "CONST qbs_prob_ennintegral p (\<lambda>x. f)"

syntax
  "_qbs_prob_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> 'a qbs_prob_space \<Rightarrow> real" ("\<integral>\<^sub>Q((2 _./ _)/ \<partial>_)" [60,61] 110)

translations
 "\<integral>\<^sub>Q x. f \<partial>p" \<rightleftharpoons> "CONST qbs_prob_integral p (\<lambda>x. f)"


text \<open> We define the function \<open>l\<^sub>X \<in> L(P(X)) \<rightarrow>\<^sub>M G(X)\<close>. \<close>
lift_definition qbs_prob_measure :: "'a qbs_prob_space \<Rightarrow> 'a measure"
is qbs_prob_t_measure
  by(auto simp add: qbs_prob_eq_def qbs_prob_t_measure_def)

declare [[coercion qbs_prob_measure]]

lemma(in qbs_prob) qbs_prob_measure_computation[simp]:
  "qbs_prob_measure (qbs_prob_space (X,\<alpha>,\<mu>)) = distr \<mu> (qbs_to_measure X) \<alpha>"
  by (simp add: qbs_prob_measure.abs_eq qbs_prob_t_measure_def)


definition qbs_emeasure ::"'a qbs_prob_space \<Rightarrow> 'a set \<Rightarrow> ennreal" where
"qbs_emeasure s \<equiv> emeasure (qbs_prob_measure s)"

lemma(in qbs_prob) qbs_emeasure_computation[simp]:
  assumes "U \<in> sets (qbs_to_measure X)"
  shows "qbs_emeasure (qbs_prob_space (X,\<alpha>,\<mu>)) U = emeasure \<mu> (\<alpha> -` U)"
  by(simp add: qbs_emeasure_def emeasure_distr[OF _ assms])


definition qbs_measure ::"'a qbs_prob_space \<Rightarrow> 'a set \<Rightarrow> real" where
"qbs_measure s \<equiv> measure (qbs_prob_measure s)"


interpretation qbs_prob_measure_prob_space : prob_space "qbs_prob_measure (s::'a qbs_prob_space)" for s
proof(transfer,auto)
  fix X :: "'a quasi_borel"
  fix \<alpha> \<mu>
  assume "qbs_prob_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
  then interpret qp: qbs_prob X \<alpha> \<mu>
    by(simp add: qbs_prob_eq_def)
  show "prob_space (qbs_prob_t_measure (X,\<alpha>,\<mu>))"
    by(simp add: qbs_prob_t_measure_def qp.prob_space_distr)
qed

lemma qbs_prob_measure_space:
  "qbs_space (qbs_prob_space_qbs s) = space (qbs_prob_measure s)"
  by(transfer,simp add: qbs_prob_t_measure_def)

lemma qbs_prob_measure_sets[measurable_cong]:
  "sets (qbs_to_measure (qbs_prob_space_qbs s)) = sets (qbs_prob_measure s)"
  by(transfer,simp add: qbs_prob_t_measure_def)

lemma(in qbs_prob) qbs_prob_ennintegral_def:
  assumes "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "qbs_prob_ennintegral (qbs_prob_space (X,\<alpha>,\<mu>)) f = (\<integral>\<^sup>+x. f (\<alpha> x) \<partial> \<mu>)"
  by (simp add: assms qbs_prob_ennintegral.abs_eq qbs_prob_t_ennintegral_def)

lemma(in qbs_prob) qbs_prob_ennintegral_def2:
  assumes "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  shows "qbs_prob_ennintegral (qbs_prob_space (X,\<alpha>,\<mu>)) f = integral\<^sup>N (distr \<mu> (qbs_to_measure X) \<alpha>) f"
  using assms by(auto simp add: qbs_prob_ennintegral.abs_eq qbs_prob_t_ennintegral_def qbs_prob_t_measure_def nn_integral_distr)

lemma (in qbs_prob) qbs_prob_ennintegral_not_morphism:
  assumes  "f \<notin> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  shows "qbs_prob_ennintegral (qbs_prob_space (X,\<alpha>,\<mu>)) f = 0"
  by(simp add: assms qbs_prob_ennintegral.abs_eq qbs_prob_t_ennintegral_def)

lemma qbs_prob_ennintegral_def2:
  assumes "qbs_prob_space_qbs s = (X :: 'a quasi_borel)"
      and "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "qbs_prob_ennintegral s f = integral\<^sup>N (qbs_prob_measure s) f"
  using assms
proof(transfer,auto)
  fix X :: "'a quasi_borel" and \<alpha> \<mu> f
  assume "qbs_prob_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
     and h:"f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  then interpret qp : qbs_prob X \<alpha> \<mu>
    by(simp add: qbs_prob_eq_def)
  show "qbs_prob_t_ennintegral (X, \<alpha>, \<mu>) f = integral\<^sup>N (qbs_prob_t_measure (X, \<alpha>, \<mu>)) f"
    using qp.qbs_prob_ennintegral_def2[OF h]
    by(simp add: qbs_prob_ennintegral.abs_eq qbs_prob_t_measure_def)
qed

lemma(in qbs_prob) qbs_prob_integral_def:
  assumes "f \<in> X \<rightarrow>\<^sub>Q real_quasi_borel"
    shows "qbs_prob_integral (qbs_prob_space (X,\<alpha>,\<mu>)) f = (\<integral>x. f (\<alpha> x) \<partial> \<mu>)"
  by (simp add: assms qbs_prob_integral.abs_eq qbs_prob_t_integral_def)

lemma(in qbs_prob) qbs_prob_integral_def2:
 "qbs_prob_integral (qbs_prob_space (X,\<alpha>,\<mu>)) f = integral\<^sup>L (distr \<mu> (qbs_to_measure X) \<alpha>) f"
proof -
  consider "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q" | "f \<notin> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q" by auto
  thus ?thesis
  proof cases
    case h:2
    then have "\<not> integrable (qbs_prob_measure (qbs_prob_space (X,\<alpha>,\<mu>))) f"
      by auto
    thus ?thesis
      using h by(simp add: qbs_prob_integral.abs_eq qbs_prob_t_integral_def not_integrable_integral_eq)
  qed (auto simp add: qbs_prob_integral.abs_eq qbs_prob_t_integral_def integral_distr )
qed

lemma qbs_prob_integral_def2:
  "qbs_prob_integral (s::'a qbs_prob_space) f = integral\<^sup>L (qbs_prob_measure s) f"
proof(transfer,auto)
  fix X :: "'a quasi_borel" and \<mu> \<alpha> f
  assume "qbs_prob_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
  then interpret qp : qbs_prob X \<alpha> \<mu>
    by(simp add: qbs_prob_eq_def)
  show "qbs_prob_t_integral (X,\<alpha>,\<mu>) f = integral\<^sup>L (qbs_prob_t_measure (X,\<alpha>,\<mu>)) f"
    using qp.qbs_prob_integral_def2
    by(simp add: qbs_prob_t_measure_def qbs_prob_integral.abs_eq)
qed

definition qbs_prob_var :: "'a qbs_prob_space \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
"qbs_prob_var s f \<equiv> qbs_prob_integral s (\<lambda>x. (f x - qbs_prob_integral s f)\<^sup>2)"

lemma(in qbs_prob) qbs_prob_var_computation:
  assumes "f \<in> X \<rightarrow>\<^sub>Q real_quasi_borel"
  shows "qbs_prob_var (qbs_prob_space (X,\<alpha>,\<mu>)) f = (\<integral>x. (f (\<alpha> x) - (\<integral>x. f (\<alpha> x) \<partial> \<mu>))\<^sup>2 \<partial> \<mu>)"
proof -
  have "(\<lambda>x. (f x - qbs_prob_integral (qbs_prob_space (X, \<alpha>, \<mu>)) f)\<^sup>2) \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
    using assms by auto
  thus ?thesis
    using assms qbs_prob_integral_def[of "\<lambda>x. (f x - qbs_prob_integral (qbs_prob_space (X,\<alpha>,\<mu>)) f)\<^sup>2"]
    by(simp add: qbs_prob_var_def qbs_prob_integral_def)
qed

lift_definition qbs_integrable :: "['a qbs_prob_space, 'a \<Rightarrow> real] \<Rightarrow> bool"
is qbs_prob_t_integrable
proof auto
  have H:"\<And> (X::'a quasi_borel) Y \<alpha> \<beta> \<mu> \<nu> f.
          qbs_prob_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>) \<Longrightarrow> qbs_prob_t_integrable (X,\<alpha>,\<mu>) f \<Longrightarrow> qbs_prob_t_integrable (Y,\<beta>,\<nu>) f"
  proof -
    fix X Y :: "'a quasi_borel"
    fix \<alpha> \<beta> \<mu> \<nu> f
    assume H0:"qbs_prob_eq (X, \<alpha>, \<mu>) (Y, \<beta>, \<nu>)"
              "qbs_prob_t_integrable (X, \<alpha>, \<mu>) f"
    then interpret qp: pair_qbs_prob X \<alpha> \<mu> Y \<beta> \<nu>
      by(auto intro!: pair_qbs_prob.intro simp: qbs_prob_eq_def)
    have [measurable]: "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M real_borel"
                and h: "integrable \<mu> (f \<circ> \<alpha>)"
      using H0 by(auto simp: qbs_prob_t_integrable_def)
    note [simp] = qbs_prob_eq_dest(3)[OF H0(1)]

    show "qbs_prob_t_integrable (Y, \<beta>, \<nu>) f"
      unfolding qbs_prob_t_integrable_def
    proof auto
      have "integrable (distr \<mu> (qbs_to_measure X) \<alpha>) f"
        using h by(simp add: comp_def integrable_distr_eq)
      hence "integrable (distr \<nu> (qbs_to_measure X) \<beta>) f"
        using qbs_prob_eq_dest(4)[OF H0(1)] by simp
      thus "integrable \<nu> (f \<circ> \<beta>)"
        by(simp add: comp_def integrable_distr_eq)
    qed
  qed
  fix X Y :: "'a quasi_borel"
  fix \<alpha> \<beta> \<mu> \<nu>
  assume H0:"qbs_prob_eq (X, \<alpha>, \<mu>) (Y, \<beta>, \<nu>)"
  then have H1:"qbs_prob_eq (Y, \<beta>, \<nu>) (X, \<alpha>, \<mu>)"
    by(auto simp add: qbs_prob_eq_def)
  show "qbs_prob_t_integrable (X, \<alpha>, \<mu>) = qbs_prob_t_integrable (Y, \<beta>, \<nu>)"
    using H[OF H0] H[OF H1] by auto
qed

lemma(in qbs_prob) qbs_integrable_def:
 "qbs_integrable (qbs_prob_space (X, \<alpha>, \<mu>)) f = (f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q \<and> integrable \<mu> (f \<circ> \<alpha>))"
  by (simp add: qbs_integrable.abs_eq qbs_prob_t_integrable_def)

lemma qbs_integrable_morphism:
  assumes "qbs_prob_space_qbs s = X"
      and "qbs_integrable s f"
    shows "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q"
  using assms by(transfer,auto simp: qbs_prob_t_integrable_def)

lemma(in qbs_prob) qbs_integrable_measurable[simp,measurable]:
  assumes "qbs_integrable (qbs_prob_space (X,\<alpha>,\<mu>)) f"
  shows "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M real_borel"
  using assms by(auto simp add: qbs_integrable_def)

lemma qbs_integrable_iff_integrable:
  "(qbs_integrable (s::'a qbs_prob_space) f) = (integrable (qbs_prob_measure s) f)"
  apply transfer
  subgoal for s f
  proof(rule prod_cases3[where y=s],simp)
    fix X :: "'a quasi_borel"
    fix \<alpha> \<mu>
    assume "qbs_prob_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
    then interpret qp: qbs_prob X \<alpha> \<mu>
      by(simp add: qbs_prob_eq_def)

    show "qbs_prob_t_integrable (X,\<alpha>,\<mu>) f = integrable (qbs_prob_t_measure (X,\<alpha>,\<mu>)) f"
         (is "?lhs = ?rhs")
      using integrable_distr_eq[of \<alpha> \<mu> "qbs_to_measure X" f]
      by(auto simp add: qbs_prob_t_integrable_def qbs_prob_t_measure_def comp_def)
  qed
  done

lemma(in qbs_prob) qbs_integrable_iff_integrable_distr:
 "qbs_integrable (qbs_prob_space (X,\<alpha>,\<mu>)) f = integrable (distr \<mu> (qbs_to_measure X) \<alpha>) f"
  by(simp add: qbs_integrable_iff_integrable)

lemma(in qbs_prob) qbs_integrable_iff_integrable:
  assumes "f \<in>  qbs_to_measure X \<rightarrow>\<^sub>M real_borel"
  shows "qbs_integrable (qbs_prob_space (X,\<alpha>,\<mu>)) f = integrable \<mu> (\<lambda>x. f (\<alpha> x))"
  by(auto intro!: integrable_distr_eq[of \<alpha> \<mu> "qbs_to_measure X" f] simp: assms qbs_integrable_iff_integrable_distr)

lemma qbs_integrable_if_integrable:
  assumes "integrable (qbs_prob_measure s) f"
  shows "qbs_integrable (s::'a qbs_prob_space) f"
  using assms by(simp add: qbs_integrable_iff_integrable)

lemma integrable_if_qbs_integrable:
  assumes "qbs_integrable (s::'a qbs_prob_space) f"
  shows "integrable (qbs_prob_measure s) f"
  using assms by(simp add: qbs_integrable_iff_integrable)

lemma qbs_integrable_iff_bounded:
  assumes "qbs_prob_space_qbs s = X"
  shows "qbs_integrable s f \<longleftrightarrow> f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q \<and> qbs_prob_ennintegral s (\<lambda>x. ennreal \<bar>f x \<bar>) < \<infinity>"
        (is "?lhs = ?rhs")
proof -
  obtain \<alpha> \<mu> where hs:
   "qbs_prob X \<alpha> \<mu>" "s = qbs_prob_space (X,\<alpha>,\<mu>)"
    using rep_qbs_prob_space'[OF assms] by auto
  then interpret qp:qbs_prob X \<alpha> \<mu> by simp
  have "?lhs = integrable (distr \<mu> (qbs_to_measure X) \<alpha>) f"
    by (simp add: hs(2) qbs_integrable_iff_integrable)
  also have "... = (f \<in> borel_measurable (distr \<mu> (qbs_to_measure X) \<alpha>) \<and> ((\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>(distr \<mu> (qbs_to_measure X) \<alpha>)) < \<infinity>))"
    by(rule integrable_iff_bounded)
  also have "... = ?rhs"
  proof -
    have [simp]:"f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q \<Longrightarrow>(\<lambda>x. ennreal \<bar>f x\<bar>) \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      by auto
    have "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q \<Longrightarrow> qbs_prob_ennintegral s (\<lambda>x. ennreal \<bar>f x\<bar>) = (\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>qbs_prob_measure s)"
      using qp.qbs_prob_ennintegral_def2[of "\<lambda>x. ennreal \<bar>f x\<bar>"]
      by(auto simp: hs(2))
    thus ?thesis
      by(simp add: hs(2)) fastforce
  qed
  finally show ?thesis .
qed

lemma qbs_integrable_cong:
  assumes "qbs_prob_space_qbs s = X"
          "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
      and "qbs_integrable s f"
    shows "qbs_integrable s g"
  by (metis Bochner_Integration.integrable_cong assms integrable_if_qbs_integrable qbs_integrable_if_integrable qbs_prob_measure_space)

lemma qbs_integrable_const[simp]:
 "qbs_integrable s (\<lambda>x. c)"
  using qbs_integrable_iff_integrable[of s "\<lambda>x. c"] by simp

lemma qbs_integrable_add[simp]:
  assumes "qbs_integrable s f"
      and "qbs_integrable s g"
    shows "qbs_integrable s (\<lambda>x. f x + g x)"
  using assms qbs_integrable_iff_integrable by blast

lemma qbs_integrable_diff[simp]:
  assumes "qbs_integrable s f"
      and "qbs_integrable s g"
    shows "qbs_integrable s (\<lambda>x. f x - g x)"
  by(rule qbs_integrable_if_integrable[OF Bochner_Integration.integrable_diff[OF integrable_if_qbs_integrable[OF assms(1)] integrable_if_qbs_integrable[OF assms(2)]]])

lemma qbs_integrable_mult_iff[simp]:
 "(qbs_integrable s (\<lambda>x. c * f x)) = (c = 0 \<or> qbs_integrable s f)"
  using qbs_integrable_iff_integrable[of s "\<lambda>x. c * f x"] integrable_mult_left_iff[of "qbs_prob_measure s" c f] qbs_integrable_iff_integrable[of s f]
  by simp

lemma qbs_integrable_mult[simp]:
  assumes "qbs_integrable s f"
  shows "qbs_integrable s (\<lambda>x. c * f x)"
  using assms qbs_integrable_mult_iff by auto

lemma qbs_integrable_abs[simp]:
  assumes "qbs_integrable s f"
  shows "qbs_integrable s (\<lambda>x. \<bar>f x\<bar>)"
  by(rule qbs_integrable_if_integrable[OF integrable_abs[OF integrable_if_qbs_integrable[OF assms]]])

lemma qbs_integrable_sq[simp]:
  assumes "qbs_integrable s f"
      and "qbs_integrable s (\<lambda>x. (f x)\<^sup>2)"
    shows "qbs_integrable s (\<lambda>x. (f x - c)\<^sup>2)"
  by(simp add: comm_ring_1_class.power2_diff,rule qbs_integrable_diff,rule qbs_integrable_add)
    (simp_all add: comm_semiring_1_class.semiring_normalization_rules(16)[of 2] assms)

lemma qbs_ennintegral_eq_qbs_integral:
  assumes "qbs_prob_space_qbs s = X"
          "qbs_integrable s f"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> 0 \<le> f x"
    shows "qbs_prob_ennintegral s (\<lambda>x. ennreal (f x)) = ennreal (qbs_prob_integral s f)"
  using nn_integral_eq_integral[OF integrable_if_qbs_integrable[OF assms(2)]] assms qbs_prob_ennintegral_def2[OF assms(1) qbs_morphism_comp[OF qbs_integrable_morphism[OF assms(1,2)],of ennreal "\<real>\<^sub>Q\<^sub>\<ge>\<^sub>0",simplified comp_def]] measurable_ennreal
  by (metis AE_I2 qbs_prob_integral_def2 qbs_prob_measure_space real.standard_borel_r_full_faithful)

lemma qbs_prob_ennintegral_cong:
  assumes "qbs_prob_space_qbs s = X"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
    shows "qbs_prob_ennintegral s f = qbs_prob_ennintegral s g"
proof -
  obtain \<alpha> \<mu> where hs:
  "s = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_prob_space'[OF assms(1)] by auto
  then interpret qp : qbs_prob  X \<alpha> \<mu>
    by simp
  have H1:"f \<circ> \<alpha> = g \<circ> \<alpha>"
    using assms(2)
    unfolding comp_def apply standard
    using assms(2)[of "\<alpha> _"] by (simp add: qbs_Mx_to_X(2))
  consider "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0" | "f \<notin> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0" by auto
  then have "qbs_prob_t_ennintegral (X,\<alpha>,\<mu>) f = qbs_prob_t_ennintegral (X,\<alpha>,\<mu>) g"
  proof cases
    case h:1
    then have "g \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      using qbs_morphism_cong[of X f g "\<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"] assms by simp
    then show ?thesis
      using h H1 by(simp add: qbs_prob_t_ennintegral_def comp_def)
  next
    case h:2
    then have "g \<notin> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      using assms qbs_morphism_cong[of X g f "\<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"] by auto
    then show ?thesis
      using h by(simp add: qbs_prob_t_ennintegral_def)
  qed
  thus ?thesis
    using hs(1) by (simp add: qbs_prob_ennintegral.abs_eq)
qed


lemma qbs_prob_ennintegral_const:
 "qbs_prob_ennintegral (s::'a qbs_prob_space) (\<lambda>x. c) = c"
  using qbs_prob_ennintegral_def2[OF _ qbs_morphism_const[of c "\<real>\<^sub>Q\<^sub>\<ge>\<^sub>0" "qbs_prob_space_qbs s",simplified]]
  by (simp add: qbs_prob_measure_prob_space.emeasure_space_1)

lemma qbs_prob_ennintegral_add:
  assumes "qbs_prob_space_qbs s = X"
          "f \<in> (X::'a quasi_borel) \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      and "g \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
    shows "qbs_prob_ennintegral s (\<lambda>x. f x + g x) = qbs_prob_ennintegral s f + qbs_prob_ennintegral s g"
  using qbs_prob_ennintegral_def2[of s X "\<lambda>x. f x + g x"] qbs_prob_ennintegral_def2[OF assms(1,2)] qbs_prob_ennintegral_def2[OF assms(1,3)] assms nn_integral_add[of f "qbs_prob_measure s" g]
  by fastforce

lemma qbs_prob_ennintegral_cmult:
  assumes "qbs_prob_space_qbs s = X"
      and "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
  shows "qbs_prob_ennintegral s (\<lambda>x. c * f x) = c * qbs_prob_ennintegral s f"
  using qbs_prob_ennintegral_def2[OF assms(1),of "\<lambda>x. c * f x"] qbs_prob_ennintegral_def2[OF assms(1,2)] nn_integral_cmult[of f "qbs_prob_measure s"] assms
  by fastforce

lemma qbs_prob_ennintegral_cmult_noninfty:
  assumes "c \<noteq> \<infinity>"
  shows "qbs_prob_ennintegral s (\<lambda>x. c * f x) = c * qbs_prob_ennintegral s f"
proof -
  obtain X \<alpha> \<mu> where hs:
   "s = qbs_prob_space (X, \<alpha>, \<mu>)" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_prob_space[of s] by auto
  then interpret qp: qbs_prob X \<alpha> \<mu> by simp
  consider "f \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0" | "f \<notin> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(auto intro!: qbs_prob_ennintegral_cmult[where X=X] simp: hs(1))
  next
    case 2
    consider "c = 0" | "c \<noteq> 0 \<and> c \<noteq> \<infinity>"
      using assms by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        by(simp add: hs qbs_prob_ennintegral.abs_eq qbs_prob_t_ennintegral_def)
    next
      case h:2
      have "(\<lambda>x. c * f x) \<notin> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
      proof(rule ccontr)
        assume "\<not> (\<lambda>x. c * f x) \<notin> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q\<^sub>\<ge>\<^sub>0"
        hence 3:"(\<lambda>x. c * f x) \<in> qbs_to_measure X \<rightarrow>\<^sub>M ennreal_borel"
          by auto
        have "f = (\<lambda>x. (1/c) *  (c * f x))"
          using h by(simp add: divide_eq_1_ennreal ennreal_divide_times mult.assoc mult.commute[of c] mult_divide_eq_ennreal)
        also have "... \<in> qbs_to_measure X \<rightarrow>\<^sub>M ennreal_borel"
          using 3 by simp
        finally show False
          using 2 by auto
      qed
      thus ?thesis
        using qp.qbs_prob_ennintegral_not_morphism 2
        by(simp add: hs(1))
    qed
  qed
qed

lemma qbs_prob_integral_cong:
  assumes "qbs_prob_space_qbs s = X"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
    shows "qbs_prob_integral s f = qbs_prob_integral s g"
  by(simp add: qbs_prob_integral_def2) (metis Bochner_Integration.integral_cong assms(1) assms(2) qbs_prob_measure_space)

lemma qbs_prob_integral_nonneg:
  assumes "qbs_prob_space_qbs s = X"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> qbs_prob_integral s f"
  using qbs_prob_measure_space[of s] assms
  by(simp add: qbs_prob_integral_def2)

lemma qbs_prob_integral_mono:
  assumes "qbs_prob_space_qbs s = X"
          "qbs_integrable (s :: 'a qbs_prob_space) f"
          "qbs_integrable s g"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x \<le> g x"
    shows "qbs_prob_integral s f \<le> qbs_prob_integral s g"
  using integral_mono[OF integrable_if_qbs_integrable[OF assms(2)] integrable_if_qbs_integrable[OF assms(3)] assms(4)[simplified qbs_prob_measure_space]]
  by(simp add: qbs_prob_integral_def2 assms(1) qbs_prob_measure_space[symmetric])

lemma qbs_prob_integral_const:
  "qbs_prob_integral (s::'a qbs_prob_space) (\<lambda>x. c) = c"
  by(simp add: qbs_prob_integral_def2 qbs_prob_measure_prob_space.prob_space)

lemma qbs_prob_integral_add:
  assumes "qbs_integrable (s::'a qbs_prob_space) f"
      and "qbs_integrable s g"
    shows "qbs_prob_integral s (\<lambda>x. f x + g x) = qbs_prob_integral s f + qbs_prob_integral s g"
  using Bochner_Integration.integral_add[OF integrable_if_qbs_integrable[OF assms(1)] integrable_if_qbs_integrable[OF assms(2)]]
  by(simp add: qbs_prob_integral_def2)

lemma qbs_prob_integral_diff:
  assumes "qbs_integrable (s::'a qbs_prob_space) f"
      and "qbs_integrable s g"
    shows "qbs_prob_integral s (\<lambda>x. f x - g x) = qbs_prob_integral s f - qbs_prob_integral s g"
  using Bochner_Integration.integral_diff[OF integrable_if_qbs_integrable[OF assms(1)] integrable_if_qbs_integrable[OF assms(2)]]
  by(simp add: qbs_prob_integral_def2)

lemma qbs_prob_integral_cmult:
  "qbs_prob_integral s (\<lambda>x. c * f x) = c * qbs_prob_integral s f"
  by(simp add: qbs_prob_integral_def2)

lemma real_qbs_prob_integral_def:
  assumes "qbs_integrable (s::'a qbs_prob_space) f"
  shows "qbs_prob_integral s f = enn2real (qbs_prob_ennintegral s (\<lambda>x. ennreal (f x))) - enn2real (qbs_prob_ennintegral s (\<lambda>x. ennreal (- f x)))"
  using assms
proof(transfer,auto)
  fix X :: "'a quasi_borel"
  fix \<alpha> \<mu> f
  assume H:"qbs_prob_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
           "qbs_prob_t_integrable (X,\<alpha>,\<mu>) f"
  then interpret qp: qbs_prob X \<alpha> \<mu>
    by(simp add: qbs_prob_eq_def)
  show "qbs_prob_t_integral (X,\<alpha>,\<mu>) f = enn2real (qbs_prob_t_ennintegral (X,\<alpha>,\<mu>) (\<lambda>x. ennreal (f x))) - enn2real (qbs_prob_t_ennintegral (X,\<alpha>,\<mu>) (\<lambda>x. ennreal (- f x)))"
    using H(2) real_lebesgue_integral_def[of \<mu> "f \<circ> \<alpha>"]
    by(auto simp add: comp_def qbs_prob_t_integrable_def qbs_prob_t_integral_def qbs_prob_t_ennintegral_def)
qed

lemma qbs_prob_var_eq:
  assumes "qbs_integrable (s::'a qbs_prob_space) f"
      and "qbs_integrable s (\<lambda>x. (f x)\<^sup>2)"
    shows "qbs_prob_var s f = qbs_prob_integral s (\<lambda>x. (f x)\<^sup>2) - (qbs_prob_integral s f)\<^sup>2"
  unfolding qbs_prob_var_def using assms
proof(transfer,auto)
  fix X :: "'a quasi_borel"
  fix \<alpha> \<mu> f
  assume H:"qbs_prob_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
           "qbs_prob_t_integrable (X,\<alpha>,\<mu>) f"
           "qbs_prob_t_integrable (X,\<alpha>,\<mu>) (\<lambda>x. (f x)\<^sup>2)"
  then interpret qp: qbs_prob X \<alpha> \<mu>
    by(simp add: qbs_prob_eq_def)
  show "qbs_prob_t_integral (X,\<alpha>,\<mu>) (\<lambda>x. (f x - qbs_prob_t_integral (X,\<alpha>,\<mu>) f)\<^sup>2) = qbs_prob_t_integral (X,\<alpha>,\<mu>) (\<lambda>x. (f x)\<^sup>2) - (qbs_prob_t_integral (X,\<alpha>,\<mu>) f)\<^sup>2"
    using H(2,3) prob_space.variance_eq[of \<mu> "f \<circ> \<alpha>"]
    by(auto simp add: qbs_prob_t_integral_def qbs_prob_def qbs_prob_t_integrable_def comp_def qbs_prob_eq_def)
qed

lemma qbs_prob_var_affine:
  assumes "qbs_integrable s f"
  shows "qbs_prob_var s (\<lambda>x. a * f x + b) = a\<^sup>2 * qbs_prob_var s f"
        (is "?lhs = ?rhs")
proof -
  have "?lhs = qbs_prob_integral s (\<lambda>x. (a * f x + b - (a * qbs_prob_integral s f + b))\<^sup>2)"
    using qbs_prob_integral_add[OF qbs_integrable_mult[OF assms,of a] qbs_integrable_const[of s b]]
    by (simp add: qbs_prob_integral_cmult qbs_prob_integral_const qbs_prob_var_def)
  also have "... = qbs_prob_integral s (\<lambda>x. (a * f x - a * qbs_prob_integral s f)\<^sup>2)"
    by simp
  also have "... = qbs_prob_integral s (\<lambda>x. a\<^sup>2 * (f x - qbs_prob_integral s f)\<^sup>2)"
    by (metis power_mult_distrib right_diff_distrib)
  also have "... = ?rhs"
    by(simp add: qbs_prob_var_def qbs_prob_integral_cmult[of s "a\<^sup>2"])
  finally show ?thesis .
qed

lemma qbs_prob_integral_Markov_inequality:
  assumes "qbs_prob_space_qbs s = X"
      and "qbs_integrable s f"
          "\<And>x. x \<in> qbs_space X \<Longrightarrow> 0 \<le> f x"
      and "0 < c"
    shows "qbs_emeasure s {x \<in> qbs_space X. c \<le> f x} \<le> ennreal (1/c * qbs_prob_integral s f)"
  using integral_Markov_inequality[OF integrable_if_qbs_integrable[OF assms(2)] _ assms(4)] assms(3)
  by(force simp add: qbs_prob_integral_def2 qbs_prob_measure_space qbs_emeasure_def assms(1) qbs_prob_measure_space[symmetric])

lemma qbs_prob_integral_Markov_inequality':
  assumes "qbs_prob_space_qbs s = X"
          "qbs_integrable s f"
          "\<And>x. x \<in> qbs_space (qbs_prob_space_qbs s) \<Longrightarrow> 0 \<le> f x"
      and "0 < c"
    shows "qbs_measure s {x \<in> qbs_space (qbs_prob_space_qbs s). c \<le> f x} \<le> (1/c * qbs_prob_integral s f)"
  using qbs_prob_integral_Markov_inequality[OF assms] ennreal_le_iff[of "1/c * qbs_prob_integral s f" "qbs_measure s {x \<in> qbs_space (qbs_prob_space_qbs s). c \<le> f x}"] qbs_prob_integral_nonneg[of s X f,OF assms(1,3)] assms(4)
  by(simp add: qbs_measure_def qbs_emeasure_def qbs_prob_measure_prob_space.emeasure_eq_measure assms(1))

lemma qbs_prob_integral_Markov_inequality_abs:
  assumes "qbs_prob_space_qbs s = X"
          "qbs_integrable s f"
      and "0 < c"
    shows "qbs_emeasure s {x \<in> qbs_space X. c \<le> \<bar>f x\<bar>} \<le> ennreal (1/c * qbs_prob_integral s (\<lambda>x. \<bar>f x\<bar>))"
  using qbs_prob_integral_Markov_inequality[OF assms(1) qbs_integrable_abs[OF assms(2)] _ assms(3)]
  by(simp add: assms(1))

lemma qbs_prob_integral_Markov_inequality_abs':
  assumes "qbs_prob_space_qbs s = X"
          "qbs_integrable s f"
      and "0 < c"
    shows "qbs_measure s {x \<in> qbs_space X. c \<le> \<bar>f x\<bar>} \<le> (1/c * qbs_prob_integral s (\<lambda>x. \<bar>f x\<bar>))"
  using qbs_prob_integral_Markov_inequality'[OF assms(1) qbs_integrable_abs[OF assms(2)] _ assms(3)]
  by(simp add: assms(1))

lemma qbs_prob_integral_real_Markov_inequality:
  assumes "qbs_prob_space_qbs s = \<real>\<^sub>Q"
          "qbs_integrable s f"
      and "0 < c"
    shows "qbs_emeasure s {r. c \<le> \<bar>f r\<bar>} \<le> ennreal (1/c * qbs_prob_integral s (\<lambda>x. \<bar>f x\<bar>))"
  using qbs_prob_integral_Markov_inequality_abs[OF assms]
  by simp

lemma qbs_prob_integral_real_Markov_inequality':
  assumes "qbs_prob_space_qbs s = \<real>\<^sub>Q"
          "qbs_integrable s f"
      and "0 < c"
    shows "qbs_measure s {r. c \<le> \<bar>f r\<bar>} \<le> 1/c * qbs_prob_integral s (\<lambda>x. \<bar>f x\<bar>)"
  using qbs_prob_integral_Markov_inequality_abs'[OF assms]
  by simp

lemma qbs_prob_integral_Chebyshev_inequality:
  assumes "qbs_prob_space_qbs s = X"
          "qbs_integrable s f"
          "qbs_integrable s (\<lambda>x. (f x)\<^sup>2)"
      and "0 < b"
    shows "qbs_measure s {x \<in> qbs_space X. b \<le> \<bar>f x - qbs_prob_integral s f\<bar>} \<le> 1 / b\<^sup>2 * qbs_prob_var s f"
proof -
  have "qbs_integrable s (\<lambda>x. \<bar>f x - qbs_prob_integral s f\<bar>\<^sup>2)"
    by(simp, rule qbs_integrable_sq[OF assms(2,3)])
  moreover have "{x \<in> qbs_space X. b\<^sup>2 \<le> \<bar>f x - qbs_prob_integral s f\<bar>\<^sup>2} = {x \<in> qbs_space X. b \<le> \<bar>f x - qbs_prob_integral s f\<bar>}"
    by (metis (mono_tags, opaque_lifting) abs_le_square_iff abs_of_nonneg assms(4) less_imp_le power2_abs)
  ultimately show ?thesis
    using qbs_prob_integral_Markov_inequality'[OF assms(1),of "\<lambda>x. \<bar>f x - qbs_prob_integral s f\<bar>^2" "b^2"] assms(4)
    by(simp add: qbs_prob_var_def assms(1))
qed

end
