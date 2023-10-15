(*  Title:   Monad_QuasiBorel.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)


section \<open>The S-Finite Measure Monad\<close>

theory Monad_QuasiBorel
  imports
 "Measure_QuasiBorel_Adjunction"
 "Kernels"

begin
subsection \<open> The S-Finite Measure Monad\<close>
subsubsection \<open> Space of S-Finite Measures\<close>
locale in_Mx =
  fixes X :: "'a quasi_borel"
    and \<alpha> :: "real \<Rightarrow> 'a"
  assumes in_Mx[simp]:"\<alpha> \<in> qbs_Mx X"
begin

lemma \<alpha>_measurable[measurable]: "\<alpha> \<in> borel \<rightarrow>\<^sub>M qbs_to_measure X"
  using in_Mx qbs_Mx_subset_of_measurable by blast

lemma \<alpha>_qbs_morphism[qbs]: "\<alpha> \<in> qbs_borel \<rightarrow>\<^sub>Q X"
  using in_Mx by(simp only: qbs_Mx_is_morphisms)

lemma X_not_empty: "qbs_space X \<noteq> {}"
  using in_Mx by(auto simp: qbs_empty_equiv simp del: in_Mx)

lemma inverse_UNIV[simp]: "\<alpha> -` (qbs_space X) = UNIV"
  by fastforce

end

locale qbs_s_finite = in_Mx X \<alpha> + s_finite_measure \<mu> 
  for X :: "'a quasi_borel" and \<alpha> and \<mu> :: "real measure" +
  assumes mu_sets[measurable_cong]: "sets \<mu> = sets borel"
begin

lemma mu_not_empty: "space \<mu> \<noteq> {}"
  by(simp add: sets_eq_imp_space_eq[OF mu_sets])

end

lemma qbs_s_finite_All:
  assumes "\<alpha> \<in> qbs_Mx X" "s_finite_kernel M borel k" "x \<in> space M"
  shows "qbs_s_finite X \<alpha> (k x)"
proof -
  interpret s_finite_kernel M borel k by fact
  show ?thesis
    using assms(1,3) image_s_finite_measure[OF assms(3)] by(auto simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def kernel_sets)
qed

locale qbs_prob = in_Mx X \<alpha> + real_distribution \<mu>
  for X :: "'a quasi_borel" and \<alpha> \<mu>
begin

lemma qbs_s_finite: "qbs_s_finite X \<alpha> \<mu>"
  by(auto simp: qbs_s_finite_def qbs_s_finite_axioms_def in_Mx_def s_finite_measure_prob)

sublocale qbs_s_finite by(rule qbs_s_finite)

end

lemma(in qbs_s_finite) qbs_probI: "prob_space \<mu> \<Longrightarrow> qbs_prob X \<alpha> \<mu>"
  by(auto simp: qbs_prob_def in_Mx_def real_distribution_def real_distribution_axioms_def mu_sets)

locale pair_qbs_s_finites = pq1: qbs_s_finite X \<alpha> \<mu> + pq2: qbs_s_finite Y \<beta> \<nu>
  for X :: "'a quasi_borel" and \<alpha> \<mu> and Y :: "'b quasi_borel" and \<beta> \<nu>
begin

lemma ab_measurable[measurable]: "map_prod \<alpha> \<beta> \<in> borel \<Otimes>\<^sub>M borel \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
proof -
  have "map_prod \<alpha> \<beta> \<in> qbs_to_measure (measure_to_qbs (borel \<Otimes>\<^sub>M borel)) \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
    by(auto intro!: set_mp[OF l_preserves_morphisms] simp: r_preserves_product)
  moreover have "sets (qbs_to_measure (measure_to_qbs (borel \<Otimes>\<^sub>M borel))) = sets ((borel \<Otimes>\<^sub>M borel) :: (real \<times> real) measure)"
    by(auto intro!: standard_borel.lr_sets_ident pair_standard_borel_ne standard_borel_ne.standard_borel)
  ultimately show ?thesis by simp
qed

end

locale pair_qbs_probs = pq1: qbs_prob X \<alpha> \<mu> + pq2: qbs_prob Y \<beta> \<nu>
  for X :: "'a quasi_borel" and \<alpha> \<mu> and Y :: "'b quasi_borel" and \<beta> \<nu>
begin
sublocale pair_qbs_s_finites
  by standard
end

locale pair_qbs_s_finite = pq1: qbs_s_finite X \<alpha> \<mu> + pq2: qbs_s_finite X \<beta> \<nu>
  for X :: "'a quasi_borel" and \<alpha> \<mu> and \<beta> \<nu>
begin
sublocale pair_qbs_s_finites X \<alpha> \<mu> X \<beta> \<nu>
  by standard
end

locale pair_qbs_prob = pq1: qbs_prob X \<alpha> \<mu> + pq2: qbs_prob X \<beta> \<nu>
  for X :: "'a quasi_borel" and \<alpha> \<mu> and \<beta> \<nu>
begin

sublocale pair_qbs_s_finite X \<alpha> \<mu> \<beta> \<nu>
  by standard

sublocale pair_qbs_probs X \<alpha> \<mu> X \<beta> \<mu>
  by standard

end

type_synonym 'a qbs_s_finite_t = "'a quasi_borel * (real \<Rightarrow> 'a) * real measure"
definition qbs_s_finite_eq :: "['a qbs_s_finite_t, 'a qbs_s_finite_t] \<Rightarrow> bool" where
  "qbs_s_finite_eq p1 p2 \<equiv>
   (let (X, \<alpha>, \<mu>) = p1;
        (Y, \<beta>, \<nu>) = p2 in
    qbs_s_finite X \<alpha> \<mu> \<and> qbs_s_finite Y \<beta> \<nu> \<and> X = Y \<and>
      distr \<mu> (qbs_to_measure X) \<alpha> = distr \<nu> (qbs_to_measure Y) \<beta>)"

definition qbs_s_finite_eq' :: "['a qbs_s_finite_t, 'a qbs_s_finite_t] \<Rightarrow> bool" where
  "qbs_s_finite_eq' p1 p2 \<equiv>
   (let (X, \<alpha>, \<mu>) = p1;
        (Y, \<beta>, \<nu>) = p2 in
    qbs_s_finite X \<alpha> \<mu> \<and> qbs_s_finite Y \<beta> \<nu> \<and> X = Y \<and>
      (\<forall>f\<in>X \<rightarrow>\<^sub>Q (qbs_borel :: ennreal quasi_borel). (\<integral>\<^sup>+x. f (\<alpha> x) \<partial>\<mu>) = (\<integral>\<^sup>+x. f (\<beta> x) \<partial>\<nu>)))"

lemma(in qbs_s_finite)
  shows qbs_s_finite_eq_refl[simp]: "qbs_s_finite_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
    and qbs_s_finite_eq'_refl[simp]: "qbs_s_finite_eq' (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
  by(simp_all add: qbs_s_finite_eq_def qbs_s_finite_eq'_def qbs_s_finite_axioms)

lemma(in pair_qbs_s_finite) 
  shows qbs_s_finite_eq_intro: "distr \<mu> (qbs_to_measure X) \<alpha> = distr \<nu> (qbs_to_measure X) \<beta> \<Longrightarrow> qbs_s_finite_eq (X,\<alpha>,\<mu>) (X,\<beta>,\<nu>)"
    and qbs_s_finite_eq'_intro: "(\<And>f. f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> (\<integral>\<^sup>+x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>\<^sup>+x. f (\<beta> x) \<partial> \<nu>)) \<Longrightarrow> qbs_s_finite_eq' (X,\<alpha>,\<mu>) (X,\<beta>,\<nu>)"
  by(simp_all add: qbs_s_finite_eq_def qbs_s_finite_eq'_def pq1.qbs_s_finite_axioms pq2.qbs_s_finite_axioms)

lemma qbs_s_finite_eq_dest:
  assumes "qbs_s_finite_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  shows "qbs_s_finite X \<alpha> \<mu>" "qbs_s_finite Y \<beta> \<nu>" "Y = X" "distr \<mu> (qbs_to_measure X) \<alpha> = distr \<nu> (qbs_to_measure X) \<beta>" 
  using assms by(auto simp: qbs_s_finite_eq_def)

lemma qbs_s_finite_eq'_dest:
  assumes "qbs_s_finite_eq' (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  shows "qbs_s_finite X \<alpha> \<mu>" "qbs_s_finite Y \<beta> \<nu>" "Y = X" "\<And>f. f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> (\<integral>\<^sup>+x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>\<^sup>+x. f (\<beta> x) \<partial> \<nu>)"
  using assms by(auto simp: qbs_s_finite_eq'_def)

lemma(in qbs_prob) qbs_s_finite_eq_qbs_prob_cong:
  assumes "qbs_s_finite_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
  shows "qbs_prob Y \<beta> \<nu>"
proof -
  interpret qs: pair_qbs_s_finites X \<alpha> \<mu> Y \<beta> \<nu>
    using assms(1) by(auto simp: qbs_s_finite_eq_def pair_qbs_s_finites_def)
  show ?thesis
    by(auto intro!: qs.pq2.qbs_probI prob_space_distrD[of \<beta> _ "qbs_to_measure Y"]) (auto simp: qbs_s_finite_eq_dest(3)[OF assms] qbs_s_finite_eq_dest(4)[OF assms,symmetric] intro!: prob_space_distr)
qed

lemma 
  shows qbs_s_finite_eq_symp: "symp qbs_s_finite_eq"
    and qbs_s_finite_eq_transp: "transp qbs_s_finite_eq"
  by(simp_all add: qbs_s_finite_eq_def transp_def symp_def)

quotient_type 'a qbs_measure = "'a qbs_s_finite_t" / partial: qbs_s_finite_eq
  morphisms rep_qbs_measure qbs_measure
proof(rule part_equivpI)
  let ?U = "UNIV :: 'a set"
  let ?Uf = "UNIV :: (real \<Rightarrow> 'a) set"
  let ?f = "(\<lambda>_. undefined) :: real \<Rightarrow> 'a"
  have "qbs_s_finite (Abs_quasi_borel (?U, ?Uf)) ?f (return borel 0)"
    unfolding qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def
  proof safe
    have "Rep_quasi_borel (Abs_quasi_borel (?U,?Uf)) = (?U, ?Uf)"
      using Abs_quasi_borel_inverse by (auto simp add: qbs_closed1_def qbs_closed2_def qbs_closed3_def is_quasi_borel_def)
    thus "(\<lambda>_. undefined) \<in> qbs_Mx (Abs_quasi_borel (?U, ?Uf))"
      by(simp add: qbs_Mx_def)
  next
    show "s_finite_measure (return borel 0)"
      by(auto intro!: sigma_finite_measure.s_finite_measure prob_space_imp_sigma_finite prob_space_return)
  qed simp_all
  thus "\<exists>x :: 'a qbs_s_finite_t. qbs_s_finite_eq x x"
    by(auto simp: qbs_s_finite_eq_def intro!: exI[where x="(Abs_quasi_borel (?U,?Uf), ?f, return borel 0)"])
qed(simp_all add: qbs_s_finite_eq_symp qbs_s_finite_eq_transp)

interpretation qbs_measure : quot_type "qbs_s_finite_eq" "Abs_qbs_measure" "Rep_qbs_measure"
  using Abs_qbs_measure_inverse Rep_qbs_measure
  by(simp add: quot_type_def equivp_implies_part_equivp qbs_measure_equivp Rep_qbs_measure_inverse Rep_qbs_measure_inject) blast

syntax
 "_qbs_measure" :: "'a quasi_borel \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> real measure \<Rightarrow> 'a qbs_measure" ("\<lbrakk>_,/ _,/ _\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n")
translations
 "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" \<rightleftharpoons> "CONST qbs_measure (X, \<alpha>, \<mu>)"

lemma rep_qbs_s_finite_measure': "\<exists>X \<alpha> \<mu>. p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<and> qbs_s_finite X \<alpha> \<mu>"
  by(rule qbs_measure.abs_induct,auto simp add: qbs_s_finite_eq_def)

lemma rep_qbs_s_finite_measure:
  obtains X \<alpha> \<mu> where "p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
  using that rep_qbs_s_finite_measure' by blast

definition qbs_null_measure :: "'a quasi_borel \<Rightarrow> 'a qbs_measure" where
"qbs_null_measure X \<equiv> \<lbrakk>X, SOME a. a \<in> qbs_Mx X, null_measure borel\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"

lemma qbs_null_measure_s_finite: "qbs_space X \<noteq> {} \<Longrightarrow> qbs_s_finite X (SOME a. a \<in> qbs_Mx X) (null_measure borel)"
  by(auto simp: qbs_empty_equiv qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def some_in_eq intro!: finite_measure.s_finite_measure_finite_measure finite_measureI)

lemma(in qbs_s_finite) in_Rep_qbs_measure':
  assumes "qbs_s_finite_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
  shows "(X',\<alpha>',\<mu>') \<in> Rep_qbs_measure \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  by (metis assms mem_Collect_eq qbs_s_finite_eq_refl qbs_measure_def qbs_measure.abs_def qbs_measure.abs_inverse)

lemmas(in qbs_s_finite) in_Rep_qbs_measure = in_Rep_qbs_measure'[OF qbs_s_finite_eq_refl]

lemma(in qbs_s_finite) if_in_Rep_qbs_measure:
  assumes "(X',\<alpha>',\<mu>') \<in> Rep_qbs_measure \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  shows "X' = X"
        "qbs_s_finite X' \<alpha>' \<mu>'"
        "qbs_s_finite_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
proof -
  show h:"X' = X"
    using assms qbs_measure.Rep_qbs_measure[of "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"]
    by auto (metis mem_Collect_eq qbs_s_finite_eq_dest(3) qbs_s_finite_eq_refl qbs_measure_def qbs_measure.abs_def qbs_measure.abs_inverse)
next
  show "qbs_s_finite X' \<alpha>' \<mu>'"
    using assms qbs_measure.Rep_qbs_measure[of "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"]
    by (auto simp: qbs_s_finite_eq_dest(2))
next
  show "qbs_s_finite_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
    using assms qbs_measure.Rep_qbs_measure[of "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"]
    by auto (metis mem_Collect_eq qbs_s_finite_eq_dest(3) qbs_s_finite_eq_refl qbs_measure_def qbs_measure.abs_def qbs_measure.abs_inverse)
qed

lemma qbs_s_finite_eq_1_imp_2:
  assumes "qbs_s_finite_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)" "f \<in> X \<rightarrow>\<^sub>Q (qbs_borel :: (_ :: {banach}) quasi_borel)"
  shows "(\<integral>x. f (\<alpha> x) \<partial>\<mu>) = (\<integral>x. f (\<beta> x) \<partial>\<nu>)" (is "?lhs = ?rhs")
proof -
 interpret pq : pair_qbs_s_finite X \<alpha> \<mu> \<beta> \<nu>
   using assms by(auto intro!: pair_qbs_s_finite.intro simp: qbs_s_finite_eq_def)
  have [measurable]: "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M borel"
    using assms  by(simp add: lr_adjunction_correspondence)
  have "?lhs = (\<integral>x. f x \<partial>(distr \<mu> (qbs_to_measure X) \<alpha>))"
    by(simp add: integral_distr)
  also have "... = (\<integral>x. f x \<partial>(distr \<nu> (qbs_to_measure X) \<beta>))"
    by(simp add: qbs_s_finite_eq_dest(4)[OF assms(1)])
  also have "... = ?rhs"
    by(simp add: integral_distr)
  finally show ?thesis .
qed

lemma qbs_s_finite_eq_equiv: "qbs_s_finite_eq = qbs_s_finite_eq'"
proof(rule ext[OF ext])
  show "\<And>a b :: 'a qbs_s_finite_t. qbs_s_finite_eq a b = qbs_s_finite_eq' a b"
  proof safe
    fix X Y :: "'a quasi_borel" and \<alpha> \<beta> \<mu> \<nu>
    {
      assume h:"qbs_s_finite_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
      then interpret pq : pair_qbs_s_finite X \<alpha> \<mu> \<beta> \<nu>
        by(auto intro!: pair_qbs_s_finite.intro simp: qbs_s_finite_eq_def)
      show "qbs_s_finite_eq' (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
        unfolding qbs_s_finite_eq_dest(3)[OF h]
      proof(rule pq.qbs_s_finite_eq'_intro)
        fix f :: "'a \<Rightarrow> ennreal"
        assume f:"f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
        show "(\<integral>\<^sup>+ x. f (\<alpha> x) \<partial>\<mu>) = (\<integral>\<^sup>+ x. f (\<beta> x) \<partial>\<nu>)" (is "?lhs = ?rhs")
        proof -
          have "?lhs = (\<integral>\<^sup>+ x. f x \<partial>(distr \<mu> (qbs_to_measure X) \<alpha>))"
            by(rule nn_integral_distr[symmetric]) (use f lr_adjunction_correspondence in auto)
          also have "... = (\<integral>\<^sup>+ x. f x \<partial>(distr \<nu> (qbs_to_measure X) \<beta>))"
            by(simp add: qbs_s_finite_eq_dest(4)[OF h])
          also have "... = ?rhs"
            by(rule nn_integral_distr) (use f lr_adjunction_correspondence in auto)
          finally show ?thesis .
        qed
      qed
    }
    {
      assume h:"qbs_s_finite_eq' (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
      then interpret pq : pair_qbs_s_finite X \<alpha> \<mu> \<beta> \<nu>
        by(auto intro!: pair_qbs_s_finite.intro simp: qbs_s_finite_eq'_def)
      show "qbs_s_finite_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)"
        unfolding qbs_s_finite_eq'_dest(3)[OF h]
      proof(rule pq.qbs_s_finite_eq_intro[OF measure_eqI])
        fix U
        assume hu[measurable]:"U \<in> sets (distr \<mu> (qbs_to_measure X) \<alpha>)"
        show "emeasure (distr \<mu> (qbs_to_measure X) \<alpha>) U = emeasure (distr \<nu> (qbs_to_measure X) \<beta>) U"
             (is "?lhs = ?rhs")
        proof -
          have "?lhs = (\<integral>\<^sup>+ x. indicator U x \<partial> (distr \<mu> (qbs_to_measure X) \<alpha>))"
            using hu by simp
          also have "... = (\<integral>\<^sup>+ x. indicator U (\<alpha> x) \<partial>\<mu>)"
            by(rule nn_integral_distr) (use hu in auto)
          also have "... = (\<integral>\<^sup>+ x. indicator U (\<beta> x) \<partial>\<nu>)"
            by(auto intro!: qbs_s_finite_eq'_dest(4)[OF h] simp: lr_adjunction_correspondence)
          also have "... = (\<integral>\<^sup>+ x. indicator U x \<partial> (distr \<nu> (qbs_to_measure X) \<beta>))"
            by(rule nn_integral_distr[symmetric]) (use hu in auto)
          also have "... = ?rhs"
            using hu by simp
          finally show ?thesis .
        qed
      qed simp
    }
  qed
qed

lemma qbs_s_finite_measure_eq: "qbs_s_finite_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>) \<Longrightarrow> \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  using Quotient3_rel[OF Quotient3_qbs_measure] by blast

lemma(in pair_qbs_s_finite) qbs_s_finite_measure_eq:
  "distr \<mu> (qbs_to_measure X) \<alpha> = distr \<nu> (qbs_to_measure X) \<beta> \<Longrightarrow> \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>X, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  by(auto intro!: qbs_s_finite_measure_eq qbs_s_finite_eq_intro)

lemma(in pair_qbs_s_finite) qbs_s_finite_measure_eq':
  "(\<And>f. f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> (\<integral>\<^sup>+x. f (\<alpha> x) \<partial> \<mu>) = (\<integral>\<^sup>+x. f (\<beta> x) \<partial> \<nu>)) \<Longrightarrow> \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>X, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  using qbs_s_finite_eq'_intro[simplified qbs_s_finite_eq_equiv[symmetric]] by(auto intro!: qbs_s_finite_measure_eq simp: qbs_s_finite_eq_def)

lemma(in pair_qbs_s_finite) qbs_s_finite_measure_eq_inverse:
  assumes "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>X, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  shows "qbs_s_finite_eq (X,\<alpha>,\<mu>) (X,\<beta>,\<nu>)" "qbs_s_finite_eq' (X,\<alpha>,\<mu>) (X,\<beta>,\<nu>)"
  using Quotient3_rel[OF Quotient3_qbs_measure,of "(X,\<alpha>,\<mu>)" "(X,\<beta>,\<nu>)",simplified]
  by(simp_all add: assms qbs_s_finite_eq_equiv)

lift_definition qbs_space_of :: "'a qbs_measure \<Rightarrow> 'a quasi_borel"
is fst by(auto simp: qbs_s_finite_eq_def)

lemma(in qbs_s_finite) qbs_space_of[simp]:
 "qbs_space_of \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = X" by(simp add: qbs_space_of.abs_eq)

lemma rep_qbs_space_of:
  assumes "qbs_space_of s = X"
  shows "\<exists>\<alpha> \<mu>. s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<and> qbs_s_finite X \<alpha> \<mu>"
proof -
  obtain X' \<alpha> \<mu> where hs:
   "s =  \<lbrakk>X', \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X' \<alpha> \<mu>"
    using rep_qbs_s_finite_measure'[of s] by auto
  then interpret qs:qbs_s_finite X' \<alpha> \<mu>
    by simp
  show ?thesis
    using assms hs(2) by(auto simp add: hs(1))
qed

corollary qbs_s_space_of_not_empty: "qbs_space (qbs_space_of X) \<noteq> {}"
  by transfer (auto simp: qbs_s_finite_eq_def qbs_s_finite_def in_Mx_def qbs_empty_equiv)


subsubsection \<open> The S-Finite Measure Monad\<close>
definition monadM_qbs :: "'a quasi_borel \<Rightarrow> 'a qbs_measure quasi_borel" where
"monadM_qbs X \<equiv> Abs_quasi_borel ({s. qbs_space_of s = X}, {\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k})"

lemma
  shows monadM_qbs_space: "qbs_space (monadM_qbs X) = {s. qbs_space_of s = X}"
    and monadM_qbs_Mx: "qbs_Mx (monadM_qbs X) = {\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k}"
proof -
  have "{\<lambda>r::real. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k} \<subseteq> UNIV \<rightarrow> {s. qbs_space_of s = X}"
  proof safe
    fix x \<alpha> and k :: "real \<Rightarrow> real measure"
    assume h:"\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k"
    interpret k:s_finite_kernel borel borel k by fact
    interpret qbs_s_finite X \<alpha> "k x"
      using k.image_s_finite_measure h(1) by(auto simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def k.kernel_sets) 
    show "qbs_space_of \<lbrakk>X, \<alpha>, k x\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = X"
      by simp
  qed
  moreover have "qbs_closed1 {\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k}"
  proof(safe intro!: qbs_closed1I)
    fix \<alpha> and f :: "real \<Rightarrow> real" and k :: "real\<Rightarrow> real measure"
    assume h:"f \<in> borel_measurable borel" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k"
    then show "\<exists>\<alpha>' ka. (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<circ> f = (\<lambda>r. \<lbrakk>X, \<alpha>', ka r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<alpha>' \<in> qbs_Mx X \<and> s_finite_kernel borel borel ka"
      by(auto intro!: exI[where x=\<alpha>] exI[where x="\<lambda>x. k (f x)"] simp: s_finite_kernel.comp_measurable[OF h(3,1)])
  qed
  moreover have "qbs_closed2 {s. qbs_space_of s = X} {\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k}"
  proof(safe intro!: qbs_closed2I)
    fix s
    assume h:"X = qbs_space_of s"
    from rep_qbs_space_of[OF this[symmetric]] obtain \<alpha> \<mu> where s:"s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
      by auto
    then interpret qbs_s_finite X \<alpha> \<mu> by simp
    show "\<exists>\<alpha> k. (\<lambda>r. s) = (\<lambda>r. \<lbrakk>qbs_space_of s, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<alpha> \<in> qbs_Mx (qbs_space_of s) \<and> s_finite_kernel borel borel k"
      by(auto intro!: exI[where x=\<alpha>] exI[where x="\<lambda>r. \<mu>"] s_finite_kernel_const simp: s(1) s_finite_kernel_cong_sets[OF _ mu_sets[symmetric]] sets_eq_imp_space_eq[OF mu_sets])
  qed
  moreover have "qbs_closed3 {\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k}"
  proof(safe intro!: qbs_closed3I)
    fix P :: "real \<Rightarrow> nat" and Fi :: "nat \<Rightarrow> _"
    assume P[measurable]: "P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
       and "\<forall>i. Fi i \<in> {\<lambda>r::real. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k}"
    then obtain \<alpha>i ki where Fi: "\<And>i. Fi i = (\<lambda>r. \<lbrakk>X, \<alpha>i i, ki i r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<And>i. \<alpha>i i \<in> qbs_Mx X" "\<And>i. s_finite_kernel borel borel (ki i)"
      by auto metis
    interpret nat_real: standard_borel_ne "count_space (UNIV :: nat set) \<Otimes>\<^sub>M (borel :: real measure)"
      by(auto intro!: pair_standard_borel_ne)
    note [simp] = nat_real.from_real_to_real[simplified space_pair_measure, simplified]
    define \<alpha> where "\<alpha> \<equiv> (\<lambda>r. case_prod \<alpha>i (nat_real.from_real r))"
    define k where "k \<equiv> (\<lambda>r. distr (distr (ki (P r) r) (count_space UNIV \<Otimes>\<^sub>M borel) (\<lambda>r'. (P r, r'))) borel nat_real.to_real)"
    have \<alpha>: "\<alpha> \<in> qbs_Mx X"
      unfolding \<alpha>_def qbs_Mx_is_morphisms
    proof(rule qbs_morphism_compose[where g=nat_real.from_real and Y="qbs_count_space UNIV \<Otimes>\<^sub>Q qbs_borel"])
      show "nat_real.from_real \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_count_space UNIV \<Otimes>\<^sub>Q qbs_borel"
        by(simp add: r_preserves_product[symmetric] standard_borel.standard_borel_r_full_faithful[of "borel :: real measure",simplified,symmetric] standard_borel_ne.standard_borel)
    next
      show "case_prod \<alpha>i \<in> qbs_count_space UNIV \<Otimes>\<^sub>Q qbs_borel \<rightarrow>\<^sub>Q X"
        using Fi(2) by(auto intro!: qbs_morphism_pair_count_space1 simp: qbs_Mx_is_morphisms)
    qed
    have sets_ki[measurable_cong]: "sets (ki i r) = sets borel" "sets (k r) = sets borel" for i r
      using Fi(3) by(auto simp: s_finite_kernel_def measure_kernel_def k_def)
    interpret k:s_finite_kernel borel borel k
    proof -
      have 1:"k = (\<lambda>(i,r). distr (ki i r) borel (\<lambda>r'. nat_real.to_real (i, r'))) \<circ> (\<lambda>r. (P r, r))"
        by standard (auto simp: k_def distr_distr comp_def)
      have "s_finite_kernel borel borel ..."
        unfolding comp_def
        by(rule s_finite_kernel.comp_measurable[where X="count_space UNIV \<Otimes>\<^sub>M borel"],rule s_finite_kernel_pair_countble1, auto intro!: s_finite_kernel.distr_s_finite_kernel[OF Fi(3)])
      thus "s_finite_kernel borel borel k" by(simp add: 1)
    qed
    have "(\<lambda>r. Fi (P r) r) = (\<lambda>r. \<lbrakk>X, \<alpha>, k r \<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
      unfolding Fi(1)
    proof
      fix r
      interpret pq:pair_qbs_s_finite X "\<alpha>i (P r)" "ki (P r) r" \<alpha> "k r"
        by(auto simp: pair_qbs_s_finite_def qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def k.image_s_finite_measure s_finite_kernel.image_s_finite_measure[OF Fi(3)] sets_ki \<alpha> Fi(2))
      show "\<lbrakk>X, \<alpha>i (P r), ki (P r) r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
        by(rule pq.qbs_s_finite_measure_eq, simp add: k_def distr_distr comp_def,simp add: \<alpha>_def)
    qed
    thus "\<exists>\<alpha> k. (\<lambda>r. Fi (P r) r) = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k"
      by(auto intro!: exI[where x=\<alpha>] exI[where x=k] simp: \<alpha> k.s_finite_kernel_axioms)
  qed
  ultimately have "Rep_quasi_borel (monadM_qbs X) = ({s. qbs_space_of s = X}, {\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k})"
    by(auto intro!: Abs_quasi_borel_inverse  simp: monadM_qbs_def is_quasi_borel_def)
  thus "qbs_space (monadM_qbs X) = {s. qbs_space_of s = X}" "qbs_Mx (monadM_qbs X) = {\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> s_finite_kernel borel borel k}"
    by(simp_all add: qbs_space_def qbs_Mx_def)
qed

lemma monadM_qbs_empty_iff: "qbs_space X = {} \<longleftrightarrow> qbs_space (monadM_qbs X) = {}"
  by(auto simp: monadM_qbs_space qbs_s_space_of_not_empty) (meson in_Mx.intro qbs_closed2_dest qbs_s_finite.qbs_space_of qbs_s_finite_def rep_qbs_s_finite_measure')

lemma(in qbs_s_finite) in_space_monadM[qbs]: "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<in> qbs_space (monadM_qbs X)"
  by(simp add: monadM_qbs_space)

lemma rep_qbs_space_monadM:
  assumes "s \<in> qbs_space (monadM_qbs X)"
  obtains \<alpha> \<mu> where "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
  using rep_qbs_space_of assms that by(auto simp: monadM_qbs_space)

lemma rep_qbs_space_monadM_sigma_finite:
  assumes "s \<in> qbs_space (monadM_qbs X)"
  obtains \<alpha> \<mu> where "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" "sigma_finite_measure \<mu>"
proof -
  obtain \<alpha> \<mu> where s:"s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
    by(metis rep_qbs_space_monadM assms)
  hence "standard_borel_ne \<mu>""s_finite_measure \<mu>"
    by(auto intro!: standard_borel_ne_sets[of borel \<mu>] simp: qbs_s_finite_def qbs_s_finite_axioms_def)
  from exists_push_forward[OF this] obtain \<mu>' f where f:
    "f \<in> (borel :: real measure) \<rightarrow>\<^sub>M \<mu>" "sets \<mu>' = sets borel" "sigma_finite_measure \<mu>'" "distr \<mu>' \<mu> f = \<mu>"
    by metis
  hence [measurable]: "f \<in> borel_measurable borel"
    using s(2) by(auto simp: qbs_s_finite_def qbs_s_finite_axioms_def cong: measurable_cong_sets)
  interpret pair_qbs_s_finite X \<alpha> \<mu> "\<alpha> \<circ> f" \<mu>'
  proof -
    have "qbs_s_finite X (\<alpha> \<circ> f) \<mu>'"
      using s(2) by(auto simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def[of \<mu>'] f(2,3) sigma_finite_measure.s_finite_measure)
    thus "pair_qbs_s_finite X \<alpha> \<mu> (\<alpha> \<circ> f) \<mu>'"
      by(auto simp: pair_qbs_s_finite_def s(2))
  qed
  have "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>X, \<alpha> \<circ> f, \<mu>'\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  proof -
    have [simp]:" distr \<mu> (qbs_to_measure X) \<alpha> = distr (distr \<mu>' \<mu> f) (qbs_to_measure X) \<alpha>"
      by(simp add: f(4))
    show ?thesis
      by(auto intro!: qbs_s_finite_measure_eq simp: distr_distr)
  qed
  with s(1) pq2.qbs_s_finite_axioms f(3) that
  show ?thesis by metis
qed

lemma qbs_space_of_in: "s \<in> qbs_space (monadM_qbs X) \<Longrightarrow> qbs_space_of s = X"
  by(simp add: monadM_qbs_space)

lemma in_qbs_space_of: "s \<in> qbs_space (monadM_qbs (qbs_space_of s))"
  by(simp add: monadM_qbs_space)

subsubsection \<open> $l$ \<close>
lift_definition qbs_l :: "'a qbs_measure \<Rightarrow> 'a measure"
is "\<lambda>p. distr (snd (snd p)) (qbs_to_measure (fst p)) (fst (snd p))"
  by(auto simp: qbs_s_finite_eq_def)

lemma(in qbs_s_finite) qbs_l: "qbs_l \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n  = distr \<mu> (qbs_to_measure X) \<alpha>"
  by(simp add: qbs_l.abs_eq)

interpretation qbs_l_s_finite: s_finite_measure "qbs_l (s :: 'a qbs_measure)"
proof(transfer)
  show "\<And>s:: 'a qbs_s_finite_t. qbs_s_finite_eq s s \<Longrightarrow> s_finite_measure (distr (snd (snd s)) (qbs_to_measure (fst s)) (fst (snd s)))"
  proof safe
    fix X :: "'a quasi_borel"
    fix \<alpha> \<mu>
    assume "qbs_s_finite_eq (X,\<alpha>,\<mu>) (X,\<alpha>,\<mu>)"
    then interpret qbs_s_finite X \<alpha> \<mu>
      by(simp add: qbs_s_finite_eq_def)
    show "s_finite_measure (distr (snd (snd (X,\<alpha>,\<mu>))) (qbs_to_measure (fst (X,\<alpha>,\<mu>))) (fst (snd (X,\<alpha>,\<mu>))))"
      by(auto intro!: s_finite_measure.s_finite_measure_distr simp: s_finite_measure_axioms)
  qed
qed

lemma space_qbs_l: "qbs_space (qbs_space_of s) = space (qbs_l s)"
  by(transfer, auto simp: space_L)

lemma space_qbs_l_ne: "space (qbs_l s) \<noteq> {}"
  by transfer (auto simp: qbs_s_finite_eq_def qbs_s_finite_def in_Mx_def space_L qbs_empty_equiv)

lemma qbs_l_sets: "sets (qbs_to_measure (qbs_space_of s)) = sets (qbs_l s)"
  by(transfer,simp)

lemma qbs_null_measure_in_Mx: "qbs_space X \<noteq> {} \<Longrightarrow> qbs_null_measure X \<in> qbs_space (monadM_qbs X)"
  by(simp add: qbs_s_finite.in_space_monadM[OF qbs_null_measure_s_finite] qbs_null_measure_def)

lemma qbs_null_measure_null_measure:"qbs_space X \<noteq> {} \<Longrightarrow> qbs_l (qbs_null_measure X) = null_measure (qbs_to_measure X)"
  by(auto simp: qbs_null_measure_def qbs_s_finite.qbs_l[OF qbs_null_measure_s_finite] null_measure_distr)

lemma space_qbs_l_in:
  assumes "s \<in> qbs_space (monadM_qbs X)"
  shows "space (qbs_l s) = qbs_space X"
  by (metis assms qbs_s_finite.qbs_space_of rep_qbs_space_monadM space_qbs_l)

lemma sets_qbs_l:
  assumes "s \<in> qbs_space (monadM_qbs X)"
  shows "sets (qbs_l s) = sets (qbs_to_measure X)"
  using assms qbs_l_sets qbs_space_of_in by blast

lemma measurable_qbs_l:
  assumes "s \<in> qbs_space (monadM_qbs X)"
  shows "qbs_l s \<rightarrow>\<^sub>M M = X \<rightarrow>\<^sub>Q measure_to_qbs M"
  by(auto simp: measurable_cong_sets[OF qbs_l_sets[of s,simplified qbs_space_of_in[OF assms(1)],symmetric] refl] lr_adjunction_correspondence)

lemma measurable_qbs_l':
  assumes "s \<in> qbs_space (monadM_qbs X)"
  shows "qbs_l s \<rightarrow>\<^sub>M M = qbs_to_measure X \<rightarrow>\<^sub>M M"
  by(simp add: measurable_qbs_l[OF assms] lr_adjunction_correspondence)

lemma rep_qbs_Mx_monadM:
  assumes "\<gamma> \<in> qbs_Mx (monadM_qbs X)"
  obtains \<alpha> k where "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<alpha> (k r)"
proof -
  have "\<And>\<alpha> r k. \<alpha> \<in> qbs_Mx X \<Longrightarrow> s_finite_kernel borel borel k \<Longrightarrow> qbs_s_finite X \<alpha> (k r)"
    by(auto simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def s_finite_kernel.image_s_finite_measure) (auto simp: s_finite_kernel_def measure_kernel_def)
  thus ?thesis
    using that assms by(fastforce simp: monadM_qbs_Mx)
qed

lemma qbs_l_measurable[measurable]:"qbs_l \<in> qbs_to_measure (monadM_qbs X) \<rightarrow>\<^sub>M s_finite_measure_algebra (qbs_to_measure X)"
proof(rule qbs_morphism_dest[OF qbs_morphismI])
  fix \<gamma>
  assume "\<gamma> \<in> qbs_Mx (monadM_qbs X)"
  from rep_qbs_Mx_monadM[OF this] obtain \<alpha> k where h:
  "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<alpha> (k r)"
    by metis
  show "qbs_l \<circ> \<gamma> \<in> qbs_Mx (measure_to_qbs (s_finite_measure_algebra (qbs_to_measure X)))"
    by(auto simp add: qbs_Mx_R comp_def h(1) qbs_s_finite.qbs_l[OF h(4)] h(2,3) intro!: s_finite_kernel.kernel_measurable_s_finite s_finite_kernel.distr_s_finite_kernel[where Y=borel])
qed

lemma qbs_l_measure_kernel: "measure_kernel (qbs_to_measure (monadM_qbs X)) (qbs_to_measure X) qbs_l"
proof(cases "qbs_space X = {}")
  case True
  with monadM_qbs_empty_iff[of X,simplified this] show ?thesis
    by(auto intro!: measure_kernel_empty_trivial simp: space_L) 
next
  case 1:False
  show ?thesis
  proof
    show "\<And>x. x \<in> space (qbs_to_measure (monadM_qbs X)) \<Longrightarrow> sets (qbs_l x) = sets (qbs_to_measure X)"
      using qbs_l_sets by(auto simp: space_L monadM_qbs_space)
  next
    show "space (qbs_to_measure X) \<noteq> {}"
      by(simp add: space_L 1)
  qed (rule measurable_emeasure_kernel_s_finite_measure_algebra[OF qbs_l_measurable])
qed

lemma qbs_l_inj: "inj_on qbs_l (qbs_space (monadM_qbs X))"
  by standard (auto simp: monadM_qbs_space, transfer,auto simp: qbs_s_finite_eq_def)

lemma qbs_l_morphism:
  assumes [measurable]:"A \<in> sets (qbs_to_measure X)"
  shows "(\<lambda>s. qbs_l s A) \<in> monadM_qbs X \<rightarrow>\<^sub>Q qbs_borel"
proof(rule qbs_morphismI)
  fix \<gamma>
  assume h:"\<gamma> \<in> qbs_Mx (monadM_qbs X)" 
  hence [qbs]: "\<gamma> \<in> qbs_borel \<rightarrow>\<^sub>Q monadM_qbs X"
    by(simp_all add: qbs_Mx_is_morphisms)
  from rep_qbs_Mx_monadM[OF h(1)] obtain \<alpha> k where hk:
   "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<alpha> (k r)"
    by metis
  then interpret a: in_Mx X \<alpha> by(simp add: in_Mx_def)
  have k[measurable_cong]:"sets (k r) = sets borel" for r
    using hk(3) by(auto simp: s_finite_kernel_def measure_kernel_def)
  show "(\<lambda>s. emeasure (qbs_l s) A) \<circ> \<gamma> \<in> qbs_Mx qbs_borel"
    by(auto simp: hk(1) qbs_s_finite.qbs_l[OF hk(4)] comp_def qbs_Mx_qbs_borel emeasure_distr sets_eq_imp_space_eq[OF k] intro!: s_finite_kernel.emeasure_measurable'[OF hk(3)] measurable_sets_borel[OF _ assms])
qed

lemma qbs_l_finite_pred: "qbs_pred (monadM_qbs X) (\<lambda>s. finite_measure (qbs_l s))"
proof -
  have "qbs_space X \<in> sets (qbs_to_measure X)"
    by (metis sets.top space_L)
  note qbs_l_morphism[OF this,qbs]
  have [simp]:"finite_measure (qbs_l s) \<longleftrightarrow> qbs_l s X \<noteq> \<infinity>" if "s \<in> monadM_qbs X" for s
    by(auto intro!: finite_measureI dest: finite_measure.emeasure_finite simp: space_qbs_l_in[OF that])
  show ?thesis
    by(simp cong: qbs_morphism_cong)
qed

lemma qbs_l_subprob_pred: "qbs_pred (monadM_qbs X) (\<lambda>s. subprob_space (qbs_l s))"
proof -
  have "qbs_space X \<in> sets (qbs_to_measure X)"
    by (metis sets.top space_L)
  note qbs_l_morphism[OF this,qbs]
  have [simp]:"subprob_space (qbs_l s) \<longleftrightarrow> qbs_l s X \<le> 1" if "s \<in> monadM_qbs X" for s  
    by(auto intro!: subprob_spaceI dest: subprob_space.subprob_emeasure_le_1 simp: space_qbs_l_ne) (simp add: space_qbs_l_in[OF that])
  show ?thesis
    by(simp cong: qbs_morphism_cong)
qed

lemma qbs_l_prob_pred: "qbs_pred (monadM_qbs X) (\<lambda>s. prob_space (qbs_l s))"
proof -
  have "qbs_space X \<in> sets (qbs_to_measure X)"
    by (metis sets.top space_L)
  note qbs_l_morphism[OF this,qbs]
  have [simp]:"prob_space (qbs_l s) \<longleftrightarrow> qbs_l s X = 1" if "s \<in> monadM_qbs X" for s  
    by(auto intro!: prob_spaceI simp: space_qbs_l_ne) (auto simp add: space_qbs_l_in[OF that] dest: prob_space.emeasure_space_1)
  show ?thesis
    by(simp cong: qbs_morphism_cong)
qed

subsubsection \<open> Return \<close>
definition return_qbs :: "'a quasi_borel \<Rightarrow> 'a \<Rightarrow> 'a qbs_measure" where
"return_qbs X x \<equiv> \<lbrakk>X, \<lambda>r. x, SOME \<mu>. real_distribution \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"

lemma(in real_distribution)
  assumes "x \<in> qbs_space X"
  shows return_qbs:"return_qbs X x = \<lbrakk>X, \<lambda>r. x, M\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    and return_qbs_prob:"qbs_prob X (\<lambda>r. x) M"
    and return_qbs_s_finite:"qbs_s_finite X (\<lambda>r. x) M"
proof -
  interpret qs1: qbs_prob X "\<lambda>r. x" M
    by(auto simp: qbs_prob_def in_Mx_def real_distribution_axioms intro!: qbs_closed2_dest assms)
  show "return_qbs X x = \<lbrakk>X, \<lambda>r. x, M\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    unfolding return_qbs_def
  proof(rule someI2)
    show "real_distribution (return borel 0)" by (auto simp: real_distribution_def real_distribution_axioms_def,rule prob_space_return) simp
  next
    fix N
    assume "real_distribution N"
    then interpret qs2: qbs_s_finite X "\<lambda>r. x" N
      by(auto simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def real_distribution_def  real_distribution_axioms_def intro!: qbs_closed2_dest assms sigma_finite_measure.s_finite_measure prob_space_imp_sigma_finite)
    interpret pair_qbs_s_finite X "\<lambda>r. x" N "\<lambda>r. x" M
      by standard
    show "\<lbrakk>X, \<lambda>r. x, N\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>X, \<lambda>r. x, M\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
      by(auto intro!: qbs_s_finite_measure_eq measure_eqI simp: emeasure_distr) (metis \<open>real_distribution N\<close> emeasure_space_1 prob_space.emeasure_space_1 qs2.mu_sets real_distribution.axioms(1) sets_eq_imp_space_eq space_borel space_eq_univ)
  qed
  show "qbs_prob X (\<lambda>r. x) M" "qbs_s_finite X (\<lambda>r. x) M"
    by(simp_all add: qs1.qbs_prob_axioms qs1.qbs_s_finite_axioms)
qed

lemma return_qbs_comp:
  assumes "\<alpha> \<in> qbs_Mx X"
  shows "(return_qbs X \<circ> \<alpha>) = (\<lambda>r. \<lbrakk>X, \<alpha>, return borel r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
proof
  fix r
  interpret pqp: pair_qbs_prob X "\<lambda>k. \<alpha> r" "return borel 0" \<alpha> "return borel r"
    by(simp add: assms qbs_Mx_to_X[OF assms] pair_qbs_prob_def qbs_prob_def in_Mx_def real_distribution_def real_distribution_axioms_def prob_space_return)
  show "(return_qbs X \<circ> \<alpha>) r = \<lbrakk>X, \<alpha>, return borel r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(auto simp: pqp.pq1.return_qbs[OF qbs_Mx_to_X[OF assms]] distr_return intro!: pqp.qbs_s_finite_measure_eq)
qed

corollary return_qbs_morphism[qbs]: "return_qbs X \<in> X \<rightarrow>\<^sub>Q monadM_qbs X"
proof(rule qbs_morphismI)
  interpret rr : real_distribution "return borel 0"
    by(simp add: real_distribution_def real_distribution_axioms_def prob_space_return)
  fix \<alpha>
  assume h:"\<alpha> \<in> qbs_Mx X"
  then have 1:"return_qbs X \<circ> \<alpha> = (\<lambda>r. \<lbrakk>X, \<alpha>, return borel r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    by(rule return_qbs_comp)
  show "return_qbs X \<circ> \<alpha> \<in> qbs_Mx (monadM_qbs X)"
    by(auto simp: 1 monadM_qbs_Mx h prob_kernel_def' intro!: exI[where x=\<alpha>] exI[where x="return borel"] prob_kernel.s_finite_kernel_prob_kernel)
qed

subsubsection \<open>Bind\<close>
definition bind_qbs :: "['a qbs_measure, 'a \<Rightarrow> 'b qbs_measure] \<Rightarrow> 'b qbs_measure" where
"bind_qbs s f \<equiv> (let (X, \<alpha>, \<mu>) = rep_qbs_measure s;
                      Y = qbs_space_of (f (\<alpha> undefined));
                      (\<beta>, k) = (SOME (\<beta>, k). f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<beta> \<in> qbs_Mx Y \<and> s_finite_kernel borel borel k) in
                      \<lbrakk>Y, \<beta>, \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"

adhoc_overloading Monad_Syntax.bind bind_qbs

lemma(in qbs_s_finite)
  assumes "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
          "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
          "\<beta> \<in> qbs_Mx Y"
          "s_finite_kernel borel borel k"
      and "(f \<circ> \<alpha>) = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    shows bind_qbs_s_finite:"qbs_s_finite Y \<beta> (\<mu> \<bind>\<^sub>k k)"
      and bind_qbs: "s \<bind> f = \<lbrakk>Y, \<beta>, \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
proof -
  interpret k: s_finite_kernel borel borel k by fact
  interpret s_fin: qbs_s_finite Y \<beta> "\<mu> \<bind>\<^sub>k k"
    by(auto simp: qbs_s_finite_def in_Mx_def assms(3) mu_sets qbs_s_finite_axioms_def k.sets_bind_kernel[OF _ mu_sets] intro!:k.comp_s_finite_measure s_finite_measure_axioms)
  show "s \<bind> f = \<lbrakk>Y, \<beta>, \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  proof -
    {
      fix X' \<alpha>' \<mu>'
      assume "(X',\<alpha>',\<mu>') \<in> Rep_qbs_measure \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
      then have h: "X' = X" "qbs_s_finite X' \<alpha>' \<mu>'" "qbs_s_finite_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
        by(simp_all add: if_in_Rep_qbs_measure)
      then interpret s_fin_pq1: pair_qbs_s_finite X \<alpha> \<mu> \<alpha>' \<mu>'
        by(auto simp: pair_qbs_s_finite_def qbs_s_finite_axioms)
      have [simp]: "qbs_space_of (f (\<alpha>' r)) = Y" for r
        using qbs_Mx_to_X[OF qbs_morphism_Mx[OF assms(2) s_fin_pq1.pq2.in_Mx],of r]
        by(auto simp: monadM_qbs_space)
      have "(let Y = qbs_space_of (f (\<alpha>' undefined)) in case SOME (\<beta>, k). (\<lambda>r. f (\<alpha>' r)) = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<beta> \<in> qbs_Mx Y \<and> s_finite_kernel borel borel k of
             (\<beta>, k) \<Rightarrow> \<lbrakk>Y, \<beta>, \<mu>' \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) = \<lbrakk>Y, \<beta>, \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
      proof -
        have "(case SOME (\<beta>, k). (\<lambda>r. f (\<alpha>' r)) = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<beta> \<in> qbs_Mx Y \<and> s_finite_kernel borel borel k of (\<beta>, k) \<Rightarrow> \<lbrakk>Y, \<beta>, \<mu>' \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) = \<lbrakk>Y, \<beta>, \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
        proof(rule someI2_ex)
          show "\<exists>a. case a of (\<beta>, k) \<Rightarrow> (\<lambda>r. f (\<alpha>' r)) = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<beta> \<in> qbs_Mx Y \<and> s_finite_kernel borel borel k"
            using qbs_morphism_Mx[OF assms(2) s_fin_pq1.pq2.in_Mx]
            by(auto simp: comp_def monadM_qbs_Mx)
        next
          show "\<And>x. (case x of (\<beta>, k) \<Rightarrow> (\<lambda>r. f (\<alpha>' r)) = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<beta> \<in> qbs_Mx Y \<and> s_finite_kernel borel borel k) \<Longrightarrow> (case x of (\<beta>, k) \<Rightarrow> \<lbrakk>Y, \<beta>, \<mu>' \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) = \<lbrakk>Y, \<beta>, \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
          proof safe
            fix \<beta>' k'
            assume h':"(\<lambda>r. f (\<alpha>' r)) = (\<lambda>r. \<lbrakk>Y, \<beta>', k' r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta>' \<in> qbs_Mx Y" "s_finite_kernel borel borel k'"
            interpret k': s_finite_kernel borel borel k' by fact
            have "qbs_s_finite Y \<beta>' (\<mu>' \<bind>\<^sub>k k')"
              by(auto simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def h'(2) k'.sets_bind_kernel[OF _ s_fin_pq1.pq2.mu_sets] s_fin_pq1.pq2.mu_sets intro!:k'.comp_s_finite_measure s_fin_pq1.pq2.s_finite_measure_axioms)
            then interpret s_fin_pq2: pair_qbs_s_finite Y \<beta>' "\<mu>' \<bind>\<^sub>k k'" \<beta> "\<mu> \<bind>\<^sub>k k"
              by(auto simp: pair_qbs_s_finite_def s_fin.qbs_s_finite_axioms)
            show "\<lbrakk>Y, \<beta>', \<mu>' \<bind>\<^sub>k k'\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>Y, \<beta>, \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
            proof(rule s_fin_pq2.qbs_s_finite_measure_eq)
              show "distr (\<mu>' \<bind>\<^sub>k k') (qbs_to_measure Y) \<beta>' = distr (\<mu> \<bind>\<^sub>k k) (qbs_to_measure Y) \<beta>" (is "?lhs = ?rhs")
              proof -
                have "?lhs = \<mu>' \<bind>\<^sub>k (\<lambda>r. distr (k' r) (qbs_to_measure Y) \<beta>')"
                  by(simp add: k'.distr_bind_kernel[OF _ s_fin_pq1.pq2.mu_sets])
                also have "... = \<mu>' \<bind>\<^sub>k (\<lambda>r. qbs_l \<lbrakk>Y, \<beta>', k' r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
                  by(rule bind_kernel_cong_All,rule qbs_s_finite.qbs_l[symmetric,OF qbs_s_finite_All[where k=k' and M=borel]]) (auto simp: k'.s_finite_kernel_axioms)
                also have "... = \<mu>' \<bind>\<^sub>k (\<lambda>r. qbs_l (f (\<alpha>' r)))"
                  by(auto simp: fun_cong[OF h'(1)])
                also have "... = distr \<mu>' (qbs_to_measure X) \<alpha>' \<bind>\<^sub>k (\<lambda>x. qbs_l (f x))"
                  by(simp add: measure_kernel.bind_kernel_distr[OF measure_kernel.measure_kernel_comp[OF qbs_l_measure_kernel set_mp[OF l_preserves_morphisms assms(2)]]] sets_eq_imp_space_eq[OF s_fin_pq1.pq2.mu_sets])
                also have "... = distr \<mu> (qbs_to_measure X) \<alpha> \<bind>\<^sub>k (\<lambda>x. qbs_l (f x))"
                  by(simp add: qbs_s_finite_eq_dest(4)[OF h(3)])
                also have "... = \<mu> \<bind>\<^sub>k (\<lambda>r. qbs_l (f (\<alpha> r)))"
                  by(simp add: measure_kernel.bind_kernel_distr[OF measure_kernel.measure_kernel_comp[OF qbs_l_measure_kernel set_mp[OF l_preserves_morphisms assms(2)]]] sets_eq_imp_space_eq[OF mu_sets])
                also have "... = \<mu> \<bind>\<^sub>k (\<lambda>r. qbs_l \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
                  by(simp add: fun_cong[OF assms(5),simplified comp_def])
                also have "... = \<mu> \<bind>\<^sub>k (\<lambda>r. distr (k r) (qbs_to_measure Y) \<beta>)"
                  by(rule bind_kernel_cong_All,rule qbs_s_finite.qbs_l[OF qbs_s_finite_All[where k=k and M=borel]]) (auto simp: k.s_finite_kernel_axioms)
                also have "... = ?rhs"
                  by(simp add: k.distr_bind_kernel[OF _ mu_sets])
                finally show ?thesis .
              qed
            qed
          qed
        qed
        thus ?thesis by simp
      qed
    }
    show ?thesis
     unfolding bind_qbs_def rep_qbs_measure_def qbs_measure.rep_def assms(1)
     by(rule someI2, rule in_Rep_qbs_measure, auto) fact
  qed
  show "qbs_s_finite Y \<beta> (\<mu> \<bind>\<^sub>k k)"
    by(rule s_fin.qbs_s_finite_axioms)
qed


lemma bind_qbs_morphism':
  assumes "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
  shows "(\<lambda>x. x \<bind> f) \<in> monadM_qbs X \<rightarrow>\<^sub>Q monadM_qbs Y"
proof(rule qbs_morphismI)
  fix \<gamma>
  assume "\<gamma> \<in> qbs_Mx (monadM_qbs X)"
  from rep_qbs_Mx_monadM[OF this] obtain \<alpha> k where h:
   "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<alpha> (k r)"
    by metis
  from rep_qbs_Mx_monadM[OF qbs_morphism_Mx[OF assms this(2)]] obtain \<alpha>' k' where h':
  "f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<alpha>', k' r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha>' \<in> qbs_Mx Y" "s_finite_kernel borel borel k'" "\<And>r. qbs_s_finite Y \<alpha>' (k' r)"
    by metis
  have [simp]:"(\<lambda>x. x \<bind> f) \<circ> \<gamma> = (\<lambda>r. \<lbrakk>Y, \<alpha>', k r \<bind>\<^sub>k k'\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    by standard (simp add: h(1) qbs_s_finite.bind_qbs[OF h(4) _ assms h'(2,3,1)])
  show "(\<lambda>x. x \<bind> f) \<circ> \<gamma> \<in> qbs_Mx (monadM_qbs Y)"
    using h'(2) by(auto simp: s_finite_kernel.bind_kernel_s_finite_kernel[OF h(3) h'(3)] monadM_qbs_Mx intro!: exI[where x=\<alpha>'])
qed

lemma bind_qbs_return':
  assumes "x \<in> qbs_space (monadM_qbs X)"
  shows "x \<bind> return_qbs X = x"
proof -
  obtain \<alpha> \<mu> where h:"qbs_s_finite X \<alpha> \<mu>" "x = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using rep_qbs_space_monadM[OF assms] by blast 
  then interpret qs: qbs_s_finite X \<alpha> \<mu> by simp
  interpret prob_kernel borel borel "return borel"
    by(simp add: prob_kernel_def')
  show ?thesis
    by(simp add: qs.bind_qbs[OF h(2) return_qbs_morphism _ _ return_qbs_comp] s_finite_kernel_axioms bind_kernel_return''[OF qs.mu_sets] h(2)[symmetric])
qed

lemma bind_qbs_return:
  assumes "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
      and "x \<in> qbs_space X"
    shows "return_qbs X x \<bind> f = f x"
proof -
  from rep_qbs_space_monadM[OF qbs_morphism_space[OF assms]] obtain \<alpha> \<mu> where h:
   "f x = \<lbrakk>Y, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite Y \<alpha> \<mu>" by auto
  then interpret qs:qbs_s_finite Y \<alpha> \<mu> by simp
  interpret sk: s_finite_kernel borel borel "\<lambda>r. \<mu>"
    by(auto intro!: s_finite_measure.s_finite_kernel_const simp: s_finite_kernel_cong_sets[OF refl qs.mu_sets[symmetric]] qs.s_finite_measure_axioms qs.mu_not_empty)
  interpret rd: real_distribution "return borel 0"
    by(simp add: real_distribution_def prob_space_return real_distribution_axioms_def)
  interpret qbs_prob X "\<lambda>r. x" "return borel 0"
    by(rule rd.return_qbs_prob[OF assms(2)])
  show ?thesis
    using bind_qbs[OF rd.return_qbs[OF assms(2)] assms(1) qs.in_Mx sk.s_finite_kernel_axioms]
    by(simp add: h(1) sk.bind_kernel_return)
qed

lemma bind_qbs_assoc:
  assumes "s \<in> qbs_space (monadM_qbs X)"
          "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
      and "g \<in> Y \<rightarrow>\<^sub>Q monadM_qbs Z"
   shows "s \<bind> (\<lambda>x. f x \<bind> g) = (s \<bind> f) \<bind> g" (is "?lhs = ?rhs")
proof -
  obtain \<alpha> \<mu> where h:"s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
    using rep_qbs_space_monadM[OF assms(1)] by blast
  then interpret qs: qbs_s_finite X \<alpha> \<mu> by simp
  from rep_qbs_Mx_monadM[OF qbs_morphism_Mx[OF assms(2) qs.in_Mx]] obtain \<beta> k where h':
   "f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx Y" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite Y \<beta> (k r)"
    by metis
  from rep_qbs_Mx_monadM[OF qbs_morphism_Mx[OF assms(3) h'(2)]] obtain \<gamma> k' where h'':
   "g \<circ> \<beta> = (\<lambda>r. \<lbrakk>Z, \<gamma>, k' r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<gamma> \<in> qbs_Mx Z" "s_finite_kernel borel borel k'" "\<And>r. qbs_s_finite Z \<gamma> (k' r)"
    by metis
  have 1:"(\<lambda>x. f x \<bind> g) \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Z, \<gamma>, k r \<bind>\<^sub>k k'\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    by standard (simp add: qbs_s_finite.bind_qbs[OF h'(4) fun_cong[OF h'(1),simplified] assms(3) h''(2,3,1)])

  have "?lhs =  \<lbrakk>Z, \<gamma>, \<mu> \<bind>\<^sub>k (\<lambda>r. k r \<bind>\<^sub>k k')\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(rule qs.bind_qbs[OF h(1) qbs_morphism_compose[OF assms(2) bind_qbs_morphism'[OF assms(3)]] h''(2) s_finite_kernel.bind_kernel_s_finite_kernel[OF h'(3) h''(3)] 1])
  also have "... = \<lbrakk>Z, \<gamma>, \<mu> \<bind>\<^sub>k k \<bind>\<^sub>k k'\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(simp add: s_finite_kernel.bind_kernel_assoc[OF h'(3) h''(3) qs.mu_sets])
  also have "... = ?rhs"
    by(simp add: qbs_s_finite.bind_qbs[OF qs.bind_qbs_s_finite[OF h(1) assms(2) h'(2,3,1)] qs.bind_qbs[OF h(1) assms(2) h'(2,3,1)] assms(3) h''(2,3,1)])
  finally show ?thesis .
qed

lemma bind_qbs_cong:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs X)"
          "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
      and [qbs]:"f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
    shows "s \<bind> f = s \<bind> g"
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu> where h:
   "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" by auto
  interpret qbs_s_finite X \<alpha> \<mu> by fact
  from rep_qbs_Mx_monadM[OF qbs_morphism_Mx[OF assms(3) in_Mx]] obtain \<beta> k where h':
  "f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx Y" "s_finite_kernel borel borel k" by metis
  have g: "g \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y" "g \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    using qbs_Mx_to_X[OF in_Mx] assms(2) fun_cong[OF h'(1)]
    by(auto simp: assms(2)[symmetric] cong: qbs_morphism_cong)
  show ?thesis
    by(simp add: bind_qbs[OF h(1) assms(3) h'(2,3,1)] bind_qbs[OF h(1) g(1) h'(2,3) g(2)])
qed

subsubsection \<open> The Functorial Action \<close>
definition distr_qbs :: "['a quasi_borel, 'b quasi_borel,'a \<Rightarrow> 'b,'a qbs_measure] \<Rightarrow> 'b qbs_measure" where
"distr_qbs _ Y f sx \<equiv> sx \<bind> return_qbs Y \<circ> f"

lemma distr_qbs_morphism':
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows "distr_qbs X Y f \<in> monadM_qbs X \<rightarrow>\<^sub>Q monadM_qbs Y"
  unfolding distr_qbs_def
  by(rule bind_qbs_morphism'[OF qbs_morphism_comp[OF assms return_qbs_morphism]])

lemma(in qbs_s_finite)
  assumes "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
      and "f \<in> X \<rightarrow>\<^sub>Q Y"
    shows distr_qbs_s_finite:"qbs_s_finite Y (f \<circ> \<alpha>) \<mu>"
      and distr_qbs: "distr_qbs X Y f s = \<lbrakk>Y, f \<circ> \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
   by(auto intro!: bind_qbs[OF assms(1) qbs_morphism_comp[OF assms(2) return_qbs_morphism],of "f \<circ> \<alpha>" "return borel" ,simplified bind_kernel_return''[OF mu_sets]] bind_qbs_s_finite[OF assms(1) qbs_morphism_comp[OF assms(2) return_qbs_morphism],of "f \<circ> \<alpha>" "return borel" ,simplified bind_kernel_return''[OF mu_sets]]
             simp: distr_qbs_def return_qbs_comp[OF qbs_morphism_Mx[OF assms(2) in_Mx],simplified comp_assoc[symmetric]] qbs_morphism_Mx[OF assms(2) in_Mx] prob_kernel.s_finite_kernel_prob_kernel[of borel borel "return borel",simplified prob_kernel_def'])

lemma(in qbs_prob)
  assumes "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
      and "f \<in> X \<rightarrow>\<^sub>Q Y"
    shows distr_qbs_prob:"qbs_prob Y (f \<circ> \<alpha>) \<mu>"
  by(auto simp: distr_qbs_def prob_space_axioms intro!: qbs_s_finite.qbs_probI[OF distr_qbs_s_finite[OF assms]])

text \<open> We show that $M$ is a functor i.e. $M$ preserve identity and composition.\<close>
lemma distr_qbs_id:
  assumes "s \<in> qbs_space (monadM_qbs X)"
  shows "distr_qbs X X id s = s"
  using bind_qbs_return'[OF assms] by(simp add: distr_qbs_def)

lemma distr_qbs_comp:
  assumes "s \<in> qbs_space (monadM_qbs X)"
          "f \<in> X \<rightarrow>\<^sub>Q Y"
      and "g \<in> Y \<rightarrow>\<^sub>Q Z" 
    shows "((distr_qbs Y Z g) \<circ> (distr_qbs X Y f)) s = distr_qbs X Z (g \<circ> f) s"
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu> where h:
  "qbs_s_finite X \<alpha> \<mu>" "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" by metis
  have "qbs_s_finite Y (f \<circ> \<alpha>) \<mu>" "distr_qbs X Y f s = \<lbrakk>Y, f \<circ> \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(simp_all add: qbs_s_finite.distr_qbs_s_finite[OF h assms(2)] qbs_s_finite.distr_qbs[OF h assms(2)])
  from qbs_s_finite.distr_qbs[OF this assms(3)] qbs_s_finite.distr_qbs[OF h qbs_morphism_comp[OF assms(2,3)]]
  show ?thesis
    by(simp add: comp_assoc)
qed

subsubsection \<open> Join \<close>
definition join_qbs :: "'a qbs_measure qbs_measure \<Rightarrow> 'a qbs_measure" where
"join_qbs \<equiv> (\<lambda>sst. sst \<bind> id)"

lemma join_qbs_morphism[qbs]: "join_qbs \<in> monadM_qbs (monadM_qbs X) \<rightarrow>\<^sub>Q monadM_qbs X"
  by(simp add: join_qbs_def bind_qbs_morphism'[OF qbs_morphism_ident])

lemma
  assumes "qbs_s_finite (monadM_qbs X) \<beta> \<mu>"
          "ssx = \<lbrakk>monadM_qbs X, \<beta>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
          "\<alpha> \<in> qbs_Mx X"
          "s_finite_kernel borel borel k"
      and "\<beta> =(\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    shows qbs_s_finite_join_qbs_s_finite: "qbs_s_finite X \<alpha> (\<mu> \<bind>\<^sub>k k)"
      and qbs_s_finite_join_qbs: "join_qbs ssx = \<lbrakk>X, \<alpha>, \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  using qbs_s_finite.bind_qbs[OF assms(1,2) qbs_morphism_ident assms(3,4)] qbs_s_finite.bind_qbs_s_finite[OF assms(1,2) qbs_morphism_ident assms(3,4)]
  by(auto simp: assms(5) join_qbs_def)

subsubsection \<open> Strength \<close>
definition strength_qbs :: "['a quasi_borel,'b quasi_borel,'a \<times> 'b qbs_measure] \<Rightarrow> ('a \<times> 'b) qbs_measure" where
"strength_qbs W X = (\<lambda>(w,sx). let (_,\<alpha>,\<mu>) = rep_qbs_measure sx
                         in \<lbrakk>W \<Otimes>\<^sub>Q X, \<lambda>r. (w,\<alpha> r), \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"

lemma(in qbs_s_finite)
  assumes "w \<in> qbs_space W"
      and "sx = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    shows strength_qbs_s_finite: "qbs_s_finite (W \<Otimes>\<^sub>Q X) (\<lambda>r. (w,\<alpha> r)) \<mu>"
      and strength_qbs: "strength_qbs W X (w,sx) = \<lbrakk>W \<Otimes>\<^sub>Q X, \<lambda>r. (w,\<alpha> r), \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
proof -
  interpret qs: qbs_s_finite "W \<Otimes>\<^sub>Q X" "\<lambda>r. (w,\<alpha> r)" \<mu>
    by(auto simp: qbs_s_finite_def s_finite_measure_axioms qbs_s_finite_axioms_def mu_sets in_Mx_def assms(1) intro!: pair_qbs_MxI)
  show "qbs_s_finite (W \<Otimes>\<^sub>Q X) (\<lambda>r. (w,\<alpha> r)) \<mu>" by (rule qs.qbs_s_finite_axioms)
  show "strength_qbs W X (w,sx) = \<lbrakk>W \<Otimes>\<^sub>Q X, \<lambda>r. (w,\<alpha> r), \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  proof -
    {
      fix X' \<alpha>' \<mu>'
      assume "(X',\<alpha>',\<mu>') \<in> Rep_qbs_measure \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
      then have h: "X' = X" "qbs_s_finite X' \<alpha>' \<mu>'" "qbs_s_finite_eq (X,\<alpha>,\<mu>) (X',\<alpha>',\<mu>')"
        by(simp_all add: if_in_Rep_qbs_measure)
      then interpret qs': qbs_s_finite "W \<Otimes>\<^sub>Q X" "\<lambda>r. (w,\<alpha>' r)" \<mu>'
        by(auto simp: qbs_s_finite_def in_Mx_def assms(1) intro!: pair_qbs_MxI)
      interpret pq: pair_qbs_s_finite "W \<Otimes>\<^sub>Q X" "\<lambda>r. (w,\<alpha> r)" \<mu> "\<lambda>r. (w,\<alpha>' r)" \<mu>'
        by(auto simp: qs.qbs_s_finite_axioms qs'.qbs_s_finite_axioms pair_qbs_s_finite_def)
      have "\<lbrakk>W \<Otimes>\<^sub>Q X, \<lambda>r. (w, \<alpha>' r), \<mu>'\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>W \<Otimes>\<^sub>Q X, \<lambda>r. (w, \<alpha> r), \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
      proof(rule pq.qbs_s_finite_measure_eq'[symmetric])
        fix f :: "_ \<Rightarrow> ennreal"
        assume "f \<in> W \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q qbs_borel"
        then have f: "curry f w \<in> X \<rightarrow>\<^sub>Q qbs_borel"
          by (metis assms(1) qbs_morphism_curry qbs_morphism_space)
        show "(\<integral>\<^sup>+ x. f (w, \<alpha> x) \<partial>\<mu>) = (\<integral>\<^sup>+ x. f (w, \<alpha>' x) \<partial>\<mu>')" (is "?lhs = ?rhs")
        proof -
          have "?lhs = (\<integral>\<^sup>+ x. curry f w (\<alpha> x) \<partial>\<mu>)" by simp
          also have "... = (\<integral>\<^sup>+ x. curry f w (\<alpha>' x) \<partial>\<mu>')"
            using h(3) f by(auto simp: qbs_s_finite_eq_equiv qbs_s_finite_eq'_def h(1))
          also have "... = ?rhs" by simp
          finally show ?thesis .
        qed
      qed
    }
    show ?thesis
      by(simp add: strength_qbs_def rep_qbs_measure_def qbs_measure.rep_def assms(2)) (rule someI2, rule in_Rep_qbs_measure, auto, fact)
  qed
qed

lemma(in qbs_prob)
  assumes "w \<in> qbs_space W"
      and "sx = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    shows strength_qbs_prob: "qbs_prob (W \<Otimes>\<^sub>Q X) (\<lambda>r. (w,\<alpha> r)) \<mu>"
  by(auto intro!: qbs_s_finite.qbs_probI[OF strength_qbs_s_finite[OF assms]] prob_space_axioms)

lemma strength_qbs_natural:
  assumes "f \<in> X \<rightarrow>\<^sub>Q X'"
          "g \<in> Y \<rightarrow>\<^sub>Q Y'"
          "x \<in> qbs_space X"
      and "sy \<in> qbs_space (monadM_qbs Y)"
    shows "(distr_qbs (X \<Otimes>\<^sub>Q Y) (X' \<Otimes>\<^sub>Q Y') (map_prod f g) \<circ> strength_qbs X Y) (x,sy) = (strength_qbs X' Y' \<circ> map_prod f (distr_qbs Y Y' g)) (x,sy)"
          (is "?lhs = ?rhs")
proof -
  from rep_qbs_space_monadM[OF assms(4)] obtain \<alpha> \<mu> 
    where h:"sy = \<lbrakk>Y, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite Y \<alpha> \<mu>" by metis
  have "?lhs = (distr_qbs (X \<Otimes>\<^sub>Q Y) (X' \<Otimes>\<^sub>Q Y') (map_prod f g)) (\<lbrakk>X \<Otimes>\<^sub>Q Y, \<lambda>r. (x,\<alpha> r), \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    by(simp add: qbs_s_finite.strength_qbs[OF h(2) assms(3) h(1)])
  also have "... = \<lbrakk>X' \<Otimes>\<^sub>Q Y', map_prod f g \<circ> (\<lambda>r. (x, \<alpha> r)), \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using assms by(simp add: qbs_s_finite.distr_qbs[OF qbs_s_finite.strength_qbs_s_finite[OF h(2) assms(3) h(1)] refl ])
  also have "... = \<lbrakk>X' \<Otimes>\<^sub>Q Y',\<lambda>r. (f x, (g \<circ> \<alpha>) r), \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" by (simp add: comp_def)
  also have "... = ?rhs"
    by(simp add: qbs_s_finite.strength_qbs[OF qbs_s_finite.distr_qbs_s_finite[OF h(2,1) assms(2)] qbs_morphism_space[OF assms(1,3)] qbs_s_finite.distr_qbs[OF h(2,1) assms(2)]])
  finally show ?thesis .
qed

context
begin

interpretation rr : standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(auto intro!: pair_standard_borel_ne)

declare rr.from_real_to_real[simplified space_pair_measure,simplified,simp]

lemma rr_from_real_to_real_id[simp]: "rr.from_real \<circ> rr.to_real = id"
  by(auto simp: comp_def)

lemma
  assumes "\<alpha> \<in> qbs_Mx X"
          "\<beta> \<in> qbs_Mx (monadM_qbs Y)"
          "\<gamma> \<in> qbs_Mx Y"
          "s_finite_kernel borel borel k"
      and "\<beta> = (\<lambda>r. \<lbrakk>Y, \<gamma>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    shows strength_qbs_ab_r_s_finite: "qbs_s_finite (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<gamma> \<circ> rr.from_real) (distr (return borel r \<Otimes>\<^sub>M k r) borel rr.to_real)"
      and strength_qbs_ab_r: "strength_qbs X Y (\<alpha> r, \<beta> r) = \<lbrakk>X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<gamma> \<circ> rr.from_real, distr (return borel r \<Otimes>\<^sub>M k r) borel rr.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" (is ?goal2)
proof -
  interpret k: s_finite_kernel borel borel k by fact
  note 1[measurable_cong] = sets_return[of borel r] k.kernel_sets[of r,simplified]
  show "qbs_s_finite (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<gamma> \<circ> rr.from_real) (distr (return borel r \<Otimes>\<^sub>M k r) borel rr.to_real)"
    using assms(1,3) by(auto simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def qbs_Mx_is_morphisms r_preserves_product[symmetric] standard_borel_ne.standard_borel intro!: s_finite_measure.s_finite_measure_distr[OF pair_measure_s_finite_measure[OF prob_space.s_finite_measure_prob[OF prob_space_return[of r borel]] k.image_s_finite_measure[of r]]] qbs_morphism_comp[where Y="qbs_borel \<Otimes>\<^sub>Q qbs_borel"] qbs_morphism_space[OF qbs_morphism_space[OF qbs_morphism_map_prod]] standard_borel.qbs_morphism_measurable_intro[of "borel :: real measure"])
  then interpret qs: qbs_s_finite "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<gamma> \<circ> rr.from_real" "distr (return borel r \<Otimes>\<^sub>M k r) borel rr.to_real" .
  interpret qs2: qbs_s_finite Y \<gamma> "k r"
    by(auto simp: qbs_s_finite_def k.image_s_finite_measure in_Mx_def assms qbs_s_finite_axioms_def k.kernel_sets)
  interpret pq: pair_qbs_s_finite "X \<Otimes>\<^sub>Q Y" "\<lambda>l. (\<alpha> r, \<gamma> l)" "k r" "map_prod \<alpha> \<gamma> \<circ> rr.from_real" "distr (return borel r \<Otimes>\<^sub>M k r) borel rr.to_real"
    by (auto simp: pair_qbs_s_finite_def qs.qbs_s_finite_axioms qs2.strength_qbs_s_finite[OF qbs_Mx_to_X[OF assms(1),of r] fun_cong[OF assms(5)]])
  have [measurable]: "map_prod \<alpha> \<gamma> \<in> borel \<Otimes>\<^sub>M borel \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
  proof -
    have "map_prod \<alpha> \<gamma> \<in> qbs_borel \<Otimes>\<^sub>Q qbs_borel \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q Y"
      using assms by(auto intro!: qbs_morphism_map_prod simp: qbs_Mx_is_morphisms)
    also have "... \<subseteq> qbs_to_measure (qbs_borel \<Otimes>\<^sub>Q qbs_borel) \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
      by(rule l_preserves_morphisms)
    also have "... = borel \<Otimes>\<^sub>M borel \<rightarrow>\<^sub>M qbs_to_measure (X \<Otimes>\<^sub>Q Y)"
      using rr.lr_sets_ident l_preserves_morphisms by(auto simp add: r_preserves_product[symmetric])
    finally show ?thesis .
  qed
  show ?goal2
    unfolding qs2.strength_qbs[OF qbs_Mx_to_X[OF assms(1),of r] fun_cong[OF assms(5)]]
  proof(rule pq.qbs_s_finite_measure_eq)
    show "distr (k r) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (\<lambda>l. (\<alpha> r, \<gamma> l)) = distr (distr (return borel r \<Otimes>\<^sub>M k r) borel rr.to_real) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<gamma> \<circ> rr.from_real)"
         (is "?lhs = ?rhs")
    proof -
      have "?lhs = distr (k r) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<gamma> \<circ> Pair r)"
        by(simp add: comp_def)
      also have "... = distr (distr (k r) (borel \<Otimes>\<^sub>M borel) (Pair r)) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<gamma>)"
        by(auto intro!: distr_distr[symmetric])
      also have "... = distr (return borel r \<Otimes>\<^sub>M k r) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<gamma>)"
      proof -
        have "return borel r \<Otimes>\<^sub>M k r = distr (k r) (borel \<Otimes>\<^sub>M borel) (\<lambda>l. (r,l))"
          by(auto intro!: measure_eqI simp: sets_pair_measure_cong[OF refl 1(2)] qs2.emeasure_pair_measure_alt' emeasure_distr nn_integral_return[OF _  qs2.measurable_emeasure_Pair'])
        thus ?thesis by simp
      qed
      also have "... = ?rhs"
        by(simp add: distr_distr comp_def)
      finally show ?thesis .
    qed
  qed
qed

lemma strength_qbs_morphism[qbs]: "strength_qbs X Y \<in> X \<Otimes>\<^sub>Q monadM_qbs Y \<rightarrow>\<^sub>Q monadM_qbs (X \<Otimes>\<^sub>Q Y)"
proof(rule pair_qbs_morphismI)
  fix \<alpha> \<beta>
  assume h:"\<alpha> \<in> qbs_Mx X"
           "\<beta> \<in> qbs_Mx (monadM_qbs Y)"
  from rep_qbs_Mx_monadM[OF this(2)] obtain \<gamma> k where hb:
    "\<beta> = (\<lambda>r. \<lbrakk>Y, \<gamma>,  k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<gamma> \<in> qbs_Mx Y" "s_finite_kernel borel borel k"
    by metis
  have "s_finite_kernel borel borel (\<lambda>r. distr (return borel r \<Otimes>\<^sub>M k r) borel rr.to_real)"
    by(auto intro!: s_finite_kernel.distr_s_finite_kernel[where Y="borel \<Otimes>\<^sub>M borel"] s_finite_kernel_pair_measure[OF prob_kernel.s_finite_kernel_prob_kernel] simp:hb prob_kernel_def')
  thus "(\<lambda>r. strength_qbs X Y (\<alpha> r, \<beta> r)) \<in> qbs_Mx (monadM_qbs (X \<Otimes>\<^sub>Q Y))"
    using strength_qbs_ab_r[OF h hb(2,3,1)] strength_qbs_ab_r_s_finite[OF h hb(2,3,1)]
    by(auto simp: monadM_qbs_Mx qbs_s_finite_def in_Mx_def intro!: exI[where x="map_prod \<alpha> \<gamma> \<circ> rr.from_real"] exI[where x="\<lambda>r. distr (return borel r \<Otimes>\<^sub>M k r) borel rr.to_real"])
qed

lemma bind_qbs_morphism[qbs]: "(\<bind>) \<in> monadM_qbs X \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q monadM_qbs Y) \<Rightarrow>\<^sub>Q monadM_qbs Y"
proof -
  {
    fix f s
    assume h:"f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y" "s \<in> qbs_space (monadM_qbs X)"
    from rep_qbs_space_monadM[OF this(2)] obtain \<alpha> \<mu> where h':
     "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" by metis
    then interpret qbs_s_finite X \<alpha> \<mu> by simp
    from rep_qbs_Mx_monadM[OF qbs_morphism_Mx[OF h(1) in_Mx]] obtain \<beta> k
      where hb:"f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx Y" "s_finite_kernel borel borel k" by metis
    have "join_qbs (distr_qbs ((X \<Rightarrow>\<^sub>Q monadM_qbs Y) \<Otimes>\<^sub>Q X) (monadM_qbs Y) (\<lambda>fx. fst fx (snd fx)) (strength_qbs (X \<Rightarrow>\<^sub>Q monadM_qbs Y) X (f, s))) = s \<bind> f"
      using qbs_s_finite_join_qbs[OF qbs_s_finite.distr_qbs_s_finite[OF strength_qbs_s_finite[of f "X \<Rightarrow>\<^sub>Q monadM_qbs Y",OF h(1) h'(1)] strength_qbs[of f "X \<Rightarrow>\<^sub>Q monadM_qbs Y",OF h(1) h'(1)] qbs_morphism_eval] qbs_s_finite.distr_qbs[OF strength_qbs_s_finite[of f "X \<Rightarrow>\<^sub>Q monadM_qbs Y",OF h(1) h'(1)] strength_qbs[of f "X \<Rightarrow>\<^sub>Q monadM_qbs Y",OF h(1) h'(1)] qbs_morphism_eval] hb(2,3)] hb(1)
      by(simp add: bind_qbs[OF h'(1) h(1) hb(2,3,1)] comp_def)
  }
  thus ?thesis
    by(auto intro!: arg_swap_morphism[OF curry_preserves_morphisms[OF qbs_morphism_cong'[of _ "join_qbs \<circ> (distr_qbs (exp_qbs X (monadM_qbs Y) \<Otimes>\<^sub>Q X) (monadM_qbs Y) (\<lambda>fx. (fst fx) (snd fx))) \<circ> (strength_qbs (exp_qbs X (monadM_qbs Y)) X)"]]] qbs_morphism_comp distr_qbs_morphism' strength_qbs_morphism join_qbs_morphism qbs_morphism_eval simp: pair_qbs_space)
qed

lemma strength_qbs_law1:
  assumes "x \<in> qbs_space (unit_quasi_borel \<Otimes>\<^sub>Q monadM_qbs X)"
  shows "snd x = (distr_qbs (unit_quasi_borel \<Otimes>\<^sub>Q X) X snd \<circ> strength_qbs unit_quasi_borel X) x"
proof -
  obtain \<alpha> \<mu> where h:
   "qbs_s_finite X \<alpha> \<mu>" "(snd x) = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using rep_qbs_space_monadM[of "snd x" X] assms by (auto simp: pair_qbs_space) metis
  have [simp]: "((),snd x) = x"
    using SigmaE assms by (auto simp: pair_qbs_space)
  show ?thesis
    using qbs_s_finite.distr_qbs[OF qbs_s_finite.strength_qbs_s_finite[OF h(1) _ h(2),of "fst x" unit_quasi_borel] qbs_s_finite.strength_qbs[OF h(1) _ h(2)] snd_qbs_morphism]
    by(auto simp: comp_def,simp add: h(2))
qed

lemma strength_qbs_law2:
  assumes "x \<in> qbs_space ((X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q monadM_qbs Z)"
  shows "(strength_qbs X (Y \<Otimes>\<^sub>Q Z) \<circ> (map_prod id (strength_qbs Y Z)) \<circ> (\<lambda>((x,y),z). (x,(y,z)))) x =
         (distr_qbs ((X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q Z) (X \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q Z)) (\<lambda>((x,y),z). (x,(y,z))) \<circ> strength_qbs (X \<Otimes>\<^sub>Q Y) Z) x"
         (is "?lhs = ?rhs")
proof -
  obtain \<alpha> \<mu> where h:
   "qbs_s_finite Z \<alpha> \<mu>" "snd x = \<lbrakk>Z, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using rep_qbs_space_monadM[of "snd x" Z] assms by (auto simp: pair_qbs_space) metis
  then have "?lhs = \<lbrakk>X \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q Z, \<lambda>r. (fst (fst x), snd (fst x), \<alpha> r), \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using assms qbs_s_finite.strength_qbs_s_finite[OF h(1) _ h(2),of "snd (fst x)" Y]
    by(auto intro!: qbs_s_finite.strength_qbs simp: pair_qbs_space)
  also have "... = ?rhs"
    using qbs_s_finite.distr_qbs[OF qbs_s_finite.strength_qbs_s_finite[OF h(1) _ h(2),of "fst x" "X \<Otimes>\<^sub>Q Y"] qbs_s_finite.strength_qbs[OF h(1) _ h(2),of "fst x" "X \<Otimes>\<^sub>Q Y"] qbs_morphism_pair_assoc1] assms
    by(auto simp: comp_def pair_qbs_space)
  finally show ?thesis .
qed

lemma strength_qbs_law3:
  assumes "x \<in> qbs_space (X \<Otimes>\<^sub>Q Y)"
  shows "return_qbs (X \<Otimes>\<^sub>Q Y) x = (strength_qbs X Y \<circ> (map_prod id (return_qbs Y))) x"
proof -
  interpret qp: qbs_prob Y "\<lambda>r. snd x" "return borel 0"
    using assms by(auto simp: prob_space_return pair_qbs_space qbs_prob_def in_Mx_def real_distribution_def real_distribution_axioms_def)
  show ?thesis
    using qp.strength_qbs[OF _ qp.return_qbs[of "snd x" Y],of "fst x" X] qp.return_qbs[OF assms] assms
    by(auto simp: pair_qbs_space)
qed

lemma strength_qbs_law4:
  assumes "x \<in> qbs_space (X \<Otimes>\<^sub>Q monadM_qbs (monadM_qbs Y))"
  shows "(strength_qbs X Y \<circ> map_prod id join_qbs) x = (join_qbs \<circ> distr_qbs (X \<Otimes>\<^sub>Q monadM_qbs Y) (monadM_qbs (X \<Otimes>\<^sub>Q Y)) (strength_qbs X Y) \<circ> strength_qbs X (monadM_qbs Y)) x"
        (is "?lhs = ?rhs")
proof -
  from assms rep_qbs_space_monadM[of "snd x" "monadM_qbs Y"] obtain \<beta> \<mu>
    where h:"qbs_s_finite (monadM_qbs Y) \<beta> \<mu>" "snd x = \<lbrakk>monadM_qbs Y, \<beta>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by (auto simp: pair_qbs_space) metis
  with rep_qbs_Mx_monadM[of \<beta> Y] obtain \<gamma> k
    where h': "\<gamma> \<in> qbs_Mx Y" "s_finite_kernel borel borel k" "\<beta> = (\<lambda>r. \<lbrakk>Y, \<gamma>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
      and h'': "\<And>r. qbs_s_finite Y \<gamma> (k r)"
    by(auto simp: qbs_s_finite_def in_Mx_def) metis
  have "?lhs = \<lbrakk>X \<Otimes>\<^sub>Q Y, \<lambda>r. (fst x, \<gamma> r), \<mu> \<bind>\<^sub>k k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using qbs_s_finite.strength_qbs[OF qbs_s_finite_join_qbs_s_finite[OF h h'] _ qbs_s_finite_join_qbs[OF h h'],of "fst x" X] assms
    by(auto simp: pair_qbs_space)
  also have "... = ?rhs"
    using qbs_s_finite_join_qbs[OF qbs_s_finite.distr_qbs_s_finite[OF qbs_s_finite.strength_qbs_s_finite[OF h(1) _ h(2),of "fst x" X] qbs_s_finite.strength_qbs[OF h(1) _ h(2),of "fst x"] strength_qbs_morphism] qbs_s_finite.distr_qbs[OF qbs_s_finite.strength_qbs_s_finite[OF h(1) _ h(2),of "fst x" X] qbs_s_finite.strength_qbs[OF h(1) _ h(2),of "fst x"] strength_qbs_morphism] pair_qbs_MxI h'(2),of "\<lambda>r. (fst x, \<gamma> r)",simplified comp_def qbs_s_finite.strength_qbs[OF h'' _ fun_cong[OF h'(3)],of "fst x" X]] assms h'(1)
    by(auto simp: pair_qbs_space qbs_s_finite_def in_Mx_def)
  finally show ?thesis .
qed

lemma distr_qbs_morphism[qbs]: "distr_qbs X Y \<in> (X \<Rightarrow>\<^sub>Q Y) \<rightarrow>\<^sub>Q (monadM_qbs X \<Rightarrow>\<^sub>Q monadM_qbs Y)"
proof -
  have [simp]: "distr_qbs X Y = (\<lambda>f sx. sx \<bind> return_qbs Y \<circ> f)"
    by standard+ (auto simp: distr_qbs_def)
  show ?thesis
    by simp
qed

lemma
  assumes "\<alpha> \<in> qbs_Mx X" "\<beta> \<in> qbs_Mx Y"
  shows return_qbs_pair_Mx: "return_qbs (X \<Otimes>\<^sub>Q Y) (\<alpha> r, \<beta> k) = \<lbrakk>X \<Otimes>\<^sub>Q Y,map_prod \<alpha> \<beta> \<circ> rr.from_real, distr (return borel r \<Otimes>\<^sub>M return borel k) borel rr.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    and return_qbs_pair_Mx_prob: "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> rr.from_real) (distr (return borel r \<Otimes>\<^sub>M return borel k) borel rr.to_real)"
proof -
  note [measurable_cong] = sets_return[of borel]
  interpret qp: qbs_prob "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<beta> \<circ> rr.from_real" "distr (return borel r \<Otimes>\<^sub>M return borel k) borel rr.to_real"
    using qbs_closed1_dest[OF assms(1)] qbs_closed1_dest[OF assms(2)]
    by(auto intro!: prob_space.prob_space_distr prob_space_pair simp: comp_def prob_space_return pair_qbs_Mx qbs_prob_def in_Mx_def real_distribution_def real_distribution_axioms_def)
  show "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> rr.from_real) (distr (return borel r \<Otimes>\<^sub>M return borel k) borel rr.to_real)"
    by standard
  show "return_qbs (X \<Otimes>\<^sub>Q Y) (\<alpha> r, \<beta> k) = \<lbrakk>X \<Otimes>\<^sub>Q Y,map_prod \<alpha> \<beta> \<circ> rr.from_real, distr (return borel r \<Otimes>\<^sub>M return borel k) borel rr.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (strength_qbs X Y \<circ> map_prod id (return_qbs Y)) (\<alpha> r, \<beta> k)"
      by(rule strength_qbs_law3[of "(\<alpha> r, \<beta> k)" X Y], insert assms) (auto simp: qbs_Mx_to_X pair_qbs_space)
    also have "... = strength_qbs X Y (\<alpha> r, \<lbrakk>Y, \<beta>, return borel k\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
      using fun_cong[OF return_qbs_comp[OF assms(2)]] by simp
    also have "... = ?rhs"
      by(rule strength_qbs_ab_r[OF assms(1) _ assms(2)]) (auto intro!: qbs_closed2_dest qbs_s_finite.in_space_monadM s_finite_measure.s_finite_kernel_const[of "return borel k",simplified s_finite_kernel_cong_sets[OF _ sets_return]] prob_space.s_finite_measure_prob simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def assms(2) prob_space_return)
    finally show ?thesis .
  qed
qed

lemma bind_bind_return_distr:
  assumes "s_finite_measure \<mu>"
      and "s_finite_measure \<nu>"
      and [measurable_cong]: "sets \<mu> = sets borel" "sets \<nu> = sets borel"
    shows "\<mu> \<bind>\<^sub>k (\<lambda>r. \<nu> \<bind>\<^sub>k (\<lambda>l. distr (return borel r \<Otimes>\<^sub>M return borel l) borel rr.to_real))
           = distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real"
    (is "?lhs = ?rhs")
proof -
  interpret rd1: s_finite_measure \<mu> by fact
  interpret rd2: s_finite_measure \<nu> by fact
  have ne: "space \<mu> \<noteq> {}" "space \<nu> \<noteq> {}"
    by(auto simp: sets_eq_imp_space_eq assms(3,4))

  have "?lhs = \<mu> \<bind>\<^sub>k (\<lambda>r. \<nu> \<bind>\<^sub>k (\<lambda>l. distr (return (borel \<Otimes>\<^sub>M borel) (r,l)) borel rr.to_real))"
    by(simp add: pair_measure_return)
  also have "... = \<mu> \<bind>\<^sub>k (\<lambda>r. \<nu> \<bind>\<^sub>k (\<lambda>l. distr (return (\<mu> \<Otimes>\<^sub>M \<nu>) (r, l)) borel rr.to_real))"
  proof -
    have "return (borel \<Otimes>\<^sub>M borel) = return (\<mu> \<Otimes>\<^sub>M \<nu>)"
      by(auto intro!: return_sets_cong sets_pair_measure_cong simp: assms(3,4))
    thus ?thesis by simp
  qed
  also have "... = \<mu> \<bind>\<^sub>k (\<lambda>r. distr (\<nu> \<bind>\<^sub>k (\<lambda>l. (return (\<mu> \<Otimes>\<^sub>M \<nu>) (r, l)))) borel rr.to_real)"
    by(auto intro!: bind_kernel_cong_All measure_kernel.distr_bind_kernel[of \<nu> "\<mu> \<Otimes>\<^sub>M \<nu>",symmetric] simp: ne measure_kernel_def space_pair_measure)
  also have "... = distr (\<mu> \<bind>\<^sub>k (\<lambda>r. \<nu> \<bind>\<^sub>k (\<lambda>l. return (\<mu> \<Otimes>\<^sub>M \<nu>) (r, l)))) borel rr.to_real"
    by(auto intro!: measure_kernel.distr_bind_kernel[of \<mu> "\<mu> \<Otimes>\<^sub>M \<nu>",symmetric] s_finite_kernel.axioms(1) s_finite_kernel.bind_kernel_s_finite_kernel'[where Y=\<nu>] s_finite_measure.s_finite_kernel_const[OF assms(2)] prob_kernel.s_finite_kernel_prob_kernel[of "\<mu> \<Otimes>\<^sub>M \<nu>"] simp: ne prob_kernel_def')
  also have "... = ?rhs"
    by(simp add: pair_measure_eq_bind_s_finite[OF assms(1,2),symmetric])
  finally show ?thesis .
qed

end

context
begin
interpretation rr : standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(auto intro!: pair_standard_borel_ne)

lemma from_real_rr_qbs_morphism[qbs]: "rr.from_real \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel \<Otimes>\<^sub>Q qbs_borel"
  by (metis borel_prod qbs_Mx_R qbs_Mx_is_morphisms qbs_borel_prod rr.from_real_measurable)

end

context pair_qbs_s_finites
begin

interpretation rr : standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(auto intro!: pair_standard_borel_ne)

sublocale qbs_s_finite "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<beta> \<circ> rr.from_real" "distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real"
  by(auto simp: qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def qbs_Mx_is_morphisms pq1.s_finite_measure_axioms pq2.s_finite_measure_axioms intro!: s_finite_measure.s_finite_measure_distr[OF pair_measure_s_finite_measure])

lemma qbs_bind_bind_return_qp:
 "\<lbrakk>Y,\<beta>,\<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> (\<lambda>y. \<lbrakk>X,\<alpha>,\<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y))) = \<lbrakk>X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> rr.from_real, distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<lbrakk>X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> rr.from_real, \<nu> \<bind>\<^sub>k (\<lambda>l. \<mu> \<bind>\<^sub>k (\<lambda>r. distr (return borel r \<Otimes>\<^sub>M return borel l) borel rr.to_real))\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(auto intro!: pq2.bind_qbs[OF refl] s_finite_kernel.bind_kernel_s_finite_kernel'[where Y=\<mu>] s_finite_measure.s_finite_kernel_const s_finite_kernel.distr_s_finite_kernel[where Y="borel \<Otimes>\<^sub>M borel"] prob_kernel.s_finite_kernel_prob_kernel[of "borel \<Otimes>\<^sub>M \<mu>"] simp: sets_eq_imp_space_eq[OF pq1.mu_sets] pq1.s_finite_measure_axioms split_beta' pair_measure_return[of _ "snd _"] prob_kernel_def')
      (auto intro!: pq1.bind_qbs prob_kernel.s_finite_kernel_prob_kernel simp: comp_def return_qbs_pair_Mx qbs_Mx_is_morphisms prob_kernel_def')
  also have "... = ?rhs"
  proof -
    have "\<nu> \<bind>\<^sub>k (\<lambda>l. \<mu> \<bind>\<^sub>k (\<lambda>r. distr (return borel r \<Otimes>\<^sub>M return borel l) borel rr.to_real)) = distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real" 
      by(auto simp: bind_bind_return_distr[OF pq1.s_finite_measure_axioms pq2.s_finite_measure_axioms pq1.mu_sets pq2.mu_sets,symmetric] pq1.s_finite_measure_axioms pq2.s_finite_measure_axioms prob_kernel_def' intro!: bind_kernel_rotate[where Z=borel] prob_kernel.s_finite_kernel_prob_kernel)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma qbs_bind_bind_return_pq:
 "\<lbrakk>X,\<alpha>,\<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> (\<lambda>x. \<lbrakk>Y,\<beta>,\<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y))) = \<lbrakk>X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> rr.from_real, distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<lbrakk>X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> rr.from_real, \<mu> \<bind>\<^sub>k (\<lambda>r. \<nu> \<bind>\<^sub>k (\<lambda>l. distr (return borel r \<Otimes>\<^sub>M return borel l) borel rr.to_real))\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(auto intro!: pq1.bind_qbs[OF refl]s_finite_kernel.bind_kernel_s_finite_kernel'[where Y=\<nu>] s_finite_measure.s_finite_kernel_const s_finite_kernel.distr_s_finite_kernel[where Y="borel \<Otimes>\<^sub>M borel"] prob_kernel.s_finite_kernel_prob_kernel[of "borel \<Otimes>\<^sub>M \<nu>"] simp: sets_eq_imp_space_eq[OF pq2.mu_sets] pq2.s_finite_measure_axioms split_beta' pair_measure_return[of _ "fst _"] prob_kernel_def')
      (auto intro!: pq2.bind_qbs prob_kernel.s_finite_kernel_prob_kernel simp: comp_def return_qbs_pair_Mx qbs_Mx_is_morphisms prob_kernel_def')
  also have "... = ?rhs"
    by(simp add: bind_bind_return_distr[OF pq1.s_finite_measure_axioms pq2.s_finite_measure_axioms pq1.mu_sets pq2.mu_sets])
  finally show ?thesis .
qed

end

lemma bind_qbs_return_rotate:
  assumes "p \<in> qbs_space (monadM_qbs X)"
      and "q \<in> qbs_space (monadM_qbs Y)"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y))) = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))"
proof -
  from rep_qbs_space_monadM[OF assms(1)] rep_qbs_space_monadM[OF assms(2)]
  obtain \<alpha> \<mu> \<beta> \<nu> where h: "p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "q = \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" "qbs_s_finite Y \<beta> \<nu>"
    by metis
  then interpret pair_qbs_s_finites X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_s_finites_def)
  show ?thesis
    by(simp add: h(1,2) qbs_bind_bind_return_pq qbs_bind_bind_return_qp)
qed

lemma qbs_bind_bind_return1:
  assumes [qbs]: "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadM_qbs Z"
          "p \<in> qbs_space (monadM_qbs X)"
          "q \<in> qbs_space (monadM_qbs Y)"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f (x,y))) = (q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> f"
          (is "?lhs = ?rhs")
proof -
  have "?lhs = q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y) \<bind> f))"
    by(auto intro!: bind_qbs_cong[OF assms(3),where Y=Z] bind_qbs_cong[OF assms(2),where Y=Z] simp: bind_qbs_return[OF assms(1),simplified pair_qbs_space])
  also have "... = q \<bind> (\<lambda>y. (p \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y))) \<bind> f)"
    by(auto intro!: bind_qbs_cong[OF assms(3),where Y=Z] bind_qbs_assoc[OF assms(2) _ assms(1)] simp: )
  also have "... = ?rhs"
    by(simp add: bind_qbs_assoc[OF assms(3) _ assms(1)])
  finally show ?thesis .
qed

lemma qbs_bind_bind_return2:
  assumes [qbs]:"f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadM_qbs Z"
          "p \<in> qbs_space (monadM_qbs X)" "q \<in> qbs_space (monadM_qbs Y)"
    shows "p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f (x,y))) = (p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> f"
          (is "?lhs = ?rhs")      
proof -
  have "?lhs = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y) \<bind> f))"
    by(auto intro!: bind_qbs_cong[OF assms(2),where Y=Z] bind_qbs_cong[OF assms(3),where Y=Z] simp: bind_qbs_return[OF assms(1),simplified pair_qbs_space])
  also have "... = p \<bind> (\<lambda>x. (q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y))) \<bind> f)"
    by(auto intro!: bind_qbs_cong[OF assms(2),where Y=Z] bind_qbs_assoc[OF assms(3) _ assms(1)])
  also have "... = ?rhs"
    by(simp add: bind_qbs_assoc[OF assms(2) _ assms(1)])
  finally show ?thesis .
qed

corollary bind_qbs_rotate:
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadM_qbs Z"
          "p \<in> qbs_space (monadM_qbs X)"
      and "q \<in> qbs_space (monadM_qbs Y)"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f (x,y))) = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f (x,y)))"
  by(simp add: qbs_bind_bind_return1[OF assms] qbs_bind_bind_return2[OF assms] bind_qbs_return_rotate assms)

context pair_qbs_s_finites
begin

interpretation rr : standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(auto intro!: pair_standard_borel_ne)

lemma
  assumes [qbs]:"f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  shows qbs_bind_bind_return:"\<lbrakk>X,\<alpha>,\<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> (\<lambda>x. \<lbrakk>Y,\<beta>,\<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> (\<lambda>y. return_qbs Z (f (x,y)))) = \<lbrakk>Z, f \<circ> (map_prod \<alpha> \<beta> \<circ> rr.from_real), distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" (is "?lhs = ?rhs")
    and qbs_bind_bind_return_s_finite: "qbs_s_finite Z (f \<circ> (map_prod \<alpha> \<beta> \<circ> rr.from_real)) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real)"
proof -
  show "qbs_s_finite Z (f \<circ> (map_prod \<alpha> \<beta> \<circ> rr.from_real)) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real)"
    using qbs_s_finite_axioms by(auto simp: qbs_s_finite_def in_Mx_def qbs_Mx_is_morphisms)
  have "?lhs = \<lbrakk>X,\<alpha>,\<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> (\<lambda>x. \<lbrakk>Y,\<beta>,\<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y))) \<bind> return_qbs Z \<circ> f"
    by(auto simp: comp_def intro!: qbs_bind_bind_return2[of "return_qbs Z \<circ> f" _ _ Z,simplified comp_def])
  also have "... = \<lbrakk>X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> rr.from_real, distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<bind> return_qbs Z \<circ> f"
    by(simp add: qbs_bind_bind_return_pq)
  also have "... = ?rhs"
    by(rule distr_qbs[OF refl assms,simplified distr_qbs_def])
  finally show "?lhs = ?rhs" .
qed

end

subsubsection \<open>The Probability Monad\<close>

definition "monadP_qbs X \<equiv> sub_qbs (monadM_qbs X) {s. prob_space (qbs_l s)}"

lemma
  shows qbs_space_monadPM: "s \<in> qbs_space (monadP_qbs X) \<Longrightarrow> s \<in> qbs_space (monadM_qbs X)"
    and qbs_Mx_monadPM: "f \<in> qbs_Mx (monadP_qbs X) \<Longrightarrow> f \<in> qbs_Mx (monadM_qbs X)"
  by(simp_all add: monadP_qbs_def sub_qbs_space sub_qbs_Mx)

lemma monadP_qbs_space: "qbs_space (monadP_qbs X) = {s. qbs_space_of s = X \<and> prob_space (qbs_l s)}"
  by(auto simp: monadP_qbs_def sub_qbs_space monadM_qbs_space)

lemma rep_qbs_space_monadP:
  assumes "s \<in> qbs_space (monadP_qbs X)"
  obtains \<alpha> \<mu> where "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_prob X \<alpha> \<mu>"
proof -
  obtain \<alpha> \<mu> where h:"s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
    using assms rep_qbs_space_monadM[of s X] by(auto simp: monadP_qbs_def sub_qbs_space)
  interpret qbs_s_finite X \<alpha> \<mu> by fact
  have "prob_space \<mu>"
    by(rule prob_space_distrD[of \<alpha> _ "qbs_to_measure X"]) (insert assms, auto simp: qbs_l[symmetric] h(1)[symmetric] monadP_qbs_space)
  thus ?thesis
    by (simp add: h(1) in_Mx_axioms mu_sets qbs_prob.intro real_distribution_axioms_def real_distribution_def that)
qed

lemma qbs_l_prob_space:
  "s \<in> qbs_space (monadP_qbs X) \<Longrightarrow> prob_space (qbs_l s)"
  by(auto simp: monadP_qbs_space)

lemma monadP_qbs_empty_iff:
 "(qbs_space X = {}) = (qbs_space (monadP_qbs X) = {})"
proof
  show "qbs_space X = {} \<Longrightarrow> qbs_space (monadP_qbs X) = {}"
  using qbs_s_space_of_not_empty by(auto simp add: monadP_qbs_space)
next
  assume "qbs_space (monadP_qbs X) = {}"
  then have h:"\<And>s. qbs_space_of s = X \<Longrightarrow> \<not> prob_space (qbs_l s)"
    by(simp add: monadP_qbs_space)
  show "qbs_space X = {}"
  proof(rule ccontr)
    assume "qbs_space X \<noteq> {}"
    then obtain a where a:"a \<in> qbs_Mx X" by (auto simp: qbs_empty_equiv)
    then interpret qbs_prob X a "return borel 0"
      by(auto simp: qbs_prob_def in_Mx_def real_distribution_axioms_def real_distribution_def prob_space_return)
    have "qbs_space_of \<lbrakk>X, a, return borel 0\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = X" "prob_space (qbs_l \<lbrakk>X, a, return borel 0\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
      by(auto simp: qbs_l intro!: prob_space_distr)
    with h show False by simp
  qed
qed

lemma in_space_monadP_qbs_pred: "qbs_pred (monadM_qbs X) (\<lambda>s. s \<in> monadP_qbs X)"
  by(rule qbs_morphism_cong'[where f="\<lambda>s. prob_space (qbs_l s)"],auto simp: qbs_l_prob_pred)
    (auto simp: monadP_qbs_def sub_qbs_space)

lemma(in qbs_prob) in_space_monadP[qbs]: "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<in> qbs_space (monadP_qbs X)"
  by(auto simp: monadP_qbs_space qbs_l prob_space_distr)

lemma qbs_morphism_monadPD: "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y \<Longrightarrow> f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
  unfolding monadP_qbs_def by(rule qbs_morphism_subD)

lemma qbs_morphism_monadPD': "f \<in> monadM_qbs X \<rightarrow>\<^sub>Q Y \<Longrightarrow> f \<in> monadP_qbs X \<rightarrow>\<^sub>Q Y"
  unfolding monadP_qbs_def by(rule qbs_morphism_subI2)

lemma qbs_morphism_monadPI:
  assumes "\<And>x. x \<in> qbs_space X \<Longrightarrow> prob_space (qbs_l (f x))" "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
  shows "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  using assms by(auto simp: monadP_qbs_def intro!:qbs_morphism_subI1)

lemma qbs_morphism_monadPI':
  assumes "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x \<in> qbs_space (monadP_qbs Y)" "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
  shows "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  using assms by(auto intro!: qbs_morphism_monadPI simp: monadP_qbs_space)

lemma qbs_morphism_monadPI'':
  assumes "f \<in> monadM_qbs X \<rightarrow>\<^sub>Q monadM_qbs Y" "\<And>s. s \<in> qbs_space (monadP_qbs X) \<Longrightarrow> f s \<in> qbs_space (monadP_qbs Y)"
  shows "f \<in> monadP_qbs X \<rightarrow>\<^sub>Q monadP_qbs Y"
proof -
  have 1:"\<And>X. monadP_qbs X = sub_qbs (monadM_qbs X) {s. qbs_space_of s = X \<and> prob_space (qbs_l s)}" (is "\<And>X. ?l X = ?r X")
  proof -
    fix X
    have "?l X = sub_qbs (sub_qbs (monadM_qbs X) (qbs_space (monadM_qbs X))) {s. prob_space (qbs_l s)}"
      by(simp add: sub_qbs_ident monadP_qbs_def)
    also have "... = ?r X"
      by(auto simp: sub_qbs_sub_qbs monadM_qbs_space Collect_conj_eq)
    finally show "?l X = ?r X" .
  qed
  show ?thesis
    unfolding 1 using assms(2) by(auto intro!: qbs_morphism_subsubI[OF assms(1),of " {s. qbs_space_of s = X \<and> prob_space (qbs_l s)}" " {s. qbs_space_of s = Y \<and> prob_space (qbs_l s)}"] simp: 1 sub_qbs_space monadM_qbs_space)
qed

lemma monadP_qbs_Mx: "qbs_Mx (monadP_qbs X) = {\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n |\<alpha> k. \<alpha> \<in> qbs_Mx X \<and> k \<in> borel \<rightarrow>\<^sub>M prob_algebra borel}"
proof safe
  fix \<gamma>
  assume h:"\<gamma> \<in> qbs_Mx (monadP_qbs X)"
  then obtain \<alpha> k where h1:
   "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<alpha> (k r)"
    using rep_qbs_Mx_monadM[of \<gamma> X] by(simp add: monadP_qbs_def sub_qbs_Mx) metis
  interpret s_finite_kernel borel borel k by fact
  have "\<gamma> \<in> UNIV \<rightarrow> {s. qbs_space_of s = X \<and> prob_space (qbs_l s)}"
    using h qbs_Mx_to_X[OF h] by(auto simp: monadP_qbs_def sub_qbs_Mx monadM_qbs_space sub_qbs_space)
  hence "\<And>r. prob_space (k r)"
    using h1(2) by(auto simp add: h1(1) Pi_iff qbs_s_finite.qbs_l[OF h1(4)] intro!: prob_space_distrD[of \<alpha> _ "qbs_to_measure X"])
  hence "prob_kernel borel borel k"
    by(auto simp: prob_kernel_def prob_kernel_axioms_def measure_kernel_axioms)
  with h1(1,2) show "\<exists>\<alpha> k. \<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<and> \<alpha> \<in> qbs_Mx X \<and> k \<in> borel \<rightarrow>\<^sub>M prob_algebra borel"
    by(auto intro!: exI[where x=\<alpha>] exI[where x=k] simp: prob_kernel_def')
next
  fix \<alpha> and k :: "real \<Rightarrow> real measure"
  assume h:"\<alpha> \<in> qbs_Mx X" "k \<in> borel \<rightarrow>\<^sub>M prob_algebra borel"
  then interpret pk: prob_kernel borel borel k
    by(simp add: prob_kernel_def'[symmetric])
  have qp: "qbs_prob X \<alpha> (k r)" for r
    using h by(auto simp: qbs_prob_def in_Mx_def pk.kernel_sets pk.prob_spaces real_distribution_axioms_def real_distribution_def)
  show "(\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<in> qbs_Mx (monadP_qbs X)"
    using h(1) qp by(auto simp: monadP_qbs_def sub_qbs_Mx monadM_qbs_space qbs_s_finite.qbs_l[OF qbs_prob.qbs_s_finite[OF qp]] qbs_s_finite.qbs_space_of[OF qbs_prob.qbs_s_finite[OF qp]] monadM_qbs_Mx qbs_prob_def  real_distribution_def intro!: exI[where x=\<alpha>] exI[where x=k] h pk.s_finite_kernel_axioms prob_space.prob_space_distr)
qed

lemma rep_qbs_Mx_monadP:
  assumes "\<gamma> \<in> qbs_Mx (monadP_qbs X)"
  obtains \<alpha> k where "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "k \<in> borel \<rightarrow>\<^sub>M prob_algebra borel" "\<And>r. qbs_prob X \<alpha> (k r)"
proof -
  have "\<And>\<alpha> r k. \<alpha> \<in> qbs_Mx X \<Longrightarrow> k \<in> borel \<rightarrow>\<^sub>M prob_algebra borel \<Longrightarrow> qbs_prob X \<alpha> (k r)"
    by(auto simp: qbs_prob_def in_Mx_def real_distribution_def real_distribution_axioms_def prob_kernel_def'[symmetric] prob_kernel_def prob_kernel_axioms_def measure_kernel_def)
  thus ?thesis
    using assms that by(fastforce simp: monadP_qbs_Mx)
qed

lemma qbs_l_monadP_le1:"s \<in> qbs_space (monadP_qbs X) \<Longrightarrow> qbs_l s A \<le> 1"
  by(auto simp: monadP_qbs_space intro!: prob_space.emeasure_le_1)

lemma qbs_l_inj_P: "inj_on qbs_l (qbs_space (monadP_qbs X))"
  by(auto intro!: inj_on_subset[OF qbs_l_inj] simp: monadP_qbs_def sub_qbs_space)

lemma qbs_l_measurable_prob[measurable]:"qbs_l \<in> qbs_to_measure (monadP_qbs X) \<rightarrow>\<^sub>M prob_algebra (qbs_to_measure X)"
proof(rule qbs_morphism_dest[OF qbs_morphismI])
  fix \<gamma>
  assume "\<gamma> \<in> qbs_Mx (monadP_qbs X)"
  from rep_qbs_Mx_monadP[OF this] obtain \<alpha> k where h[measurable]:
   "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "k \<in> borel \<rightarrow>\<^sub>M prob_algebra borel" "\<And>r. qbs_prob X \<alpha> (k r)"
    by metis
  show "qbs_l \<circ> \<gamma> \<in> qbs_Mx (measure_to_qbs (prob_algebra (qbs_to_measure X)))"
    by(auto simp: qbs_Mx_R comp_def h(1) qbs_s_finite.qbs_l[OF qbs_prob.qbs_s_finite[OF h(4)]])
qed

lemma return_qbs_morphismP: "return_qbs X \<in> X \<rightarrow>\<^sub>Q monadP_qbs X"
proof(rule qbs_morphismI)
  interpret rr : real_distribution "return borel 0"
    by(simp add: real_distribution_def real_distribution_axioms_def prob_space_return)
  fix \<alpha>
  assume h:"\<alpha> \<in> qbs_Mx X"
  then have 1:"return_qbs X \<circ> \<alpha> = (\<lambda>r. \<lbrakk>X, \<alpha>, return borel r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    by(rule return_qbs_comp)
  show "return_qbs X \<circ> \<alpha> \<in> qbs_Mx (monadP_qbs X)"
    by(auto simp: 1 monadP_qbs_Mx h intro!: exI[where x=\<alpha>] exI[where x="return borel"])
qed

lemma(in qbs_prob)
  assumes "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
          "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
          "\<beta> \<in> qbs_Mx Y"
      and g[measurable]:"g \<in> borel \<rightarrow>\<^sub>M prob_algebra borel"
      and "(f \<circ> \<alpha>) = (\<lambda>r. \<lbrakk>Y, \<beta>, g r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    shows bind_qbs_prob:"qbs_prob Y \<beta> (\<mu> \<bind> g)"
      and bind_qbs': "s \<bind> f = \<lbrakk>Y, \<beta>, \<mu> \<bind> g\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
proof -
  interpret prob_kernel borel borel g
    using assms(4) by(simp add: prob_kernel_def')
  have "prob_space (\<mu> \<bind> g)"
    by(auto intro!: prob_space_bind'[OF _ g] simp: space_prob_algebra prob_space_axioms)
  thus "qbs_prob Y \<beta> (\<mu> \<bind> g)" "s \<bind> f = \<lbrakk>Y, \<beta>, \<mu> \<bind> g\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using qbs_s_finite.qbs_probI[OF bind_qbs_s_finite[OF assms(1) qbs_morphism_monadPD[OF assms(2)] assms(3) s_finite_kernel_axioms assms(5)]]
    by(simp_all add: bind_qbs[OF assms(1) qbs_morphism_monadPD[OF assms(2)] assms(3) s_finite_kernel_axioms assms(5)] bind_kernel_bind[of g \<mu> borel])
qed

lemma bind_qbs_morphism'P:
  assumes "f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  shows "(\<lambda>x. x \<bind> f) \<in> monadP_qbs X \<rightarrow>\<^sub>Q monadP_qbs Y"
proof(safe intro!: qbs_morphism_monadPI')
  fix x
  assume "x \<in> qbs_space (monadP_qbs X)"
  from rep_qbs_space_monadP[OF this] obtain \<alpha> \<mu> where h:"x = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_prob X \<alpha> \<mu>"
    by metis
  then interpret qbs_prob X \<alpha> \<mu> by simp
  from rep_qbs_Mx_monadP[OF qbs_morphism_Mx[OF assms in_Mx]] obtain \<beta> g where h'[measurable]:
  "f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, g r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx Y" "g \<in> borel \<rightarrow>\<^sub>M prob_algebra borel" by metis
  show "x \<bind> f \<in> qbs_space (monadP_qbs Y)"
    using sets_bind[of \<mu> g] measurable_space[OF h'(3),simplified space_prob_algebra]
    by(auto simp: qbs_prob.bind_qbs'[OF h(2,1) assms h'(2,3,1)] qbs_prob_def in_Mx_def h'(2) real_distribution_def real_distribution_axioms_def intro!: qbs_prob.in_space_monadP prob_space_bind[where S=borel] measurable_prob_algebraD)
qed(auto intro!: qbs_morphism_monadPD' bind_qbs_morphism'[OF qbs_morphism_monadPD[OF assms]])

lemma distr_qbs_morphismP':
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows "distr_qbs X Y f \<in> monadP_qbs X \<rightarrow>\<^sub>Q monadP_qbs Y"
  unfolding distr_qbs_def
  by(rule bind_qbs_morphism'P[OF qbs_morphism_comp[OF assms return_qbs_morphismP]])

lemma join_qbs_morphismP: "join_qbs \<in> monadP_qbs (monadP_qbs X) \<rightarrow>\<^sub>Q monadP_qbs X"
  by(simp add: join_qbs_def bind_qbs_morphism'P[OF qbs_morphism_ident])

lemma
  assumes "qbs_prob (monadP_qbs X) \<beta> \<mu>"
          "ssx = \<lbrakk>monadP_qbs X, \<beta>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
          "\<alpha> \<in> qbs_Mx X"
          "g \<in> borel \<rightarrow>\<^sub>M prob_algebra borel"
      and "\<beta> =(\<lambda>r. \<lbrakk>X, \<alpha>, g r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    shows qbs_prob_join_qbs_s_finite: "qbs_prob X \<alpha> (\<mu> \<bind> g)"
      and qbs_prob_join_qbs: "join_qbs ssx = \<lbrakk>X, \<alpha>, \<mu> \<bind> g\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  using qbs_prob.bind_qbs'[OF assms(1,2) qbs_morphism_ident assms(3,4)] qbs_prob.bind_qbs_prob[OF assms(1,2) qbs_morphism_ident assms(3,4)]
  by(auto simp: assms(5) join_qbs_def)

context
begin

interpretation rr : standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(auto intro!: pair_standard_borel_ne)

lemma strength_qbs_ab_r_prob:
  assumes "\<alpha> \<in> qbs_Mx X"
          "\<beta> \<in> qbs_Mx (monadP_qbs Y)"
          "\<gamma> \<in> qbs_Mx Y"
      and [measurable]:"g \<in> borel \<rightarrow>\<^sub>M prob_algebra borel"
      and "\<beta> = (\<lambda>r. \<lbrakk>Y, \<gamma>, g r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    shows "qbs_prob (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<gamma> \<circ> rr.from_real) (distr (return borel r \<Otimes>\<^sub>M g r) borel rr.to_real)"
  using measurable_space[OF assms(4),of r] sets_return[of borel r]
  by(auto intro!: qbs_s_finite.qbs_probI strength_qbs_ab_r_s_finite[OF assms(1) qbs_Mx_monadPM[OF assms(2)] assms(3) prob_kernel.s_finite_kernel_prob_kernel assms(5),simplified prob_kernel_def',OF assms(4)] prob_space.prob_space_distr prob_space_pair prob_space_return simp: space_prob_algebra simp del: sets_return)

lemma strength_qbs_morphismP: "strength_qbs X Y \<in> X \<Otimes>\<^sub>Q monadP_qbs Y \<rightarrow>\<^sub>Q monadP_qbs (X \<Otimes>\<^sub>Q Y)"
proof(rule pair_qbs_morphismI)
  fix \<alpha> \<beta>
  assume h:"\<alpha> \<in> qbs_Mx X"
           "\<beta> \<in> qbs_Mx (monadP_qbs Y)"
  from rep_qbs_Mx_monadP[OF this(2)] obtain \<gamma> g where hb[measurable]:
   "\<beta> = (\<lambda>r. \<lbrakk>Y, \<gamma>, g r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<gamma> \<in> qbs_Mx Y" "g \<in> borel \<rightarrow>\<^sub>M prob_algebra borel"
    by metis
  show "(\<lambda>r. strength_qbs X Y (\<alpha> r, \<beta> r)) \<in> qbs_Mx (monadP_qbs (X \<Otimes>\<^sub>Q Y))"
    using strength_qbs_ab_r_prob[OF h hb(2,3,1)] strength_qbs_ab_r[OF h(1) qbs_Mx_monadPM[OF h(2)] hb(2) prob_kernel.s_finite_kernel_prob_kernel hb(1),simplified prob_kernel_def',OF hb(3)]
    by(auto simp: monadP_qbs_Mx qbs_prob_def in_Mx_def intro!: exI[where x="map_prod \<alpha> \<gamma> \<circ> rr.from_real"] exI[where x="\<lambda>r. distr (return borel r \<Otimes>\<^sub>M g r) borel rr.to_real"])
qed

end

lemma bind_qbs_morphismP: "(\<bind>) \<in> monadP_qbs X \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q monadP_qbs Y) \<Rightarrow>\<^sub>Q monadP_qbs Y"
proof -
  {
    fix f s
    assume h:"f \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y" "s \<in> qbs_space (monadP_qbs X)"
    from rep_qbs_space_monadP[OF this(2)] obtain \<alpha> \<mu> where h':
     "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_prob X \<alpha> \<mu>" by metis
    then interpret qbs_prob X \<alpha> \<mu> by simp
    from rep_qbs_Mx_monadP[OF qbs_morphism_Mx[OF h(1) in_Mx]] obtain \<beta> g
      where hb[measurable]:"f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, g r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx Y" "g \<in> borel \<rightarrow>\<^sub>M prob_algebra borel" by metis
    have "join_qbs (distr_qbs ((X \<Rightarrow>\<^sub>Q monadP_qbs Y) \<Otimes>\<^sub>Q X) (monadP_qbs Y) (\<lambda>fx. fst fx (snd fx)) (strength_qbs (X \<Rightarrow>\<^sub>Q monadP_qbs Y) X (f, s))) = s \<bind> f"
      using qbs_prob_join_qbs[OF qbs_prob.distr_qbs_prob[OF strength_qbs_prob[of f "X \<Rightarrow>\<^sub>Q monadP_qbs Y",OF h(1) h'(1)] strength_qbs[of f "X \<Rightarrow>\<^sub>Q monadP_qbs Y",OF h(1) h'(1)] qbs_morphism_eval] qbs_s_finite.distr_qbs[OF strength_qbs_s_finite[of f "X \<Rightarrow>\<^sub>Q monadP_qbs Y",OF h(1) h'(1)] strength_qbs[of f "X \<Rightarrow>\<^sub>Q monadP_qbs Y",OF h(1) h'(1)] qbs_morphism_eval] hb(2,3)] hb(1)
      by(simp add: bind_qbs[OF h'(1)  qbs_morphism_monadPD[OF h(1)] hb(2) prob_kernel.s_finite_kernel_prob_kernel hb(1),simplified prob_kernel_def',OF hb(3)] comp_def bind_kernel_bind[of g \<mu> borel,OF measurable_prob_algebraD])
  }
  thus ?thesis
    by(auto intro!: arg_swap_morphism[OF curry_preserves_morphisms [OF qbs_morphism_cong'[of _ "join_qbs \<circ> (distr_qbs (exp_qbs X (monadP_qbs Y) \<Otimes>\<^sub>Q X) (monadP_qbs Y) (\<lambda>fx. (fst fx) (snd fx))) \<circ> (strength_qbs (exp_qbs X (monadP_qbs Y)) X)"]]] qbs_morphism_comp distr_qbs_morphismP' strength_qbs_morphismP join_qbs_morphismP qbs_morphism_eval simp: pair_qbs_space)
qed

corollary strength_qbs_law1P:
  assumes "x \<in> qbs_space (unit_quasi_borel \<Otimes>\<^sub>Q monadP_qbs X)"
  shows "snd x = (distr_qbs (unit_quasi_borel \<Otimes>\<^sub>Q X) X snd \<circ> strength_qbs unit_quasi_borel X) x"
  by(rule strength_qbs_law1, insert assms) (auto simp: pair_qbs_space qbs_space_monadPM)

corollary strength_qbs_law2P:
  assumes "x \<in> qbs_space ((X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q monadP_qbs Z)"
  shows "(strength_qbs X (Y \<Otimes>\<^sub>Q Z) \<circ> (map_prod id (strength_qbs Y Z)) \<circ> (\<lambda>((x,y),z). (x,(y,z)))) x =
         (distr_qbs ((X \<Otimes>\<^sub>Q Y) \<Otimes>\<^sub>Q Z) (X \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q Z)) (\<lambda>((x,y),z). (x,(y,z))) \<circ> strength_qbs (X \<Otimes>\<^sub>Q Y) Z) x"
  by(rule strength_qbs_law2, insert assms) (auto simp: pair_qbs_space qbs_space_monadPM)

lemma strength_qbs_law4P:
  assumes "x \<in> qbs_space (X \<Otimes>\<^sub>Q monadP_qbs (monadP_qbs Y))"
  shows "(strength_qbs X Y \<circ> map_prod id join_qbs) x = (join_qbs \<circ> distr_qbs (X \<Otimes>\<^sub>Q monadP_qbs Y) (monadP_qbs (X \<Otimes>\<^sub>Q Y)) (strength_qbs X Y) \<circ> strength_qbs X (monadP_qbs Y)) x"
        (is "?lhs = ?rhs")
proof -
  from assms rep_qbs_space_monadP[of "snd x" "monadP_qbs Y"] obtain \<beta> \<mu>
    where h:"qbs_prob (monadP_qbs Y) \<beta> \<mu>" "snd x = \<lbrakk>monadP_qbs Y, \<beta>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by (auto simp: pair_qbs_space) metis
  then interpret qp: qbs_prob "monadP_qbs Y" \<beta> \<mu> by simp
  from rep_qbs_Mx_monadP[OF qp.in_Mx] obtain \<gamma> g
    where h': "\<gamma> \<in> qbs_Mx Y" "g \<in> borel \<rightarrow>\<^sub>M prob_algebra borel" "\<beta> = (\<lambda>r. \<lbrakk>Y, \<gamma>, g r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
      and h'': "\<And>r. qbs_prob Y \<gamma> (g r)"
    by metis
  have "?lhs = \<lbrakk>X \<Otimes>\<^sub>Q Y, \<lambda>r. (fst x, \<gamma> r), \<mu> \<bind> g\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using qbs_s_finite.strength_qbs[OF qbs_prob.qbs_s_finite[OF qbs_prob_join_qbs_s_finite[OF h h']] _ qbs_prob_join_qbs[OF h h'],of "fst x" X] assms
    by (auto simp: pair_qbs_space)
  also have "... = ?rhs"
    using qbs_prob_join_qbs[OF qbs_prob.distr_qbs_prob[OF qp.strength_qbs_prob[OF _ h(2),of "fst x" X] qp.strength_qbs[OF _ h(2)] strength_qbs_morphismP] qbs_s_finite.distr_qbs[OF qp.strength_qbs_s_finite[OF _ h(2),of "fst x" X] qp.strength_qbs[OF _ h(2)] strength_qbs_morphismP] pair_qbs_MxI h'(2),of "\<lambda>r. (fst x, \<gamma> r)",simplified comp_def qbs_s_finite.strength_qbs[OF qbs_prob.qbs_s_finite[OF h''] _ fun_cong[OF h'(3)]]] assms
    by(auto simp: pair_qbs_space h')
  finally show ?thesis .
qed

lemma distr_qbs_morphismP: "distr_qbs X Y \<in> X \<Rightarrow>\<^sub>Q Y \<rightarrow>\<^sub>Q monadP_qbs X \<Rightarrow>\<^sub>Q monadP_qbs Y"
proof -
  note [qbs] = bind_qbs_morphismP return_qbs_morphismP
  have [simp]: "distr_qbs X Y = (\<lambda>f sx. sx \<bind> return_qbs Y \<circ> f)"
    by standard+ (auto simp: distr_qbs_def)
  show ?thesis
    by simp
qed

lemma bind_qbs_return_rotateP:
  assumes "p \<in> qbs_space (monadP_qbs X)"
      and "q \<in> qbs_space (monadP_qbs Y)"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y))) = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))"
  by(auto intro!: bind_qbs_return_rotate qbs_space_monadPM assms)

lemma qbs_bind_bind_return1P:
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadP_qbs Z"
          "p \<in> qbs_space (monadP_qbs X)"
          "q \<in> qbs_space (monadP_qbs Y)"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f (x,y))) = (q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> f"
  by(auto intro!: qbs_bind_bind_return1 assms qbs_space_monadPM qbs_morphism_monadPD)

corollary qbs_bind_bind_return1P':
  assumes [qbs]:"f \<in> qbs_space (X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q monadP_qbs Z)"
          "p \<in> qbs_space (monadP_qbs X)"
          "q \<in> qbs_space (monadP_qbs Y)"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f x y)) = (q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> (case_prod f)"
  by(auto intro!: qbs_bind_bind_return1P[where f="case_prod f" and Z=Z,simplified])

lemma qbs_bind_bind_return2P:
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadP_qbs Z"
          "p \<in> qbs_space (monadP_qbs X)" "q \<in> qbs_space (monadP_qbs Y)"
    shows "p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f (x,y))) = (p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> f"
  by(auto intro!: qbs_bind_bind_return2 assms qbs_space_monadPM qbs_morphism_monadPD)

corollary qbs_bind_bind_return2P':
  assumes [qbs]:"f \<in> qbs_space (X \<Rightarrow>\<^sub>Q Y \<Rightarrow>\<^sub>Q monadP_qbs Z)"
          "p \<in> qbs_space (monadP_qbs X)"
          "q \<in> qbs_space (monadP_qbs Y)"
    shows "p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f x y)) = (p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))) \<bind> (case_prod f)"
  by(auto intro!: qbs_bind_bind_return2P[where f="case_prod f" and Z=Z,simplified])

corollary bind_qbs_rotateP:
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadP_qbs Z"
          "p \<in> qbs_space (monadP_qbs X)"
      and "q \<in> qbs_space (monadP_qbs Y)"
    shows "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f (x,y))) = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f (x,y)))"
  by(auto intro!: bind_qbs_rotate assms qbs_space_monadPM qbs_morphism_monadPD)

context pair_qbs_probs
begin

interpretation rr : standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(auto intro!: pair_standard_borel_ne)

sublocale qbs_prob "X \<Otimes>\<^sub>Q Y" "map_prod \<alpha> \<beta> \<circ> rr.from_real" "distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real"
  by(auto simp: qbs_prob_def in_Mx_def real_distribution_def qbs_Mx_is_morphisms real_distribution_axioms_def pq1.prob_space_axioms pq2.prob_space_axioms intro!: prob_space.prob_space_distr prob_space_pair)

lemma  qbs_bind_bind_return_prob:
  assumes [qbs]:"f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  shows "qbs_prob Z (f \<circ> (map_prod \<alpha> \<beta> \<circ> rr.from_real)) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real)"
  using qbs_prob_axioms by(auto simp: qbs_prob_def in_Mx_def qbs_Mx_is_morphisms)

end

subsubsection \<open> Almost Everywhere \<close>
lift_definition qbs_almost_everywhere :: "['a qbs_measure, 'a \<Rightarrow> bool] \<Rightarrow> bool"
is "\<lambda>(X,\<alpha>,\<mu>). almost_everywhere (distr \<mu> (qbs_to_measure X) \<alpha>)"
  by(auto simp: qbs_s_finite_eq_def) metis

syntax
  "_qbs_almost_everywhere" :: "pttrn \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> bool" ("AE\<^sub>Q _ in _. _" [0,0,10] 10)

translations
  "AE\<^sub>Q x in p. P" \<rightleftharpoons> "CONST qbs_almost_everywhere p (\<lambda>x. P)"

lemma AEq_qbs_l: "(AE\<^sub>Q x in p. P x) = (AE x in qbs_l p. P x)"
  by transfer (simp add: case_prod_beta')

lemma(in qbs_s_finite) AEq_def:
 "(AE\<^sub>Q x in \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n . P x) = (AE x in (distr \<mu> (qbs_to_measure X) \<alpha>). P x)"
  by(simp add: qbs_almost_everywhere.abs_eq)

lemma(in qbs_s_finite) AEq_AE: "(AE\<^sub>Q x in \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n . P x) \<Longrightarrow> (AE x in \<mu>. P (\<alpha> x))"
  by(auto simp: AEq_def intro!:AE_distrD[of \<alpha>])

lemma(in qbs_s_finite) AEq_AE_iff:
  assumes [qbs]:"qbs_pred X P"
  shows "(AE\<^sub>Q x in \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n . P x) \<longleftrightarrow> (AE x in \<mu>. P (\<alpha> x))"
  by(auto simp: AEq_AE AEq_def qbs_pred_iff_sets intro!: AE_distr_iff[THEN iffD2])

lemma AEq_qbs_pred[qbs]: "qbs_almost_everywhere \<in> monadM_qbs X \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q qbs_count_space UNIV) \<Rightarrow>\<^sub>Q qbs_count_space UNIV"
proof(rule curry_preserves_morphisms[OF pair_qbs_morphismI])
  fix \<gamma> \<beta>
  assume h:"\<gamma> \<in> qbs_Mx (monadM_qbs X)"  "\<beta> \<in> qbs_Mx (X \<Rightarrow>\<^sub>Q qbs_count_space (UNIV :: bool set))"
  from rep_qbs_Mx_monadM[OF h(1)] obtain \<alpha> k where hk:
   "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<alpha> (k r)"
    by metis
  interpret s:standard_borel_ne "borel :: real measure" by simp
  interpret s2: standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure" by(simp add: borel_prod)
  have [measurable]:"Measurable.pred (borel \<Otimes>\<^sub>M borel) (\<lambda>(x, y). \<beta> x (\<alpha> y))"
    using h(2) hk(2) by(simp add: s2.qbs_pred_iff_measurable_pred[symmetric] r_preserves_product qbs_Mx_is_morphisms)
  show "(\<lambda>r. qbs_almost_everywhere (fst (\<gamma> r, \<beta> r)) (snd (\<gamma> r, \<beta> r))) \<in> qbs_Mx (qbs_count_space UNIV)"
    using h(2) hk(2) by(simp add: hk(1) qbs_Mx_is_morphisms qbs_s_finite.AEq_AE_iff[OF hk(4)])
    (auto simp add: s.qbs_pred_iff_measurable_pred intro!: s_finite_kernel.AE_pred[OF hk(3)])    
qed

lemma AEq_I2[simp]:
  assumes "p \<in> qbs_space (monadM_qbs X)" "\<And>x. x \<in> qbs_space X \<Longrightarrow> P x"
  shows "AE\<^sub>Q x in p. P x"
  by(auto simp: space_qbs_l_in[OF assms(1)] assms(2) AEq_qbs_l)

lemma AEq_mp[elim!]:
  assumes "AE\<^sub>Q x in s. P x" "AE\<^sub>Q x in s. P x \<longrightarrow> Q x"
  shows "AE\<^sub>Q x in s. Q x"
  using assms by(auto simp: AEq_qbs_l)

lemma
  shows AEq_iffI: "AE\<^sub>Q x in s. P x \<Longrightarrow> AE\<^sub>Q x in s. P x \<longleftrightarrow> Q x \<Longrightarrow> AE\<^sub>Q x in s. Q x"
    and AEq_disjI1: "AE\<^sub>Q x in s. P x \<Longrightarrow> AE\<^sub>Q x in s. P x \<or> Q x"
    and AEq_disjI2: "AE\<^sub>Q x in s. Q x \<Longrightarrow> AE\<^sub>Q x in s. P x \<or> Q x"
    and AEq_conjI: "AE\<^sub>Q x in s. P x \<Longrightarrow> AE\<^sub>Q x in s. Q x \<Longrightarrow> AE\<^sub>Q x in s. P x \<and> Q x"
    and AEq_conj_iff[simp]: "(AE\<^sub>Q x in s. P x \<and> Q x) \<longleftrightarrow> (AE\<^sub>Q x in s. P x) \<and> (AE\<^sub>Q x in s. Q x)"
  by(auto simp: AEq_qbs_l)

lemma AEq_symmetric:
  assumes "AE\<^sub>Q x in s. P x = Q x"
  shows "AE\<^sub>Q x in s. Q x = P x"
  using assms by(auto simp: AEq_qbs_l)

lemma AEq_impI: "(P \<Longrightarrow> AE\<^sub>Q x in M. Q x) \<Longrightarrow> AE\<^sub>Q x in M. P \<longrightarrow> Q x"
  by(auto simp: AEq_qbs_l AE_impI)

lemma AEq_Ball_mp:
  "s \<in> qbs_space (monadM_qbs X) \<Longrightarrow> (\<And>x. x\<in>qbs_space X \<Longrightarrow> P x) \<Longrightarrow> AE\<^sub>Q x in s. P x \<longrightarrow> Q x \<Longrightarrow> AE\<^sub>Q x in s. Q x"
  by auto

lemma AEq_cong:
  "s \<in> qbs_space (monadM_qbs X) \<Longrightarrow> (\<And>x. x \<in> qbs_space X \<Longrightarrow> P x \<longleftrightarrow> Q x) \<Longrightarrow> (AE\<^sub>Q x in s. P x) \<longleftrightarrow> (AE\<^sub>Q x in s. Q x)"
  by auto

lemma AEq_cong_simp: "s \<in> qbs_space (monadM_qbs X) \<Longrightarrow> (\<And>x. x \<in> qbs_space X =simp=> P x = Q x) \<Longrightarrow> (AE\<^sub>Q x in s. P x) \<longleftrightarrow> (AE\<^sub>Q x in s. Q x)"
  by (auto simp: simp_implies_def)

lemma AEq_all_countable: "(AE\<^sub>Q x in s. \<forall>i. P i x) \<longleftrightarrow> (\<forall>i::'i::countable. AE\<^sub>Q x in s. P i x)"
  by(simp add: AEq_qbs_l AE_all_countable)

lemma AEq_ball_countable: "countable X \<Longrightarrow> (AE\<^sub>Q x in s. \<forall>y\<in>X. P x y) \<longleftrightarrow> (\<forall>y\<in>X. AE\<^sub>Q x in s. P x y)"
  by(simp add: AEq_qbs_l AE_ball_countable)

lemma AEq_ball_countable': "(\<And>N. N \<in> I \<Longrightarrow> AE\<^sub>Q x in s. P N x) \<Longrightarrow> countable I \<Longrightarrow> AE\<^sub>Q x in s. \<forall>N \<in> I. P N x"
  unfolding AEq_ball_countable by simp

lemma AEq_pairwise: "countable F \<Longrightarrow> pairwise (\<lambda>A B. AE\<^sub>Q x in s. R x A B) F \<longleftrightarrow> (AE\<^sub>Q x in s. pairwise (R x) F)"
  unfolding pairwise_alt by (simp add: AEq_ball_countable)

lemma AEq_finite_all: "finite S \<Longrightarrow> (AE\<^sub>Q x in s. \<forall>i\<in>S. P i x) \<longleftrightarrow> (\<forall>i\<in>S. AE\<^sub>Q x in s. P i x)"
  by(simp add: AEq_qbs_l AE_finite_all)

lemma AE_finite_allI:"finite S \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> AE\<^sub>Q x in M. Q s x) \<Longrightarrow> AE\<^sub>Q x in M. \<forall>s\<in>S. Q s x"
  by(simp add: AEq_qbs_l AE_finite_all)

subsubsection \<open> Integral \<close>
lift_definition qbs_nn_integral :: "['a qbs_measure, 'a \<Rightarrow> ennreal] \<Rightarrow> ennreal"
is "\<lambda>(X,\<alpha>,\<mu>) f.(\<integral>\<^sup>+x. f x \<partial>distr \<mu> (qbs_to_measure X) \<alpha>)"
  by(auto simp: qbs_s_finite_eq_def)

lift_definition qbs_integral :: "['a qbs_measure, 'a \<Rightarrow> ('b :: {banach,second_countable_topology})] \<Rightarrow> 'b"
is "\<lambda>p f. if f \<in> (fst p) \<rightarrow>\<^sub>Q qbs_borel then (\<integral>x. f (fst (snd p) x) \<partial> (snd (snd p))) else 0"
  using qbs_s_finite_eq_dest(3) qbs_s_finite_eq_1_imp_2 by fastforce

syntax
  "_qbs_nn_integral" :: "pttrn \<Rightarrow> ennreal \<Rightarrow> 'a qbs_measure \<Rightarrow> ennreal" ("\<integral>\<^sup>+\<^sub>Q((2 _./ _)/ \<partial>_)" [60,61] 110)

translations
 "\<integral>\<^sup>+\<^sub>Q x. f \<partial>p" \<rightleftharpoons> "CONST qbs_nn_integral p (\<lambda>x. f)"

syntax
  "_qbs_integral" :: "pttrn \<Rightarrow> _ \<Rightarrow> 'a qbs_measure \<Rightarrow> _" ("\<integral>\<^sub>Q((2 _./ _)/ \<partial>_)" [60,61] 110)

translations
 "\<integral>\<^sub>Q x. f \<partial>p" \<rightleftharpoons> "CONST qbs_integral p (\<lambda>x. f)"

lemma(in qbs_s_finite)
  shows qbs_nn_integral_def: "f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) = (\<integral>\<^sup>+x. f (\<alpha> x) \<partial> \<mu>)"
    and qbs_nn_integral_def2:"(\<integral>\<^sup>+\<^sub>Q x. f x \<partial>\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) = (\<integral>\<^sup>+x. f x \<partial>(distr \<mu> (qbs_to_measure X) \<alpha>))"
  by(simp_all add: qbs_nn_integral.abs_eq nn_integral_distr lr_adjunction_correspondence)

lemma(in qbs_s_finite) qbs_integral_def:
 "f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> (\<integral>\<^sub>Q x. f x \<partial>\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) = (\<integral>x. f (\<alpha> x) \<partial> \<mu>)"
  by(simp add: qbs_integral.abs_eq)

lemma(in qbs_s_finite) qbs_integral_def2: "(\<integral>\<^sub>Q x. f x \<partial>\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) = (\<integral>x. f x \<partial>(distr \<mu> (qbs_to_measure X) \<alpha>))"
proof -
 consider "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" | "f \<notin> X \<rightarrow>\<^sub>Q qbs_borel" by auto
  thus ?thesis
  proof cases
    case h:2
    then have "\<not> integrable (qbs_l \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) f"
      by (metis borel_measurable_integrable measurable_distr_eq1 qbs_l qbs_morphism_measurable_intro)
    thus ?thesis
      using h by(simp add: qbs_l qbs_integral.abs_eq lr_adjunction_correspondence not_integrable_integral_eq)
  qed(simp add: qbs_integral.abs_eq lr_adjunction_correspondence integral_distr)
qed

lemma qbs_measure_eqI:
  assumes [qbs]:"p \<in> qbs_space (monadM_qbs X)" "q \<in> qbs_space (monadM_qbs X)"
      and "\<And>f. f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>p) = (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>q)"
    shows "p = q"
proof -
  obtain \<alpha> \<mu> \<beta> \<nu> where h:"p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "q = \<lbrakk>X, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" "qbs_s_finite X  \<beta> \<nu>"
    by (metis rep_qbs_space_monadM assms(1,2))
  then interpret pq:pair_qbs_s_finite X \<alpha> \<mu> \<beta> \<nu>
    by(auto simp: pair_qbs_s_finite_def)
  show ?thesis
    using assms(3) by(auto simp: h(1,2) pq.pq1.qbs_nn_integral_def pq.pq2.qbs_nn_integral_def intro!: pq.qbs_s_finite_measure_eq')
qed

lemma qbs_nn_integral_def2_l: "qbs_nn_integral s f = integral\<^sup>N (qbs_l s) f"
  by transfer auto

lemma qbs_integral_def2_l: "qbs_integral s f = integral\<^sup>L (qbs_l s) f"
  by (metis in_qbs_space_of qbs_s_finite.qbs_integral_def2 qbs_s_finite.qbs_l rep_qbs_space_monadM)

lift_definition qbs_integrable :: "'a qbs_measure \<Rightarrow> ('a \<Rightarrow> 'b::{second_countable_topology,banach}) \<Rightarrow> bool"
is "\<lambda>p f. f \<in> fst p \<rightarrow>\<^sub>Q qbs_borel \<and> integrable (snd (snd p)) (f \<circ> (fst (snd p)))"
proof safe
  have 0:"f \<in> Y \<rightarrow>\<^sub>Q qbs_borel" "integrable \<nu> (\<lambda>x. f (\<beta> x))" if "qbs_s_finite_eq (X,\<alpha>,\<mu>) (Y,\<beta>,\<nu>)" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "integrable \<mu> (\<lambda>x. f (\<alpha> x))" for X :: "'a quasi_borel" and  Y \<alpha> \<beta> \<mu> \<nu> and f :: "_ \<Rightarrow> 'b"
  proof -
    interpret pair_qbs_s_finite X \<alpha> \<mu> \<beta> \<nu>
      using qbs_s_finite_eq_dest[OF that(1)] by(auto simp: pair_qbs_s_finite_def)
    show "f \<in> Y \<rightarrow>\<^sub>Q qbs_borel" "integrable \<nu> (\<lambda>x. f (\<beta> x))"
      using that qbs_s_finite_eq_dest(3)[OF that(1)] by(simp_all add: integrable_distr_eq[symmetric,of \<alpha> \<mu> "qbs_to_measure X" f] integrable_distr_eq[symmetric,of \<beta> \<nu> "qbs_to_measure X" f] lr_adjunction_correspondence qbs_s_finite_eq_dest(4)[OF that(1)])
  qed
  {
    fix X Y :: "'a quasi_borel"
    fix \<alpha> \<beta> \<mu> \<nu> and f :: "_ \<Rightarrow> 'b"
    assume 1:"qbs_s_finite_eq (X, \<alpha>, \<mu>) (Y, \<beta>, \<nu>)"
    then have 2:"qbs_s_finite_eq (Y, \<beta>, \<nu>) (X, \<alpha>, \<mu>)" by(auto simp: qbs_s_finite_eq_def)
    have "f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<and> integrable \<mu> (f \<circ> \<alpha>) \<longleftrightarrow> f \<in> Y \<rightarrow>\<^sub>Q qbs_borel \<and> integrable \<nu> (f \<circ> \<beta>)"
      unfolding comp_def using 0[OF 1,of f] 0[OF 2,of f] by blast
  }
  thus "\<And>prod1 prod2 :: 'a qbs_s_finite_t. qbs_s_finite_eq prod1 prod2 \<Longrightarrow> (\<lambda>f:: _ \<Rightarrow> 'b. f \<in> fst prod1 \<rightarrow>\<^sub>Q borel\<^sub>Q \<and> integrable (snd (snd prod1)) (f \<circ> fst (snd prod1))) = (\<lambda>f. f \<in> fst prod2 \<rightarrow>\<^sub>Q borel\<^sub>Q \<and> integrable (snd (snd prod2)) (f \<circ> fst (snd prod2)))"
    by fastforce
qed

lemma(in qbs_s_finite) qbs_integrable_def:
 "qbs_integrable \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n f \<longleftrightarrow> f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<and> integrable \<mu> (\<lambda>x. f (\<alpha> x))"
  by(simp add: qbs_integrable.abs_eq comp_def)

lemma qbs_integrable_morphism_dest:
  assumes "s \<in> qbs_space (monadM_qbs X)"
      and "qbs_integrable s f"
    shows "f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  by (metis assms qbs_s_finite.qbs_integrable_def rep_qbs_space_monadM)

lemma qbs_integrable_morphismP:
  assumes "s \<in> qbs_space (monadP_qbs X)"
      and "qbs_integrable s f"
    shows "f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  by(auto intro!: qbs_integrable_morphism_dest assms qbs_space_monadPM)

lemma(in qbs_s_finite) qbs_integrable_measurable[simp]:
  assumes "qbs_integrable \<lbrakk>X,\<alpha>,\<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n f"
  shows "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M borel"
  by(auto intro!: qbs_integrable_morphism_dest assms simp: lr_adjunction_correspondence[symmetric])

lemma qbs_integrable_iff_integrable:
  "(qbs_integrable (s::'a qbs_measure) (f :: 'a \<Rightarrow> 'b::{second_countable_topology,banach})) = (integrable (qbs_l s) f)"
proof transfer
  fix f ::" 'a \<Rightarrow> 'b::{second_countable_topology,banach}"
  show "qbs_s_finite_eq s s \<Longrightarrow> (f \<in> fst s \<rightarrow>\<^sub>Q borel\<^sub>Q \<and> integrable (snd (snd s)) (f \<circ> fst (snd s))) = integrable (distr (snd (snd s)) (qbs_to_measure (fst s)) (fst (snd s))) f" for s
  proof(rule prod_cases3[of s])
    fix X :: "'a quasi_borel"
    fix \<alpha> \<mu>
    assume "qbs_s_finite_eq s s" and s: "s = (X,\<alpha>,\<mu>)"
    then interpret qbs_s_finite X \<alpha> \<mu> by(simp add: qbs_s_finite_eq_def)
    show "f \<in> fst s \<rightarrow>\<^sub>Q qbs_borel \<and> integrable (snd (snd s)) (\<lambda>x. (f \<circ> fst (snd s)) x) \<longleftrightarrow> integrable (distr (snd (snd s)) (qbs_to_measure (fst s)) (fst (snd s))) f"
      using integrable_distr_eq[of \<alpha> \<mu> "qbs_to_measure X" f,simplified]
      by(auto simp add: lr_adjunction_correspondence s)
  qed
qed

corollary(in qbs_s_finite) qbs_integrable_distr: "qbs_integrable \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n f = integrable (distr \<mu> (qbs_to_measure X) \<alpha>) f"
  by(simp add: qbs_integrable_iff_integrable qbs_l)

lemma qbs_integrable_morphism[qbs]: "qbs_integrable \<in> monadM_qbs X \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q (qbs_borel :: ('a :: {banach, second_countable_topology}) quasi_borel)) \<Rightarrow>\<^sub>Q qbs_count_space UNIV"
proof(rule curry_preserves_morphisms[OF pair_qbs_morphismI])
  fix \<gamma> \<beta>
  assume h:"\<gamma> \<in> qbs_Mx (monadM_qbs X)" "\<beta> \<in> qbs_Mx (X \<Rightarrow>\<^sub>Q (qbs_borel :: 'a quasi_borel))"
  from rep_qbs_Mx_monadM[OF this(1)] obtain \<alpha> k
    where hk:"\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<alpha> (k r)"
    by metis
  then interpret ina: in_Mx X \<alpha> by (simp add: in_Mx_def)
  interpret standard_borel_ne "borel :: real measure" by simp
  have [measurable]: "\<beta> r \<in> qbs_to_measure X \<rightarrow>\<^sub>M borel" for r
    using h(2) by(simp add: qbs_Mx_is_morphisms lr_adjunction_correspondence[symmetric])
  have [measurable_cong]: "sets (k r) = sets borel" for r
    using hk(4) qbs_s_finite.mu_sets by blast
  have 1: "borel_measurable (borel \<Otimes>\<^sub>M borel) = (qbs_borel \<Otimes>\<^sub>Q qbs_borel \<rightarrow>\<^sub>Q qbs_borel :: (real \<times> real \<Rightarrow> 'a) set)"
    by (metis borel_prod pair_standard_borel qbs_borel_prod standard_borel.standard_borel_r_full_faithful standard_borel_axioms)
  show "(\<lambda>r. qbs_integrable (fst (\<gamma> r, \<beta> r)) (snd (\<gamma> r, \<beta> r))) \<in> qbs_Mx (qbs_count_space UNIV)"
    by(auto simp: fun_cong[OF hk(1)] qbs_s_finite.qbs_integrable_distr[OF hk(4)] integrable_distr_eq qbs_Mx_is_morphisms qbs_pred_iff_measurable_pred  intro!: s_finite_kernel.integrable_measurable_pred[OF hk(3)]) (insert h(2), simp add: 1 qbs_Mx_is_morphisms split_beta')
qed

lemma(in qbs_s_finite) qbs_integrable_iff_integrable:
  assumes "f \<in> qbs_to_measure X \<rightarrow>\<^sub>M borel"
  shows "qbs_integrable \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n f = integrable \<mu> (\<lambda>x. f (\<alpha> x))"
  by(auto intro!: integrable_distr_eq[of \<alpha> \<mu> "qbs_to_measure X" f] simp: assms qbs_integrable_distr)

lemma qbs_integrable_iff_bounded:
  assumes "s \<in> qbs_space (monadM_qbs X)"
  shows "qbs_integrable s f \<longleftrightarrow> f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<and> (\<integral>\<^sup>+\<^sub>Q x. ennreal (norm (f x)) \<partial>s) < \<infinity>"
        (is "?lhs = ?rhs")
proof -
  from rep_qbs_space_monadM[OF assms] obtain \<alpha> \<mu> where hs:
   "qbs_s_finite X \<alpha> \<mu>" "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by metis
  then interpret qs:qbs_s_finite X \<alpha> \<mu> by simp
  have "?lhs = integrable (distr \<mu> (qbs_to_measure X) \<alpha>) f"
    by (simp add: hs(2) qbs_integrable_iff_integrable qs.qbs_l)
  also have "... = (f \<in> borel_measurable (distr \<mu> (qbs_to_measure X) \<alpha>) \<and> ((\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>(distr \<mu> (qbs_to_measure X) \<alpha>)) < \<infinity>))"
    by(rule integrable_iff_bounded)
  also have "... = ?rhs"
    by(auto simp add: hs(2) qs.qbs_nn_integral_def2 lr_adjunction_correspondence)
  finally show ?thesis .
qed

lemma not_qbs_integrable_qbs_integral: "\<not> qbs_integrable s f \<Longrightarrow> qbs_integral s f = 0"
  by(simp add: qbs_integral_def2_l qbs_integrable_iff_integrable not_integrable_integral_eq)

lemma qbs_integrable_cong_AE:
  assumes "s \<in> qbs_space (monadM_qbs X)"
          "AE\<^sub>Q x in s. f x = g x"
      and "qbs_integrable s f" "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
    shows "qbs_integrable s g"
  using assms(2,4) by(auto intro!: qbs_integrable_iff_integrable[THEN iffD2] Bochner_Integration.integrable_cong_AE[of g _ f,THEN iffD2] qbs_integrable_iff_integrable[THEN iffD1,OF assms(3)] qbs_integrable_morphism_dest[OF assms(1),of f] simp:  AEq_qbs_l measurable_qbs_l[OF assms(1)])

lemma qbs_integrable_cong:
  assumes "s \<in> qbs_space (monadM_qbs X)"
          "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
      and "qbs_integrable s f"
    shows "qbs_integrable s g"
  by(auto intro!: qbs_integrable_iff_integrable[THEN iffD2] Bochner_Integration.integrable_cong[OF refl,of _ g f,THEN iffD2] qbs_integrable_iff_integrable[THEN iffD1,OF assms(3)] simp: space_qbs_l_in[OF assms(1)] assms(2))

lemma qbs_integrable_zero[simp, intro]: "qbs_integrable s (\<lambda>x. 0)"
  by(simp add: qbs_integrable_iff_integrable)

lemma qbs_integrable_const:
  assumes "s \<in> qbs_space (monadP_qbs X)"
  shows "qbs_integrable s (\<lambda>x. c)"
  using assms by(auto intro!: qbs_integrable_iff_integrable[THEN iffD2] finite_measure.integrable_const simp: monadP_qbs_space prob_space_def)

lemma qbs_integrable_add[simp,intro!]:
  assumes "qbs_integrable s f"
      and "qbs_integrable s g"
    shows "qbs_integrable s (\<lambda>x. f x + g x)"
  by(rule qbs_integrable_iff_integrable[THEN iffD2,OF Bochner_Integration.integrable_add[OF qbs_integrable_iff_integrable[THEN iffD1,OF assms(1)] qbs_integrable_iff_integrable[THEN iffD1,OF assms(2)]]])

lemma qbs_integrable_diff[simp,intro!]:
  assumes "qbs_integrable s f"
      and "qbs_integrable s g"
    shows "qbs_integrable s (\<lambda>x. f x - g x)"
  by(rule qbs_integrable_iff_integrable[THEN iffD2,OF Bochner_Integration.integrable_diff[OF qbs_integrable_iff_integrable[THEN iffD1,OF assms(1)] qbs_integrable_iff_integrable[THEN iffD1,OF assms(2)]]])

lemma qbs_integrable_sum[simp, intro!]: "(\<And>i. i \<in> I \<Longrightarrow> qbs_integrable s (f i)) \<Longrightarrow> qbs_integrable s (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by(simp add: qbs_integrable_iff_integrable)

lemma qbs_integrable_scaleR_left[simp, intro!]: "qbs_integrable s f \<Longrightarrow> qbs_integrable s (\<lambda>x. f x *\<^sub>R (c :: 'a :: {second_countable_topology,banach}))"
  by(simp add: qbs_integrable_iff_integrable)

lemma qbs_integrable_scaleR_right[simp, intro!]: "qbs_integrable s f \<Longrightarrow> qbs_integrable s (\<lambda>x. c *\<^sub>R (f x :: 'a :: {second_countable_topology,banach}) )"
  by(simp add: qbs_integrable_iff_integrable)

lemma qbs_integrable_mult_iff:
  fixes f :: "'a \<Rightarrow> real"
  shows "(qbs_integrable s (\<lambda>x. c * f x)) = (c = 0 \<or> qbs_integrable s f)"
  using qbs_integrable_iff_integrable[of s "\<lambda>x. c * f x"] integrable_mult_left_iff[of _ c f] qbs_integrable_iff_integrable[of s f] 
  by simp

lemma
  fixes c :: "_::{real_normed_algebra,second_countable_topology}"
  assumes "qbs_integrable s f"
  shows qbs_integrable_mult_right:"qbs_integrable s (\<lambda>x. c * f x)"
    and qbs_integrable_mult_left: "qbs_integrable s (\<lambda>x. f x * c)"
  using assms by(auto simp: qbs_integrable_iff_integrable)

lemma qbs_integrable_divide_zero[simp, intro!]:
  fixes c :: "_::{real_normed_field, field, second_countable_topology}"
  shows "qbs_integrable s f \<Longrightarrow> qbs_integrable s (\<lambda>x. f x / c)"
  by(simp add: qbs_integrable_iff_integrable)

lemma qbs_integrable_inner_left[simp, intro!]:
  "qbs_integrable s f \<Longrightarrow> qbs_integrable s (\<lambda>x. f x \<bullet> c)"
  by(simp add: qbs_integrable_iff_integrable)

lemma qbs_integrable_inner_right[simp, intro!]:
  "qbs_integrable s f \<Longrightarrow> qbs_integrable s (\<lambda>x. c \<bullet> f x)"
  by(simp add: qbs_integrable_iff_integrable)

lemma qbs_integrable_minus[simp, intro!]:
 "qbs_integrable s f \<Longrightarrow> qbs_integrable s (\<lambda>x. - f x)"
  by(simp add: qbs_integrable_iff_integrable)

lemma [simp, intro]:
  assumes "qbs_integrable s f"
  shows qbs_integrable_Re: "qbs_integrable s (\<lambda>x. Re (f x))"
    and qbs_integrable_Im: "qbs_integrable s (\<lambda>x. Im (f x))"
    and qbs_integrable_cnj: "qbs_integrable s (\<lambda>x. cnj (f x))"
  using assms by(simp_all add: qbs_integrable_iff_integrable)

lemma qbs_integrable_of_real[simp, intro!]:
 "qbs_integrable s f \<Longrightarrow> qbs_integrable s (\<lambda>x. of_real (f x))"
  by(simp_all add: qbs_integrable_iff_integrable)

lemma [simp, intro]:
  assumes "qbs_integrable s f"
  shows qbs_integrable_fst: "qbs_integrable s (\<lambda>x. fst (f x))"
    and qbs_integrable_snd: "qbs_integrable s (\<lambda>x. snd (f x))"
  using assms by(simp_all add: qbs_integrable_iff_integrable)

lemma qbs_integrable_norm:
  assumes "qbs_integrable s f"
  shows "qbs_integrable s (\<lambda>x. norm (f x))"
  by(rule qbs_integrable_iff_integrable[THEN iffD2,OF integrable_norm[OF qbs_integrable_iff_integrable[THEN iffD1,OF assms]]])

lemma qbs_integrable_abs:
  fixes f :: "_ \<Rightarrow> real"
  assumes "qbs_integrable s f"
  shows "qbs_integrable s (\<lambda>x. \<bar>f x\<bar>)"
  by(rule qbs_integrable_iff_integrable[THEN iffD2,OF integrable_abs[OF qbs_integrable_iff_integrable[THEN iffD1,OF assms]]])

lemma qbs_integrable_sq:
  fixes c :: "_::{real_normed_field,second_countable_topology}"
  assumes "qbs_integrable s (\<lambda>x. c)" "qbs_integrable s f"
      and "qbs_integrable s (\<lambda>x. (f x)\<^sup>2)"
    shows "qbs_integrable s (\<lambda>x. (f x - c)\<^sup>2)"
  by(simp add: comm_ring_1_class.power2_diff,rule qbs_integrable_diff,rule qbs_integrable_add)
    (simp_all add: comm_semiring_1_class.semiring_normalization_rules(16)[of 2] assms qbs_integrable_mult_right power2_eq_square[of c])

lemma qbs_nn_integral_eq_integral_AEq:
  assumes "qbs_integrable s f" "AE\<^sub>Q x in s. 0 \<le> f x"
    shows "(\<integral>\<^sup>+\<^sub>Q x. ennreal (f x) \<partial>s) = ennreal (\<integral>\<^sub>Q x. f x \<partial>s)"
  using nn_integral_eq_integral[OF qbs_integrable_iff_integrable[THEN iffD1,OF assms(1)] ] qbs_integrable_morphism_dest[OF in_qbs_space_of assms(1)] assms(2)
  by(simp add: qbs_integral_def2_l qbs_nn_integral_def2_l AEq_qbs_l)

lemma qbs_nn_integral_eq_integral:
  assumes "s \<in> qbs_space (monadM_qbs X)" "qbs_integrable s f"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> 0 \<le> f x"
    shows "(\<integral>\<^sup>+\<^sub>Q x. ennreal (f x) \<partial>s) = ennreal (\<integral>\<^sub>Q x. f x \<partial>s)"
  using qbs_nn_integral_eq_integral_AEq[OF assms(2) AEq_I2[OF assms(1,3)]] by simp

lemma qbs_nn_integral_cong_AEq:
  assumes "s \<in> qbs_space (monadM_qbs X)" "AE\<^sub>Q x in s. f x = g x"
  shows "qbs_nn_integral s f = qbs_nn_integral s g"
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu>
    where hs: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" by metis
  then interpret qs: qbs_s_finite X \<alpha> \<mu> by simp
  show ?thesis
    using assms(2) by(auto simp: qs.qbs_nn_integral_def2 hs(1) qs.AEq_def intro!: nn_integral_cong_AE)
qed

lemma qbs_nn_integral_cong:
  assumes "s \<in> qbs_space (monadM_qbs X)" "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
  shows "qbs_nn_integral s f = qbs_nn_integral s g"
  using qbs_nn_integral_cong_AEq[OF assms(1) AEq_I2[OF assms]] by simp

lemma qbs_nn_integral_const:
 "(\<integral>\<^sup>+\<^sub>Q x. c \<partial>s) = c * qbs_l s (qbs_space (qbs_space_of s))"
  by(simp add: qbs_nn_integral_def2_l space_qbs_l)

lemma qbs_nn_integral_const_prob:
  assumes "s \<in> qbs_space (monadP_qbs X)"
  shows "(\<integral>\<^sup>+\<^sub>Q x. c \<partial>s) = c"
  using assms by(simp add: qbs_nn_integral_const prob_space.emeasure_space_1 qbs_l_prob_space space_qbs_l)

lemma qbs_nn_integral_add:
  assumes "s \<in> qbs_space (monadM_qbs X)"
      and [qbs]:"f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
    shows "(\<integral>\<^sup>+\<^sub>Q x. f x + g x \<partial>s) = (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>s) + (\<integral>\<^sup>+\<^sub>Q x. g x \<partial>s)"
  by(auto simp: qbs_nn_integral_def2_l measurable_qbs_l[OF assms(1)] intro!: nn_integral_add measurable_qbs_l)

lemma qbs_nn_integral_cmult:
  assumes "s \<in> qbs_space (monadM_qbs X)" and [qbs]:"f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<integral>\<^sup>+\<^sub>Q x. c * f x \<partial>s) = c * (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>s)"
  by(auto simp: qbs_nn_integral_def2_l measurable_qbs_l[OF assms(1)] intro!: nn_integral_cmult)

lemma qbs_integral_cong_AEq:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
      and "AE\<^sub>Q x in s. f x = g x"
    shows "qbs_integral s f = qbs_integral s g"
  using assms(4) by(auto simp: qbs_integral_def2_l AEq_qbs_l measurable_qbs_l[OF assms(1)] intro!: integral_cong_AE )

lemma qbs_integral_cong:
  assumes "s \<in> qbs_space (monadM_qbs X)" "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
  shows "qbs_integral s f = qbs_integral s g"
  by(auto simp: qbs_integral_def2_l space_qbs_l_in[OF assms(1)] assms(2) intro!: Bochner_Integration.integral_cong)

lemma qbs_integral_nonneg_AEq:
  fixes f :: "_ \<Rightarrow> real"
  shows "AE\<^sub>Q x in s. 0 \<le> f x \<Longrightarrow> 0 \<le> qbs_integral s f"
  by(auto simp: qbs_integral_def2_l AEq_qbs_l intro!: integral_nonneg_AE )

lemma qbs_integral_nonneg:
  fixes f :: "_ \<Rightarrow> real"
  assumes "s \<in> qbs_space (monadM_qbs X)" "\<And>x. x \<in> qbs_space X \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> qbs_integral s f"
  by(auto simp: qbs_integral_def2_l space_qbs_l_in[OF assms(1)] assms(2) intro!: Bochner_Integration.integral_nonneg)

lemma qbs_integral_mono_AEq:
  fixes f :: "_ \<Rightarrow> real"
  assumes "qbs_integrable s f" "qbs_integrable s g" "AE\<^sub>Q x in s. f x \<le> g x"
    shows "qbs_integral s f \<le> qbs_integral s g"
  using assms by(auto simp: qbs_integral_def2_l AEq_qbs_l qbs_integrable_iff_integrable intro!: integral_mono_AE)

lemma qbs_integral_mono:
  fixes f :: "_ \<Rightarrow> real"
  assumes "s \<in> qbs_space (monadM_qbs X)"
      and "qbs_integrable s f" "qbs_integrable s g" "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x \<le> g x"
    shows "qbs_integral s f \<le> qbs_integral s g"
  by(auto simp: qbs_integral_def2_l space_qbs_l_in[OF assms(1)] qbs_integrable_iff_integrable[symmetric] assms intro!: integral_mono)

lemma qbs_integral_const_prob:
  assumes "s \<in> qbs_space (monadP_qbs X)"
  shows "(\<integral>\<^sub>Q x. c \<partial>s) = c"
  using assms by(simp add: qbs_integral_def2_l monadP_qbs_space prob_space.prob_space)

lemma
  assumes "qbs_integrable s f" "qbs_integrable s g"
  shows qbs_integral_add:"(\<integral>\<^sub>Q x. f x + g x \<partial>s) = (\<integral>\<^sub>Q x. f x \<partial>s) + (\<integral>\<^sub>Q x. g x \<partial>s)"
    and qbs_integral_diff: "(\<integral>\<^sub>Q x. f x - g x \<partial>s) = (\<integral>\<^sub>Q x. f x \<partial>s) - (\<integral>\<^sub>Q x. g x \<partial>s)"
  using assms by(auto simp: qbs_integral_def2_l qbs_integrable_iff_integrable[symmetric] intro!: Bochner_Integration.integral_add Bochner_Integration.integral_diff)

lemma [simp]:
  fixes c :: "_::{real_normed_field,second_countable_topology}"
  shows qbs_integral_mult_right_zero:"(\<integral>\<^sub>Q x. c * f x \<partial>s) = c * (\<integral>\<^sub>Q x. f x \<partial>s)"
    and qbs_integral_mult_left_zero:"(\<integral>\<^sub>Q x. f x * c \<partial>s) = (\<integral>\<^sub>Q x. f x \<partial>s) * c"
    and qbs_integral_divide_zero: "(\<integral>\<^sub>Q x. f x / c \<partial>s) = (\<integral>\<^sub>Q x. f x \<partial>s) / c"
   by(auto simp: qbs_integral_def2_l)

lemma qbs_integral_minus[simp]: "(\<integral>\<^sub>Q x. - f x \<partial>s) = - (\<integral>\<^sub>Q x. f x \<partial>s)"
   by(auto simp: qbs_integral_def2_l)

lemma [simp]:
  shows qbs_integral_scaleR_right:"(\<integral>\<^sub>Q x. c *\<^sub>R f x \<partial>s) = c *\<^sub>R (\<integral>\<^sub>Q x. f x \<partial>s)"
    and qbs_integral_scaleR_left: "(\<integral>\<^sub>Q x. f x *\<^sub>R c \<partial>s) = (\<integral>\<^sub>Q x. f x \<partial>s) *\<^sub>R c"
  by(auto simp: qbs_integral_def2_l)

lemma [simp]:
  shows qbs_integral_inner_left: "qbs_integrable s f \<Longrightarrow> (\<integral>\<^sub>Q x. f x \<bullet> c \<partial>s) = (\<integral>\<^sub>Q x. f x \<partial>s) \<bullet> c"
    and qbs_integral_inner_right: "qbs_integrable s f \<Longrightarrow>  (\<integral>\<^sub>Q x. c \<bullet> f x \<partial>s) = c \<bullet> (\<integral>\<^sub>Q x. f x \<partial>s) "
  by(auto simp: qbs_integral_def2_l qbs_integrable_iff_integrable)

lemma integral_complex_of_real[simp]: "(\<integral>\<^sub>Q x. complex_of_real (f x) \<partial>s)= of_real (\<integral>\<^sub>Q x. f x \<partial>s)"
  by(simp add: qbs_integral_def2_l)

lemma integral_cnj[simp]: "(\<integral>\<^sub>Q x. cnj (f x) \<partial>s) = cnj (\<integral>\<^sub>Q x. f x \<partial>s)"
  by(simp add: qbs_integral_def2_l)

lemma [simp]:
  assumes "qbs_integrable s f"
  shows qbs_integral_Im: "(\<integral>\<^sub>Q x. Im (f x) \<partial>s) = Im (\<integral>\<^sub>Q x. f x \<partial>s)"
    and qbs_integral_Re: "(\<integral>\<^sub>Q x. Re (f x) \<partial>s) = Re (\<integral>\<^sub>Q x. f x \<partial>s)"
  using assms by(auto simp: qbs_integral_def2_l qbs_integrable_iff_integrable)

lemma qbs_integral_of_real[simp]:"qbs_integrable s f \<Longrightarrow> (\<integral>\<^sub>Q x. of_real (f x) \<partial>s) = of_real (\<integral>\<^sub>Q x. f x \<partial>s)"
  by(auto simp: qbs_integral_def2_l qbs_integrable_iff_integrable)

lemma [simp]:
  assumes "qbs_integrable s f"
  shows qbs_integral_fst: "(\<integral>\<^sub>Q x. fst (f x) \<partial>s) = fst (\<integral>\<^sub>Q x. f x \<partial>s)"
    and qbs_integral_snd: "(\<integral>\<^sub>Q x. snd (f x) \<partial>s) = snd (\<integral>\<^sub>Q x. f x \<partial>s)"
  using assms by(auto simp: qbs_integral_def2_l qbs_integrable_iff_integrable)

lemma real_qbs_integral_def:
  assumes "qbs_integrable s f"
  shows "qbs_integral s f = enn2real (\<integral>\<^sup>+\<^sub>Q x. ennreal (f x) \<partial>s) - enn2real (\<integral>\<^sup>+\<^sub>Q x. ennreal (- f x) \<partial>s)"
  using qbs_integrable_morphism_dest[OF in_qbs_space_of assms] assms
  by(auto simp: qbs_integral_def2_l qbs_nn_integral_def2_l qbs_integrable_iff_integrable[symmetric] intro!: real_lebesgue_integral_def)

lemma Markov_inequality_qbs_prob:
 "qbs_integrable s f \<Longrightarrow> AE\<^sub>Q x in s. 0 \<le> f x \<Longrightarrow> 0 < c \<Longrightarrow> \<P>(x in qbs_l s. c \<le> f x) \<le> (\<integral>\<^sub>Q x. f x \<partial>s) / c"
  by(auto simp: qbs_integral_def2_l AEq_qbs_l qbs_integrable_iff_integrable intro!: integral_Markov_inequality_measure[where A="{}"])

lemma Chebyshev_inequality_qbs_prob:
  assumes "s \<in> qbs_space (monadP_qbs X)"
      and "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "qbs_integrable s (\<lambda>x. (f x)\<^sup>2)"
      and "0 < e"
    shows "\<P>(x in qbs_l s. e \<le> \<bar>f x - (\<integral>\<^sub>Q x. f x \<partial>s)\<bar>) \<le> (\<integral>\<^sub>Q x. (f x - (\<integral>\<^sub>Q x. f x \<partial>s))\<^sup>2 \<partial>s) / e\<^sup>2"
  using prob_space.Chebyshev_inequality[OF qbs_l_prob_space[OF assms(1)] _ _ assms(4),of f] assms(2,3)
  by(simp add: qbs_integral_def2_l qbs_integrable_iff_integrable lr_adjunction_correspondence measurable_qbs_l'[OF qbs_space_monadPM[OF assms(1)]])

lemma qbs_l_return_qbs:
  assumes "x \<in> qbs_space X"
  shows "qbs_l (return_qbs X x) = return (qbs_to_measure X) x"
proof -
  interpret qp: qbs_prob X "\<lambda>r. x" "return borel 0"
    by(auto simp: qbs_prob_def prob_space_return assms in_Mx_def real_distribution_def real_distribution_axioms_def)
  show ?thesis
    by(simp add: qp.return_qbs[OF assms] distr_return qp.qbs_l)
qed

lemma qbs_l_bind_qbs:
  assumes [qbs]: "s \<in> qbs_space (monadM_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
  shows "qbs_l (s \<bind> f) = qbs_l s \<bind>\<^sub>k qbs_l \<circ> f" (is "?lhs = ?rhs")
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu>
    where hs: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" by metis
  then interpret qs: qbs_s_finite X \<alpha> \<mu> by simp
  from rep_qbs_Mx_monadM[OF qbs_morphism_Mx[OF assms(2) qs.in_Mx]] obtain \<beta> k where
   hk: "f \<circ> \<alpha> =  (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx Y" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite Y \<beta> (k r )"
    by metis
  then interpret sk: s_finite_kernel borel borel k by simp
  interpret im: in_Mx Y \<beta> using hk(2) by(simp add: in_Mx_def)

  have "?lhs = distr (\<mu> \<bind>\<^sub>k k) (qbs_to_measure Y) \<beta>"
    by(simp add: qs.bind_qbs[OF hs(1) assms(2) hk(2,3,1)] qbs_s_finite.qbs_l[OF qs.bind_qbs_s_finite[OF hs(1) assms(2) hk(2,3,1)]])
  also have "... = \<mu> \<bind>\<^sub>k (\<lambda>x. distr (k x) (qbs_to_measure Y) \<beta>)"
    by(auto intro!: sk.distr_bind_kernel simp: qs.mu_sets)
  also have "... = \<mu> \<bind>\<^sub>k (\<lambda>r. qbs_l ((f \<circ> \<alpha>) r))"
    by(simp add: qbs_s_finite.qbs_l[OF hk(4)] hk(1))
  also have "... = \<mu> \<bind>\<^sub>k (\<lambda>r. (\<lambda>x. qbs_l (f x)) (\<alpha> r))" by simp
  also have "... = distr \<mu> (qbs_to_measure X) \<alpha> \<bind>\<^sub>k (\<lambda>x. qbs_l (f x))"
    using l_preserves_morphisms[of X "monadM_qbs Y"] assms(2)
    by(auto intro!: measure_kernel.bind_kernel_distr[OF measure_kernel.measure_kernel_comp[OF qbs_l_measure_kernel],symmetric] simp: sets_eq_imp_space_eq[OF qs.mu_sets])
  also have "... = ?rhs"
    by(simp add: hs(1) qs.qbs_l comp_def)
  finally show ?thesis .
qed

lemma qbs_integrable_return[simp, intro]:
  assumes "x \<in> qbs_space X" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "qbs_integrable (return_qbs X x) f"
  using assms by(auto simp: qbs_integrable_iff_integrable qbs_l_return_qbs[OF assms(1)] lr_adjunction_correspondence nn_integral_return space_L intro!: integrableI_bounded)

lemma qbs_integrable_bind_return:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs X)" "f \<in> Y \<rightarrow>\<^sub>Q qbs_borel" "g \<in> X \<rightarrow>\<^sub>Q Y"
  shows "qbs_integrable (s \<bind> (\<lambda>x. return_qbs Y (g x))) f = qbs_integrable s (f \<circ> g)" (is "?lhs = ?rhs")
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu>
    where hs: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" by metis
  then interpret qs: qbs_s_finite X \<alpha> \<mu> by simp

  have 1:"return_qbs Y \<circ> (g \<circ> \<alpha>) = (\<lambda>r. \<lbrakk>Y, g \<circ> \<alpha>, return borel r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
    by(auto intro!: return_qbs_comp qbs_morphism_Mx[OF assms(3)])
  have hb: "qbs_s_finite Y (g \<circ> \<alpha>) \<mu>" "s \<bind> (\<lambda>x. return_qbs Y (g x)) = \<lbrakk>Y, g \<circ> \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using qbs_s_finite.bind_qbs[OF hs(2,1) qbs_morphism_comp[OF assms(3) return_qbs_morphism] qbs_morphism_Mx[OF assms(3)] prob_kernel.s_finite_kernel_prob_kernel 1[simplified comp_assoc[symmetric]]]
          qbs_s_finite.bind_qbs_s_finite[OF hs(2,1) qbs_morphism_comp[OF assms(3) return_qbs_morphism] qbs_morphism_Mx[OF assms(3)] prob_kernel.s_finite_kernel_prob_kernel 1[simplified comp_assoc[symmetric]]]
    by(auto simp: prob_kernel_def' comp_def bind_kernel_return''[OF qs.mu_sets])
  have "?lhs = integrable \<mu> (f \<circ> (g \<circ> \<alpha>))"
    by(auto simp: hb(2) intro!: qbs_s_finite.qbs_integrable_iff_integrable[OF hb(1),simplified comp_def] simp: comp_def lr_adjunction_correspondence[symmetric])
  also have "... = ?rhs"
    by(auto simp: hs(1) comp_def lr_adjunction_correspondence[symmetric] intro!: qs.qbs_integrable_iff_integrable[symmetric])
  finally show ?thesis .
qed

lemma qbs_nn_integral_morphism[qbs]: "qbs_nn_integral \<in> monadM_qbs X \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q qbs_borel) \<Rightarrow>\<^sub>Q qbs_borel"
proof(rule curry_preserves_morphisms[OF pair_qbs_morphismI])
  fix \<alpha> \<beta>
  assume h:"\<alpha> \<in> qbs_Mx (monadM_qbs X)" "\<beta> \<in> qbs_Mx (X \<Rightarrow>\<^sub>Q (qbs_borel :: ennreal quasi_borel))"
  from rep_qbs_Mx_monadM[OF h(1)] obtain a k
    where ak: "\<alpha> = (\<lambda>r. \<lbrakk>X, a, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "a \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X a (k r)"
    by metis
  have 1:"borel_measurable ((borel :: real measure) \<Otimes>\<^sub>M (borel :: real measure)) = qbs_borel \<Otimes>\<^sub>Q qbs_borel \<rightarrow>\<^sub>Q (qbs_borel :: ennreal quasi_borel)"
    by (metis borel_prod qbs_borel_prod standard_borel.standard_borel_r_full_faithful standard_borel_ne_borel standard_borel_ne_def)
  show "(\<lambda>r. qbs_nn_integral (fst (\<alpha> r, \<beta> r)) (snd (\<alpha> r, \<beta> r))) \<in> qbs_Mx qbs_borel"
    unfolding qbs_Mx_qbs_borel
    by(rule measurable_cong[where f="\<lambda>r. \<integral>\<^sup>+ x. \<beta> r (a x) \<partial>k r",THEN iffD1], insert h ak(2))
      (auto simp: qbs_s_finite.qbs_nn_integral_def[OF ak(4)] qbs_Mx_is_morphisms ak(1) 1 intro!: s_finite_kernel.nn_integral_measurable_f[OF ak(3)])
qed

lemma qbs_nn_integral_return:
  assumes "f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
      and "x \<in> qbs_space X"
    shows "qbs_nn_integral (return_qbs X x) f = f x"
  using assms by(auto intro!: nn_integral_return simp: qbs_nn_integral_def2_l qbs_l_return_qbs space_L lr_adjunction_correspondence)

lemma qbs_nn_integral_bind:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs X)"
          "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y" "g \<in> Y \<rightarrow>\<^sub>Q qbs_borel"
    shows "qbs_nn_integral (s \<bind> f) g = qbs_nn_integral s (\<lambda>y. (qbs_nn_integral (f y) g))" (is "?lhs = ?rhs")
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu>
    where hs: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" by metis
  then interpret qs: qbs_s_finite X \<alpha> \<mu> by simp
  from rep_qbs_Mx_monadM[OF qbs_morphism_Mx[OF assms(2) qs.in_Mx]] obtain \<beta> k
    where hk: "f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx Y" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite Y \<beta> (k r)"
    by metis
  note sf = qs.bind_qbs[OF hs(1) assms(2) hk(2,3,1)] qs.bind_qbs_s_finite[OF hs(1) assms(2) hk(2,3,1)]
  have "?lhs = (\<integral>\<^sup>+ x. g (\<beta> x) \<partial>(\<mu> \<bind>\<^sub>k k))"
    by(simp add: sf(1) qbs_s_finite.qbs_nn_integral_def[OF sf(2)])
  also have "... = (\<integral>\<^sup>+ r. (\<integral>\<^sup>+ y. g (\<beta> y) \<partial>(k r)) \<partial>\<mu>)"
    using assms(3) hk(2) by(auto intro!: s_finite_kernel.nn_integral_bind_kernel[OF hk(3)] qs.mu_sets simp: s_finite_kernel_cong_sets[OF qs.mu_sets] lr_adjunction_correspondence)
  also have "... = ?rhs"
    using fun_cong[OF hk(1)] by(auto simp: hs(1) qs.qbs_nn_integral_def qbs_s_finite.qbs_nn_integral_def[OF hk(4),symmetric] intro!: nn_integral_cong)
  finally show ?thesis .
qed

lemma qbs_nn_integral_bind_return:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs Y)" "f \<in> Z \<rightarrow>\<^sub>Q qbs_borel" "g \<in> Y \<rightarrow>\<^sub>Q Z"
  shows "qbs_nn_integral (s \<bind> (\<lambda>y. return_qbs Z (g y))) f = qbs_nn_integral s (f \<circ> g)"
  by(auto simp: qbs_nn_integral_bind[OF assms(1) _ assms(2)] qbs_nn_integral_return intro!: qbs_nn_integral_cong[OF assms(1)])

lemma qbs_integral_morphism[qbs]:
 "qbs_integral \<in> monadM_qbs X \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q qbs_borel) \<Rightarrow>\<^sub>Q (qbs_borel :: ('b :: {second_countable_topology,banach}) quasi_borel)"
proof(rule curry_preserves_morphisms[OF pair_qbs_morphismI])
  fix \<alpha> and \<gamma> :: "_ \<Rightarrow> _ \<Rightarrow> 'b"
  assume h:"\<alpha> \<in> qbs_Mx (monadM_qbs X)" "\<gamma> \<in> qbs_Mx (X \<Rightarrow>\<^sub>Q qbs_borel)"
  from rep_qbs_Mx_monadM[OF this(1)] obtain \<beta> k
    where hk: "\<alpha> = (\<lambda>r. \<lbrakk>X, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<beta> (k r)"
    by metis
  have 1:"borel_measurable ((borel :: real measure) \<Otimes>\<^sub>M (borel :: real measure)) = qbs_borel \<Otimes>\<^sub>Q qbs_borel \<rightarrow>\<^sub>Q (qbs_borel :: (_ :: {second_countable_topology,banach}) quasi_borel)"
    by (metis borel_prod qbs_borel_prod standard_borel.standard_borel_r_full_faithful standard_borel_ne_borel standard_borel_ne_def)
  show "(\<lambda>r. qbs_integral (fst (\<alpha> r,\<gamma> r)) (snd (\<alpha> r,\<gamma> r))) \<in> qbs_Mx borel\<^sub>Q"
    unfolding qbs_Mx_R
    by(rule measurable_cong[where f="\<lambda>r. \<integral> x. \<gamma> r (\<beta> x) \<partial>k r",THEN iffD1], insert h hk(2))
      (auto simp: qbs_s_finite.qbs_integral_def[OF hk(4)] qbs_Mx_is_morphisms hk(1) 1 intro!: s_finite_kernel.integral_measurable_f[OF hk(3)])
qed

lemma qbs_integral_return:
  assumes [qbs]:"f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "x \<in> qbs_space X"
  shows "qbs_integral (return_qbs X x) f = f x"
  by(auto simp: qbs_integral_def2_l qbs_l_return_qbs lr_adjunction_correspondence[symmetric] space_L integral_return)

lemma
  assumes [qbs]: "s \<in> qbs_space (monadM_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y" "g \<in> Y \<rightarrow>\<^sub>Q qbs_borel"
      and "qbs_integrable s (\<lambda>x. \<integral>\<^sub>Q y. norm (g y) \<partial>f x)" "AE\<^sub>Q x in s. qbs_integrable (f x) g"
    shows qbs_integrable_bind: "qbs_integrable (s \<bind> f) g" (is ?goal1)
      and qbs_integral_bind:"(\<integral>\<^sub>Q y. g y \<partial>(s \<bind> f)) = (\<integral>\<^sub>Q x. \<integral>\<^sub>Q y. g y \<partial>f x \<partial>s)" (is "?lhs = ?rhs")
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu>
    where hs: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" by metis
  then interpret qs: qbs_s_finite X \<alpha> \<mu> by simp
  from rep_qbs_Mx_monadM[OF qbs_morphism_Mx[OF assms(2) qs.in_Mx]] obtain \<beta> k
    where hk: "f \<circ> \<alpha> = (\<lambda>r. \<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<beta> \<in> qbs_Mx Y" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite Y \<beta> (k r)"
    by metis
  note sf = qs.bind_qbs[OF hs(1) assms(2) hk(2,3,1)]
  have g[measurable]: "\<And>h M. h \<in> M \<rightarrow>\<^sub>M qbs_to_measure Y \<Longrightarrow> (\<lambda>x. g (h x)) \<in> M \<rightarrow>\<^sub>M borel"
    using assms(3) by(auto simp: lr_adjunction_correspondence)
  interpret qs2: qbs_s_finite Y \<beta> "\<mu> \<bind>\<^sub>k k"
    by(rule qs.bind_qbs_s_finite[OF hs(1) assms(2) hk(2,3,1)])
  show ?goal1
    by(auto simp: sf qs2.qbs_integrable_def intro!: s_finite_kernel.integrable_bind_kernel[OF hk(3) qs.mu_sets])
      (insert qs.AEq_AE[OF assms(5)[simplified hs(1)],simplified fun_cong[OF hk(1),simplified] qbs_s_finite.qbs_integrable_def[OF hk(4)]] assms(4)[simplified hs(1) qs.qbs_integrable_def fun_cong[OF hk(1),simplified]],auto simp: hs(1) qs.qbs_integrable_def qbs_s_finite.qbs_integral_def[OF hk(4)])
  have "?lhs = (\<integral>r. g (\<beta> r) \<partial>(\<mu> \<bind>\<^sub>k k))"
    by(simp add: sf qs2.qbs_integral_def)
  also have "... = (\<integral>r. (\<integral>l. g (\<beta> l)\<partial>k r) \<partial>\<mu>)"
    using qs.AEq_AE[OF assms(5)[simplified hs(1)],simplified fun_cong[OF hk(1),simplified] qbs_s_finite.qbs_integrable_def[OF hk(4)]] assms(4)[simplified hs(1) qs.qbs_integrable_def fun_cong[OF hk(1),simplified]]
    by(auto intro!: s_finite_kernel.integral_bind_kernel[OF hk(3) qs.mu_sets] simp: qbs_s_finite.qbs_integral_def[OF hk(4)])
  also have "... = (\<integral>r. (\<integral>\<^sub>Q y. g y\<partial>\<lbrakk>Y, \<beta>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<partial>\<mu>)"
    by(auto intro!: Bochner_Integration.integral_cong simp: qbs_s_finite.qbs_integral_def[OF hk(4)])
  also have "... = ?rhs"
    by(auto simp: hs(1) qs.qbs_integral_def fun_cong[OF hk(1),simplified comp_def])
  finally show "?lhs = ?rhs" .
qed

lemma qbs_integral_bind_return:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs Y)" "f \<in> Z \<rightarrow>\<^sub>Q qbs_borel" "g \<in> Y \<rightarrow>\<^sub>Q Z"
  shows "qbs_integral (s \<bind> (\<lambda>y. return_qbs Z (g y))) f = qbs_integral s (f \<circ> g)"
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu>
    where hs: "s = \<lbrakk>Y, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite Y \<alpha> \<mu>" by metis
  then interpret qs: qbs_s_finite Y \<alpha> \<mu> by simp

  have hb: "qbs_s_finite Z (g \<circ> \<alpha>) \<mu>" "s \<bind> (\<lambda>y. return_qbs Z (g y)) = \<lbrakk>Z, g \<circ> \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    using qs.bind_qbs_s_finite[OF hs(1) _ qbs_morphism_Mx[OF assms(3) qs.in_Mx] prob_kernel.s_finite_kernel_prob_kernel return_qbs_comp[OF qbs_morphism_Mx[OF assms(3) qs.in_Mx],simplified comp_assoc[symmetric] comp_def[of _ g]],simplified prob_kernel_def']
    by(auto simp: qs.bind_qbs[OF hs(1) _ qbs_morphism_Mx[OF assms(3) qs.in_Mx] prob_kernel.s_finite_kernel_prob_kernel return_qbs_comp[OF qbs_morphism_Mx[OF assms(3) qs.in_Mx],simplified comp_assoc[symmetric] comp_def[of _ g]],simplified prob_kernel_def']  bind_kernel_return''[OF qs.mu_sets])
  show ?thesis
    by(simp add: hb(2) qbs_s_finite.qbs_integral_def[OF hb(1)] qs.qbs_integral_def[simplified hs(1)[symmetric]])
qed

subsubsection \<open> Binary Product Measures\<close>
definition qbs_pair_measure :: "['a qbs_measure, 'b qbs_measure] \<Rightarrow> ('a \<times> 'b) qbs_measure" (infix "\<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s" 80) where
qbs_pair_measure_def':"qbs_pair_measure p q \<equiv> (p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (qbs_space_of p \<Otimes>\<^sub>Q qbs_space_of q) (x, y))))"


context pair_qbs_s_finites
begin

interpretation rr : standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(auto intro!: pair_standard_borel_ne)

lemma
  shows qbs_pair_measure: "\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = \<lbrakk>X \<Otimes>\<^sub>Q Y, map_prod \<alpha> \<beta> \<circ> rr.from_real, distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    and qbs_pair_measure_s_finite: "qbs_s_finite (X \<Otimes>\<^sub>Q Y) (map_prod \<alpha> \<beta> \<circ> rr.from_real) (distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel rr.to_real)"
  by(simp_all add: qbs_pair_measure_def' pq1.qbs_l pq2.qbs_l qbs_bind_bind_return_pq qbs_s_finite_axioms)

lemma qbs_l_qbs_pair_measure:
  "qbs_l (\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) = distr (\<mu> \<Otimes>\<^sub>M \<nu>) (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (map_prod \<alpha> \<beta>)"
  by(simp add: qbs_pair_measure qbs_s_finite.qbs_l[OF qbs_pair_measure_s_finite] distr_distr comp_assoc)

lemma qbs_nn_integral_pair_measure:
  assumes [qbs]:"f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<integral>\<^sup>+\<^sub>Q z. f z \<partial>(\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)) = (\<integral>\<^sup>+ z. (f \<circ> map_prod \<alpha> \<beta>) z \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>))"
  using assms by(simp add: qbs_nn_integral_def2 qbs_pair_measure distr_distr comp_assoc nn_integral_distr lr_adjunction_correspondence)

lemma qbs_integral_pair_measure:
  assumes [qbs]:"f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<integral>\<^sub>Q z. f z \<partial>(\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)) = (\<integral> z. (f \<circ> map_prod \<alpha> \<beta>) z \<partial>(\<mu> \<Otimes>\<^sub>M \<nu>))"
  using assms by(simp add: qbs_integral_def2 qbs_pair_measure distr_distr comp_assoc integral_distr lr_adjunction_correspondence)

lemma qbs_pair_measure_integrable_eq:
 "qbs_integrable (\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) f \<longleftrightarrow> f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q qbs_borel \<and> integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (f \<circ> (map_prod \<alpha> \<beta>))" (is "?h \<longleftrightarrow> ?h1 \<and> ?h2")
proof safe
  assume h: ?h
  show ?h1
    by(auto intro!: qbs_integrable_morphism_dest[OF _ h] simp: qbs_pair_measure_def')
  have 1:"integrable (distr (\<mu> \<Otimes>\<^sub>M \<nu>) borel (to_real_on (borel \<Otimes>\<^sub>M borel))) (f \<circ> (map_prod \<alpha> \<beta> \<circ> from_real_into (borel \<Otimes>\<^sub>M borel)))"
    using h[simplified qbs_pair_measure] by(simp add: qbs_integrable_def[of f] comp_def[of f])
  have "integrable (\<mu> \<Otimes>\<^sub>M \<nu>) (\<lambda>x. (f \<circ> (map_prod \<alpha> \<beta> \<circ> from_real_into (borel \<Otimes>\<^sub>M borel))) (to_real_on (borel \<Otimes>\<^sub>M borel) x))"
    by(intro integrable_distr[OF _ 1]) simp
  thus ?h2
    by(simp add: comp_def)
next
  assume h: ?h1 ?h2
  then show ?h
    by(simp add: qbs_pair_measure qbs_integrable_def) (simp add: lr_adjunction_correspondence integrable_distr_eq[of rr.to_real "\<mu> \<Otimes>\<^sub>M \<nu>" borel "\<lambda>x. f (map_prod \<alpha> \<beta> (rr.from_real x))"] comp_def)
qed

end

lemmas(in pair_qbs_probs) qbs_pair_measure_prob = qbs_prob_axioms

context
  fixes X Y p q
  assumes p[qbs]:"p \<in> qbs_space (monadM_qbs X)" and q[qbs]:"q \<in> qbs_space (monadM_qbs Y)"
begin

lemma qbs_pair_measure_def: "p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q = p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))"
  by(simp add: qbs_space_of_in[OF p] qbs_space_of_in[OF q] qbs_pair_measure_def')

lemma qbs_pair_measure_def2: "p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q = q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))"
  by(simp add: bind_qbs_return_rotate qbs_pair_measure_def)

lemma
  assumes "f \<in>  X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q monadM_qbs Z"
  shows qbs_pair_bind_bind_return1':"q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f (x,y))) = p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q \<bind> f"
    and qbs_pair_bind_bind_return2':"p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f (x,y))) = p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q \<bind> f"
  by(simp_all add: qbs_bind_bind_return1[OF assms] qbs_bind_bind_return2[OF assms] bind_qbs_return_rotate qbs_pair_measure_def)

lemma
  assumes [qbs]:"f \<in>  X \<rightarrow>\<^sub>Q exp_qbs Y (monadM_qbs Z)"
  shows qbs_pair_bind_bind_return1'': "q \<bind> (\<lambda>y. p \<bind> (\<lambda>x. f x y)) = p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q \<bind> (\<lambda>x. f (fst x) (snd x))"
    and qbs_pair_bind_bind_return2'': "p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. f x y)) = p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q \<bind> (\<lambda>x. f (fst x) (snd x))"
   by(auto intro!: qbs_pair_bind_bind_return1'[where f="\<lambda>x. f (fst x) (snd x)",simplified] qbs_pair_bind_bind_return2'[where f="\<lambda>x. f (fst x) (snd x)",simplified] uncurry_preserves_morphisms) qbs

lemma qbs_nn_integral_Fubini_fst:
  assumes [qbs]:"f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q qbs_borel"
    shows "(\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y. f (x,y) \<partial>q \<partial>p) = (\<integral>\<^sup>+\<^sub>Q z. f z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))"
          (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y. qbs_nn_integral (return_qbs (X \<Otimes>\<^sub>Q Y) (x, y)) f \<partial>q \<partial>p)"
    by(auto intro!: qbs_nn_integral_cong p q simp: qbs_nn_integral_return)
  also have "... = ?rhs"
    by(auto intro!: qbs_nn_integral_cong[OF p] simp:qbs_nn_integral_bind[OF q _ assms] qbs_nn_integral_bind[OF p _ assms] qbs_pair_measure_def)
  finally show ?thesis .
qed

lemma qbs_nn_integral_Fubini_snd:
  assumes [qbs]:"f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q qbs_borel"
    shows "(\<integral>\<^sup>+\<^sub>Q y. \<integral>\<^sup>+\<^sub>Q x. f (x,y) \<partial>p \<partial>q) = (\<integral>\<^sup>+\<^sub>Q z. f z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>\<^sup>+\<^sub>Q y. \<integral>\<^sup>+\<^sub>Q x. qbs_nn_integral (return_qbs (X \<Otimes>\<^sub>Q Y) (x, y)) f \<partial>p \<partial>q)"
    by(auto intro!: qbs_nn_integral_cong p q simp: qbs_nn_integral_return)
  also have "... = ?rhs"
    by(auto intro!: qbs_nn_integral_cong[OF q] simp:qbs_nn_integral_bind[OF q _ assms] qbs_nn_integral_bind[OF p _ assms] qbs_pair_measure_def2)
  finally show ?thesis .
qed

lemma qbs_ennintegral_indep_mult:
  assumes [qbs]: "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> Y \<rightarrow>\<^sub>Q qbs_borel"
    shows "(\<integral>\<^sup>+\<^sub>Q z. f (fst z) * g (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>p) * (\<integral>\<^sup>+\<^sub>Q y. g y \<partial>q)" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y .f x * g y \<partial>q \<partial>p)"
    using qbs_nn_integral_Fubini_fst[where f="\<lambda>z. f (fst z) * g (snd z)"] by simp
  also have "... = (\<integral>\<^sup>+\<^sub>Q x. f x * \<integral>\<^sup>+\<^sub>Q y . g y \<partial>q \<partial>p)"
    by(simp add: qbs_nn_integral_cmult[OF q])
  also have "... = ?rhs"
    by(simp add: qbs_nn_integral_cmult[OF p] ab_semigroup_mult_class.mult.commute[where b="qbs_nn_integral q g"])
  finally show ?thesis .
qed

end

lemma qbs_l_qbs_pair_measure:
  assumes "standard_borel M" "standard_borel N"
  defines "X \<equiv> measure_to_qbs M" and "Y \<equiv> measure_to_qbs N"
  assumes [qbs]: "p \<in> qbs_space (monadM_qbs X)" "q \<in> qbs_space (monadM_qbs Y)"
  shows "qbs_l (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) = qbs_l p \<Otimes>\<^sub>M qbs_l q"
proof -
  obtain \<alpha> \<mu> \<beta> \<nu>
    where hp: "p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
      and hq: "q = \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite Y \<beta> \<nu>" 
    using rep_qbs_space_monadM assms(5,6) by meson
  have 1:"sets (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) = sets (M \<Otimes>\<^sub>M N)"
    by(auto simp: r_preserves_product[symmetric] X_def Y_def intro!: standard_borel.lr_sets_ident pair_standard_borel assms)
  have "qbs_l (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) = qbs_l p \<bind>\<^sub>k qbs_l \<circ> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x,y)))"
    by(auto simp: qbs_pair_measure_def[of p X q Y] intro!: qbs_l_bind_qbs[of _ X _ "X \<Otimes>\<^sub>Q Y"])
  also have "... = qbs_l p \<bind>\<^sub>k (\<lambda>x. qbs_l (q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x, y))))"
    by(simp add: comp_def)
  also have "... = qbs_l p \<bind>\<^sub>k (\<lambda>x. qbs_l q \<bind>\<^sub>k qbs_l \<circ> (\<lambda>y.  return_qbs (X \<Otimes>\<^sub>Q Y) (x, y)))"
    by(auto intro!: bind_kernel_cong_All qbs_l_bind_qbs[of _ "Y" _ "X \<Otimes>\<^sub>Q Y"] simp: space_qbs_l_in[OF assms(5)])
  also have "... = qbs_l p \<bind>\<^sub>k (\<lambda>x. qbs_l q \<bind>\<^sub>k (\<lambda>y. return (qbs_to_measure (X \<Otimes>\<^sub>Q Y)) (x, y)))"
    by(auto simp: comp_def space_qbs_l_in[OF assms(6)] space_qbs_l_in[OF assms(5)] qbs_l_return_qbs intro!: bind_kernel_cong_All)
  also have "... = qbs_l p \<bind>\<^sub>k (\<lambda>x. qbs_l q \<bind>\<^sub>k (\<lambda>y. return (M \<Otimes>\<^sub>M N) (x, y)))"
    by(simp add: return_cong[OF 1])
  also have "... = qbs_l p \<bind>\<^sub>k (\<lambda>x. qbs_l q \<bind>\<^sub>k (\<lambda>y. return (qbs_l p \<Otimes>\<^sub>M qbs_l q) (x, y)))"
    by(auto cong: return_cong sets_pair_measure_cong simp: sets_qbs_l[OF assms(5)] standard_borel.lr_sets_ident[OF assms(1)] sets_qbs_l[OF assms(6)] standard_borel.lr_sets_ident[OF assms(2)] X_def Y_def)
  also have "... = qbs_l p \<Otimes>\<^sub>M qbs_l q"
    by(auto intro!: pair_measure_eq_bind_s_finite[symmetric] qbs_l_s_finite.s_finite_measure_axioms)
  finally show ?thesis .
qed

lemma qbs_pair_measure_morphism[qbs]: "qbs_pair_measure \<in> monadM_qbs X \<rightarrow>\<^sub>Q monadM_qbs Y \<Rightarrow>\<^sub>Q monadM_qbs (X \<Otimes>\<^sub>Q Y)"
  by(rule curry_preserves_morphisms,rule qbs_morphism_cong'[where f="(\<lambda>(p,q). (p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x, y)))))"]) (auto simp: pair_qbs_space qbs_pair_measure_def)

lemma qbs_pair_measure_morphismP:
 "qbs_pair_measure \<in> monadP_qbs X \<rightarrow>\<^sub>Q monadP_qbs Y \<Rightarrow>\<^sub>Q monadP_qbs (X \<Otimes>\<^sub>Q Y)"
proof -
  note [qbs] = return_qbs_morphismP bind_qbs_morphismP
  show ?thesis
    by(rule curry_preserves_morphisms,rule qbs_morphism_cong'[where f="(\<lambda>(p,q). (p \<bind> (\<lambda>x. q \<bind> (\<lambda>y. return_qbs (X \<Otimes>\<^sub>Q Y) (x, y)))))"]) (auto simp: pair_qbs_space qbs_pair_measure_def[OF qbs_space_monadPM qbs_space_monadPM])
qed

lemma qbs_nn_integral_indep1:
  assumes [qbs]:"p \<in> qbs_space (monadM_qbs X)" "q \<in> qbs_space (monadP_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
    shows "(\<integral>\<^sup>+\<^sub>Q z. f (fst z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sup>+\<^sub>Q x. f x \<partial>p)"
proof -
  obtain Y \<beta> \<nu> where hq:
   "q = \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_prob Y \<beta> \<nu>"
    using rep_qbs_space_monadP[OF assms(2)] by blast 
  then interpret qbs_prob Y \<beta> \<nu> by simp
  show ?thesis
    by(simp add: qbs_nn_integral_const_prob[OF in_space_monadP] qbs_nn_integral_Fubini_snd[OF assms(1) in_space_monadM,symmetric] hq(1))
qed

lemma qbs_nn_integral_indep2:
  assumes [qbs]:"q \<in> qbs_space (monadM_qbs Y)" "p \<in> qbs_space (monadP_qbs X)" "f \<in> Y \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<integral>\<^sup>+\<^sub>Q z. f (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sup>+\<^sub>Q y. f y \<partial>q)"
proof -
  obtain  X \<alpha> \<mu> where hp:
    "p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_prob X \<alpha> \<mu>"
    using rep_qbs_space_monadP[OF assms(2)] by metis
  then interpret qbs_prob X \<alpha> \<mu> by simp
  show ?thesis
    by(simp add: qbs_nn_integral_const_prob[OF in_space_monadP] qbs_nn_integral_Fubini_snd[OF in_space_monadM assms(1),symmetric] hp(1))
qed


context
begin

interpretation rr : standard_borel_ne "borel \<Otimes>\<^sub>M borel :: (real \<times> real) measure"
  by(auto intro!: pair_standard_borel_ne)

lemma qbs_integrable_pair_swap:
  assumes "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
  shows "qbs_integrable (q \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p) (\<lambda>(x,y). f (y,x))"
proof -
  obtain X \<alpha> \<mu> Y \<beta> \<nu>
    where hp: "p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
      and hq: "q = \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite Y \<beta> \<nu>" 
    using rep_qbs_s_finite_measure by meson
  interpret p1: pair_qbs_s_finites X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_s_finites_def hq hp)
  interpret p2: pair_qbs_s_finites Y \<beta> \<nu> X \<alpha> \<mu>
    by(simp add: pair_qbs_s_finites_def hq hp)
  show ?thesis
    using assms by(auto simp: hp(1) hq(1) p1.qbs_pair_measure p2.qbs_pair_measure p1.qbs_integrable_def p2.qbs_integrable_def)
    (auto simp add: integrable_distr_eq lr_adjunction_correspondence qbs_Mx_is_morphisms map_prod_def split_beta' intro!:integrable_product_swap_iff_s_finite[OF p1.pq2.s_finite_measure_axioms p1.pq1.s_finite_measure_axioms,THEN iffD1])
qed

lemma qbs_integrable_pair1':
  assumes [qbs]:"p \<in> qbs_space (monadM_qbs X)"
          "q \<in> qbs_space (monadM_qbs Y)"
          "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q qbs_borel"
          "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. norm (f (x,y)) \<partial>q)"
      and "AE\<^sub>Q x in p. qbs_integrable q (\<lambda>y. f (x,y))"
    shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
proof -
  obtain \<alpha> \<mu> \<beta> \<nu>
    where hp: "p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
      and hq: "q = \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite Y \<beta> \<nu>" 
    using rep_qbs_space_monadM assms(1,2) by meson
  then interpret pqs: pair_qbs_s_finites X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_s_finites_def)
  have [measurable]: "f \<in> borel_measurable (qbs_to_measure (X \<Otimes>\<^sub>Q Y))"
    by(simp add: lr_adjunction_correspondence[symmetric])
  show ?thesis
    using assms(4) pqs.pq1.AEq_AE[OF assms(5)[simplified hp(1)]]
    by(auto simp add: pqs.qbs_integrable_def pqs.qbs_pair_measure hp(1) hq(1) integrable_distr_eq pqs.pq2.qbs_integrable_def pqs.pq1.qbs_integrable_def pqs.pq2.qbs_integral_def intro!: s_finite_measure.Fubini_integrable' pqs.pq2.s_finite_measure_axioms)
qed

lemma 
  assumes "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
  shows qbs_integrable_pair1D1': "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. f (x,y) \<partial>q)"             (is ?g1)
    and qbs_integrable_pair1D1_norm': "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. norm (f (x,y)) \<partial>q)" (is ?g2)
    and qbs_integrable_pair1D2': "AE\<^sub>Q x in p. qbs_integrable q (\<lambda>y. f (x,y))"          (is ?g3)
    and qbs_integrable_pair2D1': "qbs_integrable q (\<lambda>y. \<integral>\<^sub>Q x. f (x,y) \<partial>p)"             (is ?g4)
    and qbs_integrable_pair2D1_norm': "qbs_integrable q (\<lambda>y. \<integral>\<^sub>Q x. norm (f (x,y)) \<partial>p)" (is ?g5)
    and qbs_integrable_pair2D2': "AE\<^sub>Q y in q. qbs_integrable p (\<lambda>x. f (x,y))"          (is ?g6)
    and qbs_integral_Fubini_fst': "(\<integral>\<^sub>Q x. \<integral>\<^sub>Q y. f (x,y) \<partial>q \<partial>p) = (\<integral>\<^sub>Q z. f z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))" (is ?g7)
    and qbs_integral_Fubini_snd': "(\<integral>\<^sub>Q y. \<integral>\<^sub>Q x. f (x,y) \<partial>p \<partial>q) = (\<integral>\<^sub>Q z. f z \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))" (is ?g8)
proof -
  obtain X \<alpha> \<mu> Y \<beta> \<nu>
    where hp: "p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
      and hq: "q = \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite Y \<beta> \<nu>"
    by (meson rep_qbs_space_of)
  then interpret pqs: pair_qbs_s_finites X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_s_finites_def)
  have [qbs]:"p \<in> qbs_space (monadM_qbs X)" "q \<in> qbs_space (monadM_qbs Y)"
    by(simp_all add: hp hq)
  note qbs_pair_measure_morphism[qbs]
  have f[qbs]:"f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q qbs_borel"
    by(auto intro!: qbs_integrable_morphism_dest[OF _ assms])   
  have [measurable]: "f \<in> borel_measurable (qbs_to_measure (X \<Otimes>\<^sub>Q Y))"
    by(simp add: lr_adjunction_correspondence[symmetric])
  show ?g1 ?g2 ?g4 ?g5
    using assms
    by(auto simp: hp(1) hq(1) pqs.qbs_integrable_def pqs.qbs_pair_measure integrable_distr_eq pqs.pq1.qbs_integrable_def pqs.pq2.qbs_integrable_def pqs.pq2.qbs_integral_def pqs.pq1.qbs_integral_def intro!: Bochner_Integration.integrable_cong[where g="\<lambda>r. \<integral>\<^sub>Q y. f (\<alpha> r, y) \<partial>\<lbrakk>Y, \<beta>,  \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" and f="\<lambda>x. \<integral> y. f (\<alpha> x, \<beta> y) \<partial>\<nu>" and N0=\<mu>,THEN iffD1] Bochner_Integration.integrable_cong[where g="\<lambda>r. \<integral>\<^sub>Q x. f (x, \<beta> r) \<partial>\<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" and f="\<lambda>y. \<integral> x. f (\<alpha> x, \<beta> y) \<partial>\<mu>" and N0=\<nu>,THEN iffD1])
      (auto intro!: pqs.pq2.integrable_fst''[of \<mu>] integrable_snd_s_finite[OF pqs.pq1.s_finite_measure_axioms pqs.pq2.s_finite_measure_axioms] simp: map_prod_def split_beta')
  show ?g3 ?g6
    using assms
    by(auto simp: hp(1) pqs.pq1.AEq_AE_iff hq(1) pqs.pq2.AEq_AE_iff pqs.qbs_integrable_def pqs.qbs_pair_measure integrable_distr_eq)
      (auto simp: pqs.pq1.qbs_integrable_def pqs.pq2.qbs_integrable_def map_prod_def split_beta' intro!: pqs.pq2.AE_integrable_fst'' AE_integrable_snd_s_finite[OF pqs.pq1.s_finite_measure_axioms pqs.pq2.s_finite_measure_axioms])
  show ?g7 ?g8
    using assms
    by(auto simp: hp(1) hq(1) pqs.qbs_integrable_def pqs.qbs_pair_measure pqs.qbs_integral_def pqs.pq1.qbs_integral_def pqs.pq2.qbs_integral_def integral_distr integrable_distr_eq)
      (auto simp: map_prod_def split_beta' intro!: pqs.pq2.integral_fst'''[of \<mu> "\<lambda>x. f (\<alpha> (fst x),\<beta> (snd x))",simplified] integral_snd_s_finite[OF pqs.pq1.s_finite_measure_axioms pqs.pq2.s_finite_measure_axioms,of "\<lambda>x y. f (\<alpha> x, \<beta> y)",simplified split_beta'])
qed

end

lemma 
  assumes h:"qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (case_prod f)"
  shows qbs_integrable_pair1D1: "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. f x y \<partial>q)"
    and qbs_integrable_pair1D1_norm: "qbs_integrable p (\<lambda>x. \<integral>\<^sub>Q y. norm (f x y) \<partial>q)"
    and qbs_integrable_pair1D2:  "AE\<^sub>Q x in p. qbs_integrable q (\<lambda>y. f x y)"
    and qbs_integrable_pair2D1: "qbs_integrable q (\<lambda>y. \<integral>\<^sub>Q x. f x y \<partial>p)"
    and qbs_integrable_pair2D1_norm: "qbs_integrable q (\<lambda>y. \<integral>\<^sub>Q x. norm (f x y) \<partial>p)"
    and qbs_integrable_pair2D2:  "AE\<^sub>Q y in q. qbs_integrable p (\<lambda>x. f x y)"
    and qbs_integral_Fubini_fst: "(\<integral>\<^sub>Q x. \<integral>\<^sub>Q y. f x y \<partial>q \<partial>p) = (\<integral>\<^sub>Q (x,y). f x y \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))" (is ?g7)
    and qbs_integral_Fubini_snd: "(\<integral>\<^sub>Q y. \<integral>\<^sub>Q x. f x y \<partial>p \<partial>q) = (\<integral>\<^sub>Q (x,y). f x y \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q))" (is ?g8)
  using qbs_integrable_pair1D1'[OF h] qbs_integrable_pair1D1_norm'[OF h] qbs_integrable_pair1D2'[OF h] qbs_integral_Fubini_fst'[OF h]
        qbs_integrable_pair2D1'[OF h] qbs_integrable_pair2D1_norm'[OF h] qbs_integrable_pair2D2'[OF h] qbs_integral_Fubini_snd'[OF h]
  by simp_all

lemma qbs_integrable_pair2':
  assumes "p \<in> qbs_space (monadM_qbs X)"
          "q \<in> qbs_space (monadM_qbs Y)"
          "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q qbs_borel"
          "qbs_integrable q (\<lambda>y. \<integral>\<^sub>Q x. norm (f (x,y)) \<partial>p)"
      and "AE\<^sub>Q y in q. qbs_integrable p (\<lambda>x. f (x,y))"
    shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) f"
  using qbs_integrable_pair_swap[OF qbs_integrable_pair1'[OF assms(2,1) qbs_morphism_pair_swap[OF assms(3)],simplified],OF assms(4,5)]
  by simp

lemma qbs_integrable_indep_mult:
  fixes f :: "_ \<Rightarrow> _::{real_normed_div_algebra,second_countable_topology}"
  assumes "qbs_integrable p f" "qbs_integrable q g"
  shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>x. f (fst x) * g (snd x))"
proof -
  obtain X \<alpha> \<mu> Y \<beta> \<nu>
    where hp: "p = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
      and hq: "q = \<lbrakk>Y, \<beta>, \<nu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite Y \<beta> \<nu>"
    by (meson rep_qbs_space_of)
  then interpret pqs: pair_qbs_s_finites X \<alpha> \<mu> Y \<beta> \<nu>
    by(simp add: pair_qbs_s_finites_def)
  have [qbs]:"f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> Y \<rightarrow>\<^sub>Q qbs_borel" "p \<in> qbs_space (monadM_qbs X)" "q \<in> qbs_space (monadM_qbs Y)"
    by(auto intro!: qbs_integrable_morphism_dest assms simp:hp hq)
  show ?thesis
    by(auto intro!: qbs_integrable_pair1'[of _ X _ Y] qbs_integrable_mult_left qbs_integrable_norm assms(1) AEq_I2[of _ X] simp: norm_mult qbs_integrable_mult_right[OF assms(2)])
qed 

lemma qbs_integrable_indep1:
  fixes f :: "_ \<Rightarrow> _::{real_normed_div_algebra,second_countable_topology}"
  assumes "qbs_integrable p f" "q \<in> qbs_space (monadP_qbs Y)"
  shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>x. f (fst x))"
  using qbs_integrable_indep_mult[OF assms(1) qbs_integrable_const[OF assms(2),of 1]] by simp

lemma qbs_integral_indep1:
  fixes f :: "_ \<Rightarrow> _::{real_normed_div_algebra,second_countable_topology}"
  assumes "qbs_integrable p f" "q \<in> qbs_space (monadP_qbs Y)"
  shows "(\<integral>\<^sub>Q z. f (fst z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q x. f x \<partial>p)"
  using qbs_integral_Fubini_snd'[OF qbs_integrable_indep1[OF assms]]
  by(simp add: qbs_integral_const_prob[OF assms(2)])

lemma qbs_integrable_indep2:
  fixes g :: "_ \<Rightarrow> _::{real_normed_div_algebra,second_countable_topology}"
  assumes "qbs_integrable q g" "p \<in> qbs_space (monadP_qbs X)"
  shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>x. g (snd x))"
  using qbs_integrable_pair_swap[OF qbs_integrable_indep1[OF assms]]
  by(simp add: split_beta')

lemma qbs_integral_indep2:
  fixes g :: "_ \<Rightarrow> _::{real_normed_div_algebra,second_countable_topology}"
  assumes "qbs_integrable q g" "p \<in> qbs_space (monadP_qbs X)"
  shows "(\<integral>\<^sub>Q z. g (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q y. g y \<partial>q)"
  using qbs_integral_Fubini_fst'[OF qbs_integrable_indep2[OF assms]]
  by(simp add: qbs_integral_const_prob[OF assms(2)])

lemma qbs_integral_indep_mult1:
  fixes f and g:: "_ \<Rightarrow> _::{real_normed_field,second_countable_topology}"
  assumes "p \<in> qbs_space (monadP_qbs X)" "q \<in> qbs_space (monadP_qbs Y)"
      and "qbs_integrable p f" "qbs_integrable q g"
    shows "(\<integral>\<^sub>Q z. f (fst z) * g (snd z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q x. f x \<partial>p) * (\<integral>\<^sub>Q y. g y \<partial>q)"
  using qbs_integral_Fubini_fst'[OF qbs_integrable_indep_mult[OF assms(3,4)]]
  by simp

lemma qbs_integral_indep_mult2:
  fixes f and g:: "_ \<Rightarrow> _::{real_normed_field,second_countable_topology}"
  assumes "p \<in> qbs_space (monadP_qbs X)" "q \<in> qbs_space (monadP_qbs Y)"
      and "qbs_integrable p f" "qbs_integrable q g"
    shows "(\<integral>\<^sub>Q z. g (snd z) * f (fst z) \<partial>(p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q)) = (\<integral>\<^sub>Q y. g y \<partial>q) * (\<integral>\<^sub>Q x. f x \<partial>p)"
  using qbs_integral_indep_mult1[OF assms] by(simp add: mult.commute)

subsubsection \<open> The Inverse Function of $l$\<close>
definition qbs_l_inverse :: "'a measure \<Rightarrow> 'a qbs_measure" where
 "qbs_l_inverse M \<equiv> \<lbrakk>measure_to_qbs M, from_real_into M, distr M borel (to_real_on M)\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"

context standard_borel_ne
begin

lemma qbs_l_inverse_def2:
  assumes [measurable_cong]: "sets \<mu> = sets M"
      and "s_finite_measure \<mu>"
    shows "qbs_l_inverse \<mu> = \<lbrakk>measure_to_qbs M, from_real, distr \<mu> borel to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
proof -
  interpret s: standard_borel_ne \<mu>
    using assms standard_borel_ne_axioms standard_borel_ne_sets by blast
  have [measurable]: "s.from_real \<in> borel \<rightarrow>\<^sub>M M"
    using assms(1) measurable_cong_sets s.from_real_measurable by blast
  show ?thesis
    by(auto simp: distr_distr qbs_l_inverse_def qbs_s_finite_eq_def qbs_s_finite_def in_Mx_def qbs_Mx_R qbs_s_finite_axioms_def intro!: qbs_s_finite_measure_eq s_finite_measure.s_finite_measure_distr assms cong: measure_to_qbs_cong_sets[OF assms(1)]) (auto intro!: distr_cong simp: sets_eq_imp_space_eq[OF assms(1)])
qed

lemma
  assumes [measurable_cong]:"sets \<mu> = sets M"
  shows qbs_l_inverse_s_finite: "s_finite_measure \<mu> \<Longrightarrow> qbs_s_finite (measure_to_qbs M) from_real (distr \<mu> borel to_real)"
    and qbs_l_inverse_qbs_prob: "prob_space \<mu> \<Longrightarrow> qbs_prob (measure_to_qbs M) from_real (distr \<mu> borel to_real)"
   by(auto simp: qbs_s_finite_def qbs_prob_def in_Mx_def  qbs_s_finite_axioms_def real_distribution_def real_distribution_axioms_def qbs_Mx_R intro!: s_finite_measure.s_finite_measure_distr prob_space.prob_space_distr)

corollary
  assumes [measurable_cong]:"sets \<mu> = sets M"
  shows qbs_l_inverse_in_space_monadM: "s_finite_measure \<mu> \<Longrightarrow> qbs_l_inverse \<mu> \<in> qbs_space (monadM_qbs M)"
    and qbs_l_inverse_in_space_monadP: "prob_space \<mu> \<Longrightarrow> qbs_l_inverse \<mu> \<in> qbs_space (monadP_qbs M)"
  by(auto simp: qbs_l_inverse_def2[OF assms(1)] qbs_l_inverse_def2[OF assms(1) prob_space.s_finite_measure_prob] assms intro!: qbs_s_finite.in_space_monadM[OF qbs_l_inverse_s_finite] qbs_prob.in_space_monadP[OF qbs_l_inverse_qbs_prob])

lemma qbs_l_qbs_l_inverse:
  assumes [measurable_cong]: "sets \<mu> = sets M" "s_finite_measure \<mu>"
  shows "qbs_l (qbs_l_inverse \<mu>) = \<mu>"
proof -
  interpret qbs_s_finite "measure_to_qbs M" from_real "distr \<mu> borel to_real"
    by(auto intro!: qbs_l_inverse_s_finite assms)
  show ?thesis
    using distr_id'[OF assms(1),simplified sets_eq_imp_space_eq[OF assms(1)]]
    by(auto simp: qbs_l qbs_l_inverse_def2[OF assms] distr_distr cong: distr_cong)
qed

corollary qbs_l_qbs_l_inverse_prob:
  "sets \<mu> = sets M \<Longrightarrow> prob_space \<mu> \<Longrightarrow> qbs_l (qbs_l_inverse \<mu>) = \<mu>"
  by(auto intro!: qbs_l_qbs_l_inverse prob_space.s_finite_measure_prob)

lemma qbs_l_inverse_qbs_l:
  assumes "s \<in> qbs_space (monadM_qbs (measure_to_qbs M))"
  shows "qbs_l_inverse (qbs_l s) = s"
proof -
  from rep_qbs_space_monadM[OF assms] obtain \<alpha> \<mu> where h:
   "s = \<lbrakk>measure_to_qbs M, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite (measure_to_qbs M) \<alpha> \<mu>"
    by metis
  then interpret qs:qbs_s_finite "measure_to_qbs M" \<alpha> \<mu> by simp
  have [simp]: "distr \<mu> (qbs_to_measure (measure_to_qbs M)) \<alpha> = distr \<mu> M \<alpha>"
    by(simp cong: distr_cong)
  interpret s: standard_borel_ne "distr \<mu> M \<alpha>"
    by(rule standard_borel_ne_sets[of M]) (auto simp: standard_borel_ne_axioms)
  have [measurable]: "s.from_real \<in> borel \<rightarrow>\<^sub>M M" "\<alpha> \<in> \<mu> \<rightarrow>\<^sub>M M"
    using qs.\<alpha>_measurable[simplified measurable_cong_sets[OF refl lr_sets_ident]]
    by(auto simp: s.from_real_measurable[simplified measurable_cong_sets[OF refl sets_distr]])
  interpret pqs:pair_qbs_s_finite "measure_to_qbs M" s.from_real "distr \<mu> borel (s.to_real \<circ> \<alpha>)" \<alpha> \<mu>
    by(auto simp: pair_qbs_s_finite_def h) (auto simp: qbs_s_finite_def in_Mx_def qs.s_finite_measure_axioms qbs_s_finite_axioms_def qbs_Mx_R  intro!: s_finite_measure.s_finite_measure_distr)
  show ?thesis
    by(auto simp add: h(1) qs.qbs_l qbs_l_inverse_def distr_distr cong: measure_to_qbs_cong_sets intro!: pqs.qbs_s_finite_measure_eq)
      (insert qbs_Mx_to_X[of _ "measure_to_qbs M"], auto simp: comp_def qbs_space_R)
qed

corollary qbs_l_inverse_qbs_l_prob:
  assumes "s \<in> qbs_space (monadP_qbs (measure_to_qbs M))"
  shows "qbs_l_inverse (qbs_l s) = s"
  by(auto intro!: qbs_l_inverse_qbs_l qbs_space_monadPM assms)

lemma s_finite_kernel_qbs_morphism:
  assumes "s_finite_kernel N M k"
  shows "(\<lambda>x. qbs_l_inverse (k x)) \<in> measure_to_qbs N \<rightarrow>\<^sub>Q monadM_qbs (measure_to_qbs M)"
proof -
  interpret sfin: s_finite_kernel N M k by fact
  have "\<lbrakk>measure_to_qbs M, from_real, distr (k x) borel to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n = qbs_l_inverse (k x)" if x:"x \<in> space N" for x
  proof -
    note sfin.kernel_sets[OF x,simp, measurable_cong]
    then interpret skx: standard_borel_ne "k x"
      using standard_borel_ne_axioms standard_borel_ne_sets by blast
    interpret pqs: pair_qbs_s_finite "measure_to_qbs M" from_real "distr (k x) borel to_real" skx.from_real "distr (k x) borel skx.to_real"
      using skx.from_real_measurable[simplified measurable_cong_sets[OF refl sfin.kernel_sets[OF x]]]
      by(auto simp: pair_qbs_s_finite_def qbs_s_finite_def in_Mx_def qbs_Mx_R qbs_s_finite_axioms_def sfin.image_s_finite_measure[OF x] intro!: s_finite_measure.s_finite_measure_distr)
    show ?thesis
      by(auto simp: qbs_l_inverse_def distr_distr cong: measure_to_qbs_cong_sets  intro!: pqs.qbs_s_finite_measure_eq) (auto intro!: distr_cong simp: sfin.kernel_space[OF x])
  qed
  moreover have "(\<lambda>x. \<lbrakk>measure_to_qbs M, from_real, distr (k x) borel to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<in> measure_to_qbs N \<rightarrow>\<^sub>Q monadM_qbs (measure_to_qbs M)"
  proof(rule qbs_morphismI)
    fix \<alpha> :: "real \<Rightarrow> _"
    assume "\<alpha> \<in> qbs_Mx (measure_to_qbs N)"
    then have [measurable]: "\<alpha> \<in> borel \<rightarrow>\<^sub>M N"
      by(simp add: qbs_Mx_R)
    show "(\<lambda>x. \<lbrakk>measure_to_qbs M, from_real, distr (k x) borel to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n) \<circ> \<alpha> \<in> qbs_Mx (monadM_qbs (measure_to_qbs M))"
      by(auto simp: monadM_qbs_Mx qbs_Mx_R intro!: exI[where x=from_real] exI[where x="\<lambda>x. distr (k (\<alpha> x)) borel to_real"] s_finite_kernel.comp_measurable[OF sfin.distr_s_finite_kernel])
  qed
  ultimately show ?thesis
    by(rule qbs_morphism_cong'[of "measure_to_qbs N",simplified qbs_space_R])
qed

lemma prob_kernel_qbs_morphism:
  assumes [measurable]:"k \<in> N  \<rightarrow>\<^sub>M prob_algebra M"
  shows "(\<lambda>x. qbs_l_inverse (k x)) \<in> measure_to_qbs N \<rightarrow>\<^sub>Q monadP_qbs (measure_to_qbs M)"
proof(safe intro!: qbs_morphism_monadPI' s_finite_kernel_qbs_morphism prob_kernel.s_finite_kernel_prob_kernel)
  fix x
  assume "x \<in> qbs_space (measure_to_qbs N)"
  then have "x \<in> space N" by(simp add: qbs_space_R)
  from measurable_space[OF assms this]
  have [measurable_cong, simp]: "sets (k x) = sets M" and p:"prob_space (k x)"
    by(auto simp: space_prob_algebra)
  then interpret s: standard_borel_ne "k x"
    using standard_borel_ne_axioms standard_borel_ne_sets by blast
  show "qbs_l_inverse (k x) \<in> qbs_space (monadP_qbs (measure_to_qbs M))"
    using s.qbs_l_inverse_in_space_monadP[OF refl p] by(simp cong: measure_to_qbs_cong_sets)
qed(simp add: prob_kernel_def')

lemma qbs_l_inverse_return:
  assumes "x \<in> space M"
  shows "qbs_l_inverse (return M x) = return_qbs (measure_to_qbs M) x"
proof -
  interpret s: standard_borel_ne "return M x"
    by(rule standard_borel_ne_sets[of M]) (auto simp: standard_borel_ne_axioms)
  show ?thesis
    using s.qbs_l_inverse_in_space_monadP[OF refl prob_space_return[OF assms]]
    by(auto intro!: inj_onD[OF qbs_l_inj_P[of "measure_to_qbs M"]] return_cong qbs_l_inverse_in_space_monadP qbs_morphism_space[OF return_qbs_morphismP[of "measure_to_qbs M"]] assms simp: s.qbs_l_qbs_l_inverse_prob[OF refl prob_space_return[OF assms]] qbs_l_return_qbs[of _ M,simplified qbs_space_R,OF assms] qbs_space_R cong: measure_to_qbs_cong_sets)
qed

lemma qbs_l_inverse_bind_kernel:
  assumes "standard_borel_ne N" "s_finite_measure M" "s_finite_kernel M N k"
    shows "qbs_l_inverse (M \<bind>\<^sub>k k) = qbs_l_inverse M \<bind> (\<lambda>x. qbs_l_inverse (k x))" (is "?lhs = ?rhs")
proof -
  interpret sfin: s_finite_kernel M N k by fact
  interpret s: standard_borel_ne N by fact
  have sets[simp,measurable_cong]:"sets (M \<bind>\<^sub>k k) = sets N"
    by(auto intro!: sets_bind_kernel[OF _ space_ne] simp: sfin.kernel_sets)
  then interpret s2: standard_borel_ne "M \<bind>\<^sub>k k"
    using s.standard_borel_ne_axioms standard_borel_ne_sets by blast
  have [measurable]: "s2.from_real \<in> borel \<rightarrow>\<^sub>M N"
    using measurable_cong_sets s2.from_real_measurable sets by blast
  have comp1:"(\<lambda>x. qbs_l_inverse (k x)) \<circ> from_real = (\<lambda>r. \<lbrakk>measure_to_qbs N, s.from_real, distr (k (from_real r)) borel s.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)"
  proof
    fix r
    have setskfr[measurable_cong, simp]: "sets (k (from_real r)) = sets N"
      by(auto intro!: sfin.kernel_sets measurable_space[OF from_real_measurable])
    then interpret s3: standard_borel_ne "k (from_real r)"
      using s.standard_borel_ne_axioms standard_borel_ne_sets by blast
    have [measurable]: "s3.from_real \<in> borel \<rightarrow>\<^sub>M N"
      using measurable_cong_sets s3.from_real_measurable setskfr by blast
    show "((\<lambda>x. qbs_l_inverse (k x)) \<circ> from_real) r = \<lbrakk>measure_to_qbs N, s.from_real, distr (k (from_real r)) borel s.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n "
      by(auto simp: qbs_l_inverse_def qbs_s_finite_eq_def qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def qbs_Mx_R distr_distr measurable_space[OF from_real_measurable] cong: measure_to_qbs_cong_sets intro!: sfin.image_s_finite_measure s_finite_measure.s_finite_measure_distr qbs_s_finite_measure_eq) (auto intro!: distr_cong simp: sets_eq_imp_space_eq[OF setskfr])
  qed
  have "?lhs = \<lbrakk>measure_to_qbs (M \<bind>\<^sub>k k), s2.from_real, distr (M \<bind>\<^sub>k k) borel s2.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(simp add: qbs_l_inverse_def)
  also have "... = \<lbrakk>measure_to_qbs N, s.from_real, distr (M \<bind>\<^sub>k k) borel s.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(auto cong: measure_to_qbs_cong_sets intro!: qbs_s_finite_measure_eq distr_cong s_finite_measure.s_finite_measure_distr sfin.comp_s_finite_measure assms(2) simp: qbs_s_finite_eq_def qbs_s_finite_def qbs_s_finite_axioms_def in_Mx_def qbs_Mx_R distr_distr sets_eq_imp_space_eq[OF sets])
  also have "... = \<lbrakk>measure_to_qbs N, s.from_real, M \<bind>\<^sub>k (\<lambda>x. distr (k x) borel s.to_real)\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    by(simp add: sfin.distr_bind_kernel[OF space_ne refl])
  also have "... = \<lbrakk>measure_to_qbs N, s.from_real, distr M borel to_real \<bind>\<^sub>k (\<lambda>r. distr (k (from_real r)) borel s.to_real)\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
  proof -
    have "M \<bind>\<^sub>k (\<lambda>x. distr (k x) borel s.to_real) = M \<bind>\<^sub>k (\<lambda>x. distr (k (from_real (to_real x))) borel s.to_real)"
      by(auto intro!: bind_kernel_cong_All)
    also have "... = distr M borel to_real \<bind>\<^sub>k (\<lambda>r. distr (k (from_real r)) borel s.to_real)"
      by(auto intro!: measure_kernel.bind_kernel_distr[symmetric,where Y=borel] space_ne measure_kernel.distr_measure_kernel[where Y=N] sfin.measure_kernel_comp)
    finally show ?thesis by simp
  qed
  also have "... = ?rhs"
    by(auto intro!: qbs_s_finite.bind_qbs[OF qbs_l_inverse_s_finite[OF refl assms(2)] _ s.s_finite_kernel_qbs_morphism[OF assms(3)] _  _ comp1,symmetric] s_finite_kernel.distr_s_finite_kernel[OF sfin.comp_measurable] simp: qbs_Mx_R) (simp add: qbs_l_inverse_def)
  finally show ?thesis .
qed

lemma qbs_l_inverse_bind:
  assumes "standard_borel_ne N" "s_finite_measure M" "k \<in> M  \<rightarrow>\<^sub>M prob_algebra N"
  shows "qbs_l_inverse (M \<bind> k) = qbs_l_inverse M \<bind> (\<lambda>x. qbs_l_inverse (k x))"
  by(auto simp: bind_kernel_bind[OF measurable_prob_algebraD[OF assms(3)],symmetric] prob_kernel_def' intro!: qbs_l_inverse_bind_kernel assms prob_kernel.s_finite_kernel_prob_kernel)

end

subsubsection \<open> PMF and SPMF \<close>
definition "qbs_pmf \<equiv> (\<lambda>p. qbs_l_inverse (measure_pmf p))"
definition "qbs_spmf \<equiv> (\<lambda>p. qbs_l_inverse (measure_spmf p))"

declare [[coercion qbs_pmf]]

lemma qbs_pmf_qbsP:
  fixes p :: "(_ :: countable) pmf"
  shows "qbs_pmf p \<in> qbs_space (monadP_qbs (count_space\<^sub>Q UNIV))"
  by(auto simp: qbs_pmf_def measure_to_qbs_cong_sets[of "count_space UNIV" "measure_pmf p",simplified] intro!: standard_borel_ne.qbs_l_inverse_in_space_monadP measure_pmf.prob_space_axioms)

lemma qbs_pmf_qbs[qbs]:
  fixes p :: "(_ :: countable) pmf"
  shows "qbs_pmf p \<in> qbs_space (monadM_qbs (count_space\<^sub>Q UNIV))"
  by (simp add: qbs_pmf_qbsP qbs_space_monadPM)

lemma qbs_spmf_qbs[qbs]:
  fixes q :: "(_ :: countable) spmf"
  shows "qbs_spmf q \<in> qbs_space (monadM_qbs (count_space\<^sub>Q UNIV))"
  by(auto simp: qbs_spmf_def measure_to_qbs_cong_sets[of "count_space UNIV" "measure_spmf q",simplified] intro!: standard_borel_ne.qbs_l_inverse_in_space_monadM subprob_space.s_finite_measure_subprob)

lemma [simp]:
  fixes p :: "(_ :: countable) pmf" and q :: "(_ :: countable) spmf"
  shows qbs_l_qbs_pmf:  "qbs_l (qbs_pmf p)  = measure_pmf p"
    and qbs_l_qbs_spmf: "qbs_l (qbs_spmf q) = measure_spmf q"
  by(auto simp: qbs_pmf_def qbs_spmf_def intro!: standard_borel_ne.qbs_l_qbs_l_inverse subprob_space.s_finite_measure_subprob measure_pmf.subprob_space_axioms)

lemma qbs_pmf_return_pmf:
  fixes x :: "_ :: countable"
  shows "qbs_pmf (return_pmf x) = return_qbs (count_space\<^sub>Q UNIV) x"
proof -
  note return_qbs_morphismP[qbs]
  show ?thesis
    by(auto intro!: inj_onD[OF qbs_l_inj_P[where X="count_space\<^sub>Q UNIV"]] return_cong qbs_pmf_qbsP simp: qbs_l_return_qbs return_pmf.rep_eq)
qed

lemma qbs_pmf_bind_pmf:
  fixes p :: "('a :: countable) pmf" and f :: "'a \<Rightarrow> ('b :: countable) pmf"
  shows "qbs_pmf (p \<bind> f) = qbs_pmf p \<bind> (\<lambda>x. qbs_pmf (f x))"
  by(auto simp: measure_pmf_bind qbs_pmf_def space_prob_algebra measure_pmf.prob_space_axioms intro!: standard_borel_ne.qbs_l_inverse_bind[where N="count_space UNIV"] prob_space.s_finite_measure_prob)

lemma qbs_pair_pmf:
  fixes p :: "('a :: countable) pmf" and q :: "('b :: countable) pmf"
  shows "qbs_pmf p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s qbs_pmf q = qbs_pmf (pair_pmf p q)"
proof(rule inj_onD[OF qbs_l_inj_P[of "count_space\<^sub>Q UNIV \<Otimes>\<^sub>Q count_space\<^sub>Q UNIV"]])
  show "qbs_l (qbs_pmf p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s qbs_pmf q) = qbs_l (qbs_pmf (pair_pmf p q))"
    by(simp add: measure_pair_pmf qbs_l_qbs_pair_measure[OF standard_borel_ne.standard_borel standard_borel_ne.standard_borel,of "count_space UNIV" "count_space UNIV"])
next
  note [qbs] = qbs_pmf_qbsP qbs_pair_measure_morphismP
  show "qbs_pmf p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s qbs_pmf q \<in> qbs_space (monadP_qbs (count_space\<^sub>Q UNIV \<Otimes>\<^sub>Q count_space\<^sub>Q UNIV))" "qbs_pmf (pair_pmf p q) \<in> qbs_space (monadP_qbs (count_space\<^sub>Q UNIV \<Otimes>\<^sub>Q count_space\<^sub>Q UNIV))"
    by auto (simp add: qbs_count_space_prod)
qed

subsubsection \<open> Density \<close>
lift_definition density_qbs :: "['a qbs_measure, 'a \<Rightarrow> ennreal] \<Rightarrow> 'a qbs_measure"
is "\<lambda>(X,\<alpha>,\<mu>) f. if f \<in> X \<rightarrow>\<^sub>Q qbs_borel then (X, \<alpha>, density \<mu> (f \<circ> \<alpha>)) else (X, SOME a. a \<in> qbs_Mx X, null_measure borel)"
proof safe
  fix X Y :: "'a quasi_borel"
  fix \<alpha> \<beta> \<mu> \<nu> and f :: "_ \<Rightarrow> ennreal"
  assume 1:"qbs_s_finite_eq (X, \<alpha>, \<mu>) (Y, \<beta>, \<nu>)"
  then interpret qs: pair_qbs_s_finite X \<alpha> \<mu> \<beta> \<nu>
    using qbs_s_finite_eq_dest[OF 1] by(simp add: pair_qbs_s_finite_def)
  have [simp]:"(SOME a. a \<in> qbs_Mx X) \<in> qbs_Mx X" "(SOME a. a \<in> qbs_Mx Y) \<in> qbs_Mx X"
    using qs.pq1.in_Mx by(simp_all only: some_in_eq qbs_s_finite_eq_dest[OF 1]) blast+
  {
    assume "f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
    then have "qbs_s_finite_eq (X, \<alpha>, density \<mu> (f \<circ> \<alpha>)) (Y, \<beta>, density \<nu> (f \<circ> \<beta>))"
      by(auto simp: qbs_s_finite_eq_def lr_adjunction_correspondence density_distr[symmetric] comp_def qbs_s_finite_eq_dest[OF 1] qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def qs.pq1.mu_sets qs.pq2.mu_sets AE_distr_iff intro!: qs.pq1.s_finite_measure_density qs.pq2.s_finite_measure_density)
  }
  moreover have "f \<in> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> f \<notin> Y \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> qbs_s_finite_eq (X, \<alpha>, density \<mu> (f \<circ> \<alpha>)) (Y, (SOME a. a \<in> qbs_Mx Y), null_measure borel)"
       "f \<notin> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> f \<in> Y \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> qbs_s_finite_eq (X, (SOME a. a \<in> qbs_Mx X), null_measure borel) (Y, \<beta>, density \<nu> (f \<circ> \<beta>))"
       "f \<notin> X \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> f \<notin> Y \<rightarrow>\<^sub>Q qbs_borel \<Longrightarrow> qbs_s_finite_eq (X, (SOME a. a \<in> qbs_Mx X), null_measure borel) (Y, (SOME a. a \<in> qbs_Mx Y), null_measure borel)"
    by(auto simp: qbs_s_finite_eq_dest[OF 1] qbs_s_finite_eq_def qbs_s_finite_def in_Mx_def qbs_s_finite_axioms_def distr_return null_measure_distr intro!: subprob_space.s_finite_measure_subprob subprob_spaceI)
  ultimately show "qbs_s_finite_eq (if f \<in> X \<rightarrow>\<^sub>Q borel\<^sub>Q then (X, \<alpha>, density \<mu> (f \<circ> \<alpha>)) else (X, SOME aa. aa \<in> qbs_Mx X, null_measure borel)) (if f \<in> Y \<rightarrow>\<^sub>Q borel\<^sub>Q then (Y, \<beta>, density \<nu> (f \<circ> \<beta>)) else (Y, SOME a. a \<in> qbs_Mx Y, null_measure borel))"
    by auto
qed

lemma(in qbs_s_finite)
  assumes "f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows density_qbs:"density_qbs \<lbrakk>X,\<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n f = \<lbrakk>X, \<alpha>, density \<mu> (f \<circ> \<alpha>)\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"
    and density_qbs_s_finite: "qbs_s_finite X \<alpha> (density \<mu> (f \<circ> \<alpha>))"
  using assms by(auto simp: density_qbs.abs_eq  qbs_s_finite_def in_Mx_def lr_adjunction_correspondence qbs_s_finite_axioms_def mu_sets AE_distr_iff intro!: s_finite_measure_density)

lemma density_qbs_density_qbs_eq:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs X)" "f \<in>  X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "density_qbs (density_qbs s f) g = density_qbs s (\<lambda>x. f x * g x)"
proof -
  from rep_qbs_space_monadM[OF assms(1)] obtain \<alpha> \<mu>
    where hs: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>" by metis
  then interpret qbs_s_finite X \<alpha> \<mu> by simp
  show ?thesis
    using assms(2,3) by(simp add: hs(1) density_qbs[OF assms(2)] qbs_s_finite.density_qbs[OF density_qbs_s_finite[OF assms(2)] assms(3)] density_qbs lr_adjunction_correspondence density_density_eq) (simp add: comp_def)
qed

lemma qbs_l_density_qbs:
  assumes "s \<in> qbs_space (monadM_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "qbs_l (density_qbs s f) = density (qbs_l s) f"
proof -
  from rep_qbs_space_monadM[OF assms(1)]
  obtain \<alpha> \<mu> where s: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
    by metis
  then interpret qbs_s_finite X \<alpha> \<mu> by simp
  show ?thesis
    using assms(2) by(simp add: s(1) qbs_l qbs_s_finite.density_qbs[OF s(2) assms(2)] qbs_s_finite.qbs_l[OF qbs_s_finite.density_qbs_s_finite[OF s(2) assms(2)]] density_distr lr_adjunction_correspondence) (simp add: comp_def)
qed

corollary qbs_l_density_qbs_indicator:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs X)" "qbs_pred X P"
  shows "qbs_l (density_qbs s (indicator {x\<in>qbs_space X. P x})) (qbs_space X) = qbs_l s {x\<in>qbs_space X. P x} "
proof -
  have 1[measurable]: "{x \<in> qbs_space X. P x} \<in> sets (qbs_to_measure X)"
    by (metis qbs_pred_iff_sets space_L assms(2))
  have 2[qbs]: "indicator {x \<in> qbs_space X. P x} \<in> X \<rightarrow>\<^sub>Q qbs_borel"
    by(rule indicator_qbs_morphism'') qbs
  show ?thesis
    using assms(2) by(auto simp: qbs_l_density_qbs[of _ X] emeasure_density[of "indicator {x\<in>space (qbs_to_measure X). P x}" "qbs_l s",OF _ sets.top,simplified measurable_qbs_l'[OF assms(1)],OF borel_measurable_indicator[OF predE],simplified space_L space_qbs_l_in[OF assms(1)]] qbs_pred_iff_measurable_pred nn_set_integral_space[of "qbs_l s",simplified space_qbs_l_in[OF assms(1)]] nn_integral_indicator[of _ "qbs_l s",simplified sets_qbs_l[OF assms(1)]])
qed

lemma qbs_nn_integral_density_qbs:
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<integral>\<^sup>+\<^sub>Q x. g x \<partial>(density_qbs s f)) = (\<integral>\<^sup>+\<^sub>Q x. f x * g x \<partial>s)"
  by(auto simp: qbs_nn_integral_def2_l qbs_l_density_qbs[of _ X] measurable_qbs_l'[OF assms(1)] lr_adjunction_correspondence[symmetric] intro!:nn_integral_density)

lemma qbs_integral_density_qbs:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" and f :: "'a \<Rightarrow> real"
  assumes [qbs]:"s \<in> qbs_space (monadM_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
      and "AE\<^sub>Q x in s. f x \<ge> 0"
    shows "(\<integral>\<^sub>Q x. g x \<partial>(density_qbs s f)) = (\<integral>\<^sub>Q x. f x *\<^sub>R g x \<partial>s)"
  using assms(4) by(auto simp: qbs_integral_def2_l qbs_l_density_qbs[of _ X] measurable_qbs_l'[OF assms(1)] lr_adjunction_correspondence[symmetric] AEq_qbs_l intro!: integral_density)

lemma density_qbs_morphism[qbs]: "density_qbs \<in> monadM_qbs X \<rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q qbs_borel) \<Rightarrow>\<^sub>Q monadM_qbs X"
proof(rule curry_preserves_morphisms[OF pair_qbs_morphismI])
  fix \<gamma> and \<beta> :: "_ \<Rightarrow> _ \<Rightarrow> ennreal"
  assume h:"\<gamma> \<in> qbs_Mx (monadM_qbs X)"  "\<beta> \<in> qbs_Mx (X \<Rightarrow>\<^sub>Q qbs_borel)"
  hence [qbs]: "\<gamma> \<in> qbs_borel \<rightarrow>\<^sub>Q monadM_qbs X" "\<beta> \<in> qbs_borel \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q qbs_borel"
    by(simp_all add: qbs_Mx_is_morphisms)
  from rep_qbs_Mx_monadM[OF h(1)] obtain \<alpha> k where hk:
   "\<gamma> = (\<lambda>r. \<lbrakk>X, \<alpha>, k r\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n)" "\<alpha> \<in> qbs_Mx X" "s_finite_kernel borel borel k" "\<And>r. qbs_s_finite X \<alpha> (k r)"
    by metis
  then interpret a: in_Mx X \<alpha> by(simp add: in_Mx_def)
  have [measurable]: "(\<lambda>(x, y). \<beta> x (\<alpha> y)) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
  proof -
    have "(\<lambda>(x, y). \<beta> x (\<alpha> y)) \<in> qbs_borel \<Otimes>\<^sub>Q qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
      by simp
    thus ?thesis
      by(simp add: lr_adjunction_correspondence qbs_borel_prod borel_prod)
  qed
  have [simp]:"density_qbs (\<gamma> r) (\<beta> r) = \<lbrakk>X, \<alpha>, density (k r) (\<beta> r \<circ> \<alpha>)\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n " for r
    using hk(4) by(auto simp add: hk(1) density_qbs.abs_eq[OF qbs_s_finite.qbs_s_finite_eq_refl[OF hk(4)]])
  show "(\<lambda>r. density_qbs (fst (\<gamma> r,\<beta> r)) (snd (\<gamma> r,\<beta> r))) \<in> qbs_Mx (monadM_qbs X)"
    by(auto simp: monadM_qbs_Mx comp_def intro!: exI[where x=\<alpha>] exI[where x="\<lambda>r. density (k r) (\<beta> r \<circ> \<alpha>)"] s_finite_kernel.density_s_finite_kernel[OF hk(3)])
qed

lemma density_qbs_cong_AE:
  assumes [qbs]: "s \<in> qbs_space (monadM_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
      and "AE\<^sub>Q x in s. f x = g x"
    shows "density_qbs s f = density_qbs s g"
proof(rule inj_onD[OF qbs_l_inj[of X]])
  show "qbs_l (density_qbs s f) = qbs_l (density_qbs s g)"
    using assms(4) by(auto simp: qbs_l_density_qbs[of _ X] measurable_qbs_l'[OF assms(1)] AEq_qbs_l lr_adjunction_correspondence[symmetric] intro!: density_cong)
qed simp_all

corollary density_qbs_cong:
  assumes [qbs]: "s \<in> qbs_space (monadM_qbs X)" "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> X \<rightarrow>\<^sub>Q qbs_borel"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
    shows "density_qbs s f = density_qbs s g"
  by(auto intro!: density_qbs_cong_AE[of _ X] AEq_I2[of _ X] assms(4))

lemma density_qbs_1[simp]: "density_qbs s (\<lambda>x. 1) = s"
proof -
  obtain X where s[qbs]: "s \<in> qbs_space (monadM_qbs X)"
    using in_qbs_space_of by blast
  show ?thesis
    by(auto intro!: inj_onD[OF qbs_l_inj _ _ s] simp: qbs_l_density_qbs[of _ X] density_1)
qed

lemma pair_density_qbs:
  assumes [qbs]: "p \<in> qbs_space (monadM_qbs X)" "q \<in> qbs_space (monadM_qbs Y)"
      and [qbs]: "f \<in> X \<rightarrow>\<^sub>Q qbs_borel" "g \<in> Y \<rightarrow>\<^sub>Q qbs_borel"
    shows "density_qbs p f \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s density_qbs q g = density_qbs (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>(x,y). f x * g y)"
proof(safe intro!: qbs_measure_eqI[of _ "X \<Otimes>\<^sub>Q Y"])
  fix h :: "_ \<Rightarrow> ennreal"
  assume h[qbs]:"h \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q borel\<^sub>Q"
  show "(\<integral>\<^sup>+\<^sub>Q z. h z \<partial>(density_qbs p f \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s density_qbs q g)) = (\<integral>\<^sup>+\<^sub>Q z. h z \<partial>(density_qbs (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>(x, y). f x * g y)))" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y. h (x, y) \<partial>density_qbs q g \<partial>density_qbs p f)"
      by(simp add: qbs_nn_integral_Fubini_fst[of _ X _ Y])
    also have "... = (\<integral>\<^sup>+\<^sub>Q x. \<integral>\<^sup>+\<^sub>Q y. g y * h (x, y) \<partial>q \<partial>density_qbs p f)"
      by(auto intro!: qbs_nn_integral_cong[of _ X] simp: qbs_nn_integral_density_qbs[of _ Y])
    also have "... = ?rhs"
      by(auto simp add: qbs_nn_integral_density_qbs[of _ X] qbs_nn_integral_density_qbs[of _ "X \<Otimes>\<^sub>Q Y"] split_beta' qbs_nn_integral_Fubini_fst[of _ X _ Y,symmetric] qbs_nn_integral_cmult[of _ Y] mult.assoc intro!: qbs_nn_integral_cong[of _ X])
    finally show ?thesis .
  qed
qed simp_all

subsubsection \<open> Normalization \<close>
definition normalize_qbs :: "'a qbs_measure \<Rightarrow> 'a qbs_measure" where
"normalize_qbs s \<equiv> (let X = qbs_space_of s;
                        r = qbs_l s (qbs_space X) in
                    if r \<noteq> 0 \<and> r \<noteq> \<infinity> then density_qbs s (\<lambda>x. 1 / r)
                    else qbs_null_measure X)"

lemma
  assumes "s \<in> qbs_space (monadM_qbs X)"
  shows normalize_qbs: "qbs_l s (qbs_space X) \<noteq> 0 \<Longrightarrow> qbs_l s (qbs_space X) \<noteq> \<infinity> \<Longrightarrow> normalize_qbs s = density_qbs s (\<lambda>x. 1 /  emeasure (qbs_l s) (qbs_space X))"
    and normalize_qbs0: "qbs_l s (qbs_space X) = 0 \<Longrightarrow> normalize_qbs s = qbs_null_measure X"
    and normalize_qbsinfty: "qbs_l s (qbs_space X) = \<infinity> \<Longrightarrow> normalize_qbs s = qbs_null_measure X"
  by(auto simp: qbs_space_of_in[OF assms(1)] normalize_qbs_def)

lemma normalize_qbs_prob:
  assumes "s \<in> qbs_space (monadM_qbs X)" "qbs_l s (qbs_space X) \<noteq> 0" "qbs_l s (qbs_space X) \<noteq> \<infinity>"
  shows "normalize_qbs s \<in> qbs_space (monadP_qbs X)"
  unfolding normalize_qbs[OF assms]
proof -
  obtain \<alpha> \<mu>
    where hs: "s = \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "qbs_s_finite X \<alpha> \<mu>"
    using rep_qbs_space_monadM assms(1) by meson
  interpret qs: qbs_s_finite X \<alpha> \<mu> by fact
  have "density_qbs s (\<lambda>x. 1 / emeasure (qbs_l s) (qbs_space X)) = density_qbs \<lbrakk>X, \<alpha>, \<mu>\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n (\<lambda>x. 1 / emeasure (qbs_l s) (qbs_space X))"
    by(simp add: hs)
  also have "... \<in> qbs_space (monadP_qbs X)"
    by(auto simp add: qs.density_qbs monadP_qbs_space qbs_s_finite.qbs_l[OF qs.density_qbs_s_finite,of "\<lambda>x. 1 / emeasure (qbs_l s) (qbs_space X)",simplified] qbs_s_finite.qbs_space_of[OF qs.density_qbs_s_finite,of "\<lambda>x. 1 / emeasure (qbs_l s) (qbs_space X)",simplified] intro!: prob_space.prob_space_distr, auto intro!: prob_spaceI simp: emeasure_density)
      (insert assms(2,3),auto simp: hs qs.qbs_l emeasure_distr emeasure_distr[of _ _ "qbs_to_measure X",OF _ sets.top,simplified space_L] divide_eq_1_ennreal ennreal_divide_times)
  finally show "density_qbs s (\<lambda>x. 1 / emeasure (qbs_l s) (qbs_space X)) \<in> qbs_space (monadP_qbs X)" .
qed

lemma normalize_qbs_morphism[qbs]: "normalize_qbs \<in> monadM_qbs X \<rightarrow>\<^sub>Q monadM_qbs X"
proof -
  have "(if emeasure (qbs_l s) (qbs_space X) \<noteq> 0 \<and> emeasure (qbs_l s) (qbs_space X) \<noteq> \<infinity> then density_qbs s (\<lambda>x. 1 / emeasure (qbs_l s) (qbs_space X)) else qbs_null_measure X) = normalize_qbs s"  (is "?f s = _") if s:"s \<in> qbs_space (monadM_qbs X)" for s
    by(simp add: qbs_space_of_in[OF s] normalize_qbs_def)
  moreover have "(\<lambda>s. ?f s) \<in> monadM_qbs X \<rightarrow>\<^sub>Q monadM_qbs X"
  proof(cases "qbs_space X = {}")
    case True
    then show ?thesis
      by(simp add: qbs_morphism_from_empty  monadM_qbs_empty_iff[of X])
  next
    case X:False
    have [qbs]:"(\<lambda>s. emeasure (qbs_l s) (qbs_space X)) \<in> monadM_qbs X \<rightarrow>\<^sub>Q qbs_borel"
      by(rule qbs_l_morphism[OF sets.top[of "qbs_to_measure X",simplified space_L]])
    have [qbs]: "qbs_null_measure X \<in> qbs_space (monadM_qbs X)"
      by(auto intro!: qbs_null_measure_in_Mx X)
    have [qbs]: "(\<lambda>s x. 1 / emeasure (qbs_l s) (qbs_space X)) \<in> monadM_qbs X \<rightarrow>\<^sub>Q X \<Rightarrow>\<^sub>Q qbs_borel"
      by(rule arg_swap_morphism) simp
    show ?thesis
      by qbs
  qed
  ultimately show ?thesis
    by(simp cong: qbs_morphism_cong)
qed

lemma normalize_qbs_morphismP:
  assumes [qbs]:"s \<in> X \<rightarrow>\<^sub>Q monadM_qbs Y"
      and "\<And>x. x \<in> qbs_space X \<Longrightarrow> qbs_l (s x) (qbs_space Y) \<noteq> 0" "\<And>x. x \<in> qbs_space X \<Longrightarrow> qbs_l (s x) (qbs_space Y) \<noteq> \<infinity>"
    shows "(\<lambda>x. normalize_qbs (s x)) \<in> X \<rightarrow>\<^sub>Q monadP_qbs Y"
  by(rule qbs_morphism_monadPI'[OF normalize_qbs_prob]) (use assms(2,3) qbs_morphism_space[OF assms(1)] in auto)

lemma normalize_qbs_monadP_ident:
  assumes "s \<in> qbs_space (monadP_qbs X)"
  shows "normalize_qbs s = s"
  using normalize_qbs[OF qbs_space_monadPM[OF assms]] prob_space.emeasure_space_1[OF qbs_l_prob_space[OF assms]]
  by(auto simp: space_qbs_l_in[OF qbs_space_monadPM[OF assms]] intro!: inj_onD[OF qbs_l_inj_P _ _ assms])

corollary normalize_qbs_idenpotent: "normalize_qbs (normalize_qbs s) = normalize_qbs s"
proof -
  obtain X where s[qbs]: "s \<in> qbs_space (monadM_qbs X)"
    using in_qbs_space_of by blast
  then have X: "qbs_space X \<noteq> {}"
    by (metis qbs_s_space_of_not_empty qbs_space_of_in)
  then obtain x where x:"x \<in> qbs_space X" by auto
  consider "qbs_l s (qbs_space X) = 0" | "qbs_l s (qbs_space X) = \<top>" | "qbs_l s (qbs_space X) \<noteq> 0"  "qbs_l s (qbs_space X) \<noteq> \<top>"
    by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using normalize_qbs0[OF qbs_null_measure_in_Mx[OF X]]
      by(simp add: normalize_qbs0[OF s] qbs_null_measure_null_measure[OF X])
  next
    case 2
    then show ?thesis
      using normalize_qbs0[OF qbs_null_measure_in_Mx[OF X]]
      by(simp add: normalize_qbsinfty[OF s] qbs_null_measure_null_measure[OF X])
  next
    case 3
    have "normalize_qbs s \<in> qbs_space (monadP_qbs X)"
      by(rule qbs_morphism_space[OF normalize_qbs_morphismP[of "\<lambda>x. s"],of X X x]) (auto simp: 3 x)
    then show ?thesis
      by(simp add: normalize_qbs_monadP_ident)
  qed
qed

subsubsection \<open> Product Measures \<close>
definition PiQ_measure :: "['a set, 'a \<Rightarrow> 'b qbs_measure] \<Rightarrow> ('a \<Rightarrow> 'b) qbs_measure" where
"PiQ_measure \<equiv> (\<lambda>I si. if (\<forall>i\<in>I. \<exists>Mi. standard_borel_ne Mi \<and> si i \<in> qbs_space (monadM_qbs (measure_to_qbs Mi)))
                        then if countable I \<and> (\<forall>i\<in>I. prob_space (qbs_l (si i))) then qbs_l_inverse (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))
                             else if finite I \<and> (\<forall>i\<in>I. sigma_finite_measure (qbs_l (si i))) then qbs_l_inverse (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))
                             else qbs_null_measure (\<Pi>\<^sub>Q i\<in>I. qbs_space_of (si i))
                        else qbs_null_measure (\<Pi>\<^sub>Q i\<in>I. qbs_space_of (si i)))"

syntax
  "_PiQ_measure" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a qbs_measure \<Rightarrow> ('i => 'a) qbs_measure"  ("(3\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s _\<in>_./ _)"  10)
translations
  "\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s x\<in>I. X" == "CONST PiQ_measure I (\<lambda>x. X)"

context
  fixes I and Mi
  assumes standard_borel_ne:"\<And>i. i \<in> I \<Longrightarrow> standard_borel_ne (Mi i)"
begin

context
  assumes countableI:"countable I"
begin

interpretation sb:standard_borel_ne "\<Pi>\<^sub>M i\<in>I. (borel :: real measure)"
  by (simp add: countableI product_standard_borel_ne)

interpretation sbM: standard_borel_ne "\<Pi>\<^sub>M i\<in>I. Mi i"
  by (simp add: countableI standard_borel_ne product_standard_borel_ne)

lemma
  assumes "\<And>i. i \<in> I \<Longrightarrow> si i \<in> qbs_space (monadP_qbs (measure_to_qbs (Mi i)))"
      and "\<And>i. i \<in> I \<Longrightarrow> si i = \<lbrakk>measure_to_qbs (Mi i), \<alpha> i, \<mu> i\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n" "\<And>i. i \<in> I \<Longrightarrow> qbs_prob (measure_to_qbs (Mi i)) (\<alpha> i) (\<mu> i)"
    shows PiQ_measure_prob_eq:  "(\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s i\<in>I. si i) = \<lbrakk>measure_to_qbs (\<Pi>\<^sub>M i\<in>I. Mi i), sbM.from_real, distr (\<Pi>\<^sub>M i\<in>I. qbs_l (si i)) borel sbM.to_real\<rbrakk>\<^sub>s\<^sub>f\<^sub>i\<^sub>n"  (is "_ = ?rhs")
      and PiQ_measure_qbs_prob: "qbs_prob (measure_to_qbs (\<Pi>\<^sub>M i\<in>I. Mi i)) sbM.from_real (distr (\<Pi>\<^sub>M i\<in>I. qbs_l (si i)) borel sbM.to_real)" (is "?qbsprob")
proof -
  have [measurable_cong,simp]: "prob_space (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))" "sets (\<Pi>\<^sub>M i\<in>I. qbs_l (si i)) = sets (\<Pi>\<^sub>M i\<in>I. Mi i)"
    using sets_qbs_l[OF assms(1)[THEN qbs_space_monadPM]] standard_borel.lr_sets_ident[OF standard_borel_ne.standard_borel[OF standard_borel_ne]]
    by(auto cong: sets_PiM_cong intro!: prob_space_PiM qbs_l_prob_space assms(1))
  show ?qbsprob
    by(auto simp: pair_qbs_s_finite_def intro!: qbs_prob.qbs_s_finite sbM.qbs_l_inverse_qbs_prob)
  have "(\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s i\<in>I. si i) = qbs_l_inverse (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))"
    using countableI assms(1)[THEN qbs_space_monadPM] qbs_l_prob_space[OF assms(1)] standard_borel_ne by(auto simp: PiQ_measure_def)
  also have "... = ?rhs"
    by(auto intro!: sbM.qbs_l_inverse_def2 prob_space.s_finite_measure_prob cong: sets_PiM_cong[OF refl])
  finally show "(\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s i\<in>I. si i) = ?rhs" .
qed

lemma qbs_l_PiQ_measure_prob:
  assumes "\<And>i. i \<in> I \<Longrightarrow> si i \<in> qbs_space (monadP_qbs (measure_to_qbs (Mi i)))"
  shows "qbs_l (\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s i\<in>I. si i) = (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))"
proof -
  have "qbs_l (\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s i\<in>I. si i) = qbs_l (qbs_l_inverse (\<Pi>\<^sub>M i\<in>I. qbs_l (si i)))"
    using countableI assms(1)[THEN qbs_space_monadPM] qbs_l_prob_space[OF assms(1)] standard_borel_ne by(auto simp: PiQ_measure_def)
  also have "... = (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))"
    using sets_qbs_l[OF assms(1)[THEN qbs_space_monadPM]] standard_borel.lr_sets_ident[OF standard_borel_ne.standard_borel[OF standard_borel_ne]]
    by(auto intro!: sbM.qbs_l_qbs_l_inverse_prob prob_space_PiM qbs_l_prob_space[OF assms(1)] cong: sets_PiM_cong)
  finally show ?thesis .
qed

end

context
  assumes finI: "finite I"
begin

interpretation sb:standard_borel_ne "\<Pi>\<^sub>M i\<in>I. (borel :: real measure)"
  by (simp add: finI product_standard_borel_ne countable_finite)

interpretation sbM: standard_borel_ne "\<Pi>\<^sub>M i\<in>I. Mi i"
  by (simp add: countable_finite finI standard_borel_ne product_standard_borel_ne)

lemma qbs_l_PiQ_measure:
  assumes "\<And>i. i \<in> I \<Longrightarrow> si i \<in> qbs_space (monadM_qbs (measure_to_qbs (Mi i)))"
      and "\<And>i. i \<in> I \<Longrightarrow> sigma_finite_measure (qbs_l (si i))"
    shows "qbs_l (\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s i\<in>I. si i) = (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))"
proof -
  have [simp]: "s_finite_measure (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))"
  proof -
    have "(\<Pi>\<^sub>M i\<in>I. qbs_l (si i)) = (\<Pi>\<^sub>M i\<in>I. if i \<in> I then qbs_l (si i) else null_measure (count_space UNIV))"
      by(simp cong: PiM_cong)
    also have "s_finite_measure ..."
      by(auto intro!: sigma_finite_measure.s_finite_measure product_sigma_finite.sigma_finite finI simp: product_sigma_finite_def assms(2)) (auto intro!: finite_measure.sigma_finite_measure finite_measureI)
    finally show ?thesis .
  qed
  have "qbs_l (\<Pi>\<^sub>Q\<^sub>m\<^sub>e\<^sub>a\<^sub>s i\<in>I. si i) = qbs_l (qbs_l_inverse (\<Pi>\<^sub>M i\<in>I. qbs_l (si i)))"
    using finI assms(1) assms(2) standard_borel_ne by(fastforce simp: PiQ_measure_def)
  also have "... = (\<Pi>\<^sub>M i\<in>I. qbs_l (si i))"
    using sets_qbs_l[OF assms(1)] standard_borel.lr_sets_ident[OF standard_borel_ne.standard_borel[OF standard_borel_ne]]
    by(auto intro!: sbM.qbs_l_qbs_l_inverse  prob_space_PiM cong: sets_PiM_cong)
  finally show ?thesis .
qed


end

end
subsection \<open>Measures\<close>
subsubsection \<open> The Lebesgue Measure \<close>
definition lborel_qbs ("lborel\<^sub>Q") where "lborel_qbs \<equiv> qbs_l_inverse lborel"

lemma lborel_qbs_qbs[qbs]: "lborel_qbs \<in> qbs_space (monadM_qbs qbs_borel)"
  by(auto simp: lborel_qbs_def measure_to_qbs_cong_sets[OF sets_lborel,symmetric] intro!: standard_borel_ne.qbs_l_inverse_in_space_monadM lborel.s_finite_measure_axioms)

lemma qbs_l_lborel_qbs[simp]: "qbs_l lborel\<^sub>Q = lborel"
  by(auto intro!: standard_borel_ne.qbs_l_qbs_l_inverse lborel.s_finite_measure_axioms simp: lborel_qbs_def)

corollary
  shows qbs_integral_lborel: "(\<integral>\<^sub>Q x. f x \<partial>lborel_qbs) = (\<integral>x. f x \<partial>lborel)"
    and qbs_nn_integral_lborel: "(\<integral>\<^sup>+\<^sub>Q x. f x \<partial>lborel_qbs) = (\<integral>\<^sup>+x. f x \<partial>lborel)"
  by(simp_all add: qbs_integral_def2_l qbs_nn_integral_def2_l)


lemma(in standard_borel_ne) measure_with_args_morphism:
  assumes "s_finite_kernel X M k"
  shows "qbs_l_inverse \<circ> k \<in> measure_to_qbs X \<rightarrow>\<^sub>Q monadM_qbs (measure_to_qbs M)"
proof(safe intro!: qbs_morphismI)
  fix \<alpha> :: "real \<Rightarrow> _"
  assume "\<alpha> \<in> qbs_Mx (measure_to_qbs X)"
  then have h[measurable]:"\<alpha> \<in> borel \<rightarrow>\<^sub>M X"
    by(simp add: qbs_Mx_R)
  interpret s:s_finite_kernel X M k by fact
  have 1: "\<And>r. sets (k (\<alpha> r)) = sets M" "\<And>r. s_finite_measure (k (\<alpha> r))"
    using measurable_space[OF h] s.kernel_sets by(auto intro!: s.image_s_finite_measure)
  show "qbs_l_inverse \<circ> k \<circ> \<alpha> \<in> qbs_Mx (monadM_qbs (measure_to_qbs M))"
    by(auto intro!: exI[where x=from_real] exI[where x="(\<lambda>r. distr (k (\<alpha> r)) borel to_real)"] s_finite_kernel.comp_measurable[OF s_finite_kernel.distr_s_finite_kernel[OF assms]] simp: monadM_qbs_Mx qbs_Mx_R qbs_l_inverse_def2[OF 1] comp_def)
qed

lemma(in standard_borel_ne) measure_with_args_morphismP:
  assumes [measurable]:"\<mu> \<in> X \<rightarrow>\<^sub>M prob_algebra M"
  shows "qbs_l_inverse \<circ> \<mu> \<in> measure_to_qbs X \<rightarrow>\<^sub>Q monadP_qbs (measure_to_qbs M)"
  by(rule qbs_morphism_monadPI'[OF _ measure_with_args_morphism])
    (insert measurable_space[OF assms], auto simp: qbs_space_R space_prob_algebra prob_kernel_def' intro!: qbs_l_inverse_in_space_monadP prob_kernel.s_finite_kernel_prob_kernel)

subsubsection \<open> Counting Measure \<close>
abbreviation "counting_measure_qbs A \<equiv> qbs_l_inverse (count_space A)"

lemma qbs_nn_integral_count_space_nat:
  fixes f :: "nat \<Rightarrow> ennreal"
  shows "(\<integral>\<^sup>+\<^sub>Q i. f i \<partial>counting_measure_qbs UNIV) = (\<Sum>i. f i)"
  by(simp add: standard_borel_ne.qbs_l_qbs_l_inverse[OF _ refl sigma_finite_measure.s_finite_measure[OF sigma_finite_measure_count_space]] qbs_nn_integral_def2_l nn_integral_count_space_nat)

subsubsection \<open> Normal Distribution \<close>
lemma qbs_normal_distribution_qbs: "(\<lambda>\<mu> \<sigma>. density_qbs lborel\<^sub>Q (normal_density \<mu> \<sigma>)) \<in> qbs_borel \<Rightarrow>\<^sub>Q qbs_borel \<Rightarrow>\<^sub>Q monadM_qbs qbs_borel"
  by simp

lemma qbs_l_qbs_normal_distribution[simp]: "qbs_l (density_qbs lborel\<^sub>Q (normal_density \<mu> \<sigma>)) = density lborel (normal_density \<mu> \<sigma>)"
  by(auto simp: qbs_l_density_qbs[of _ qbs_borel])

lemma qbs_normal_distribution_P: "\<sigma> > 0 \<Longrightarrow> density_qbs lborel\<^sub>Q (normal_density \<mu> \<sigma>) \<in> qbs_space (monadP_qbs qbs_borel)"
  by(auto simp: monadP_qbs_def sub_qbs_space prob_space_normal_density)

lemma qbs_normal_distribution_integral:
 "(\<integral>\<^sub>Q x. f x \<partial> (density_qbs lborel\<^sub>Q (normal_density \<mu> \<sigma>))) = (\<integral> x. f x \<partial> (density lborel (\<lambda>x. ennreal (normal_density \<mu> \<sigma> x))))"
  by(auto simp: qbs_integral_def2_l)

lemma qbs_normal_distribution_expectation:
  assumes [measurable]:"f \<in> borel_measurable borel" and [arith]: "\<sigma> > 0"
  shows "(\<integral>\<^sub>Q x. f x \<partial> (density_qbs lborel\<^sub>Q (normal_density \<mu> \<sigma>))) = (\<integral> x. normal_density \<mu> \<sigma> x * f x \<partial> lborel)"
  by(simp add: qbs_normal_distribution_integral integral_real_density integral_density)

lemma qbs_normal_posterior:
  assumes [arith]: "\<sigma> > 0" "\<sigma>' > 0"
  shows "normalize_qbs (density_qbs (density_qbs lborel\<^sub>Q (normal_density \<mu> \<sigma>)) (normal_density \<mu>' \<sigma>')) = density_qbs lborel\<^sub>Q (normal_density ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)))" (is "?lhs = ?rhs")
proof -
  have 0: "\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2) > 0" "sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) > 0"
    by (simp_all add: power2_eq_square sum_squares_gt_zero_iff)
  have 1:"qbs_l (density_qbs lborel\<^sub>Q (\<lambda>x. ennreal (1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- ((\<mu> - \<mu>')\<^sup>2 / (2 * \<sigma>\<^sup>2 + 2 * \<sigma>'\<^sup>2))) * normal_density ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x))) UNIV = ennreal (exp (- ((\<mu> - \<mu>')\<^sup>2 / (2 * \<sigma>\<^sup>2 + 2 * \<sigma>'\<^sup>2))) / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)))"
    using prob_space.emeasure_space_1[OF prob_space_normal_density[OF 0(1)]] by(auto simp add: qbs_l_density_qbs[of _ qbs_borel] emeasure_density ennreal_mult' nn_integral_cmult simp del: times_divide_eq_left) (simp add: ennreal_mult'[symmetric])
  have "?lhs = normalize_qbs (density_qbs lborel\<^sub>Q (\<lambda>x. ennreal (1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- ((\<mu> - \<mu>')\<^sup>2 / (2 * \<sigma>\<^sup>2 + 2 * \<sigma>'\<^sup>2))) * normal_density ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x)))"
    by(simp add: density_qbs_density_qbs_eq[of _ qbs_borel] ennreal_mult'[symmetric] normal_density_times del: times_divide_eq_left)
  also have "... = density_qbs (density_qbs lborel\<^sub>Q (\<lambda>x. ennreal (1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- ((\<mu> - \<mu>')\<^sup>2 / (2 * \<sigma>\<^sup>2 + 2 * \<sigma>'\<^sup>2))) * normal_density ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x))) (\<lambda>x. 1 / emeasure (qbs_l (density_qbs lborel\<^sub>Q (\<lambda>x. ennreal (1 / sqrt (2 * pi * (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) * exp (- ((\<mu> - \<mu>')\<^sup>2 / (2 * \<sigma>\<^sup>2 + 2 * \<sigma>'\<^sup>2))) * normal_density ((\<mu> * \<sigma>'\<^sup>2 + \<mu>' * \<sigma>\<^sup>2) / (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) (\<sigma> * \<sigma>' / sqrt (\<sigma>\<^sup>2 + \<sigma>'\<^sup>2)) x)))) (qbs_space borel\<^sub>Q))"
    by(rule normalize_qbs) (simp_all add: 1 del: times_divide_eq_left)
  also have "... = ?rhs"
    by(simp add: 1 density_qbs_density_qbs_eq[of _ qbs_borel] del: times_divide_eq_left, auto intro!: density_qbs_cong[of _ qbs_borel])
      (insert 0, auto simp: ennreal_1[symmetric] ennreal_mult'[symmetric] divide_ennreal normal_density_def  simp del: ennreal_1)
  finally show ?thesis .
qed

subsubsection \<open> Uniform Distribution \<close>
definition uniform_qbs :: "'a qbs_measure \<Rightarrow> 'a set \<Rightarrow> 'a qbs_measure" where
"uniform_qbs \<equiv> (\<lambda>s A. qbs_l_inverse (uniform_measure (qbs_l s) A))"

lemma(in standard_borel_ne) qbs_l_uniform_qbs':
  assumes "sets \<mu> = sets M" "s_finite_measure \<mu>" "\<mu> A \<noteq> 0"
  shows "qbs_l (uniform_qbs (qbs_l_inverse \<mu>) A) = uniform_measure \<mu> A" (is "?lhs = ?rhs")
proof -
  have "?lhs = qbs_l (qbs_l_inverse (uniform_measure \<mu> A))"
    by(simp add: qbs_l_qbs_l_inverse[OF assms(1,2)] uniform_qbs_def)
  also have "... = ?rhs"
  proof(rule qbs_l_qbs_l_inverse)
    consider "\<mu> A = \<infinity>" | "\<mu> A \<noteq> \<infinity>" by auto
    then show "s_finite_measure (uniform_measure \<mu> A)"
    proof cases
      case 1
      have A[measurable]: "A \<in> sets \<mu>"
        using assms(3) emeasure_notin_sets by blast
      have "uniform_measure \<mu> A = density \<mu> (\<lambda>x. 0)"
        by(auto simp: uniform_measure_def 1 intro!: density_cong)
      also have "... = null_measure \<mu>"
        by(simp add: null_measure_eq_density)
      finally show ?thesis
        by(auto intro!: finite_measure.s_finite_measure_finite_measure finite_measureI)
    next
      case 2
      show ?thesis
        by(rule prob_space.s_finite_measure_prob[OF prob_space_uniform_measure[OF assms(3) 2]])
    qed
  qed(simp add: assms)
  finally show ?thesis .
qed

corollary(in standard_borel_ne) qbs_l_uniform_qbs:
  assumes "s \<in> qbs_space (monadM_qbs (measure_to_qbs M))" "qbs_l s A \<noteq> 0" 
  shows "qbs_l (uniform_qbs s A) = uniform_measure (qbs_l s) A"
  by(simp add: qbs_l_uniform_qbs'[OF sets_qbs_l[OF assms(1),simplified lr_sets_ident] qbs_l_s_finite.s_finite_measure_axioms assms(2),symmetric] qbs_l_inverse_qbs_l[OF assms(1)])

lemma interval_uniform_qbs: "(\<lambda>a b. uniform_qbs lborel\<^sub>Q {a<..<b::real}) \<in> borel\<^sub>Q \<Rightarrow>\<^sub>Q borel\<^sub>Q \<Rightarrow>\<^sub>Q monadM_qbs borel\<^sub>Q"
proof(rule curry_preserves_morphisms)
  have "(\<lambda>xy. uniform_qbs lborel\<^sub>Q {fst xy<..<snd xy::real}) = qbs_l_inverse \<circ> (\<lambda>xy. uniform_measure lborel {fst xy<..<snd xy})"
    by(auto simp: uniform_qbs_def)
  also have "... \<in> measure_to_qbs (borel \<Otimes>\<^sub>M borel) \<rightarrow>\<^sub>Q monadM_qbs borel\<^sub>Q"
  proof(safe intro!: standard_borel_ne.measure_with_args_morphism measure_kernel.s_finite_kernel_finite_bounded)
    show "measure_kernel (borel \<Otimes>\<^sub>M borel) borel (\<lambda>xy. uniform_measure lborel {fst xy<..<snd xy :: real})"
    proof
      fix B :: "real set"
      assume [measurable]:"B \<in> sets borel"
      have [simp]:"emeasure lborel ({fst x<..<snd x} \<inter> B) / emeasure lborel {fst x<..<snd x} = (if fst x \<le> snd x then emeasure lborel ({fst x<..<snd x} \<inter> B) / ennreal (snd x - fst x) else 0)" for x
        by auto
      show "(\<lambda>x. emeasure (uniform_measure lborel {fst x<..<snd x}) B) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
        by (simp, measurable) auto
    qed auto
  next
    show "(a, b) \<in> space (borel \<Otimes>\<^sub>M borel) \<Longrightarrow> emeasure (uniform_measure lborel {fst (a, b)<..<snd (a, b)}) (space borel) < \<infinity>" for a b :: real
      by(cases "a \<le> b") (use ennreal_divide_eq_top_iff top.not_eq_extremum in auto)
  qed simp
  finally show "(\<lambda>xy. uniform_qbs lborel\<^sub>Q {fst xy<..<snd xy::real}) \<in> borel\<^sub>Q \<Otimes>\<^sub>Q borel\<^sub>Q \<rightarrow>\<^sub>Q monadM_qbs borel\<^sub>Q"
    by (simp add: borel_prod qbs_borel_prod)
qed

context
  fixes a b :: real
  assumes [arith]:"a < b"
begin

lemma qbs_uniform_distribution_expectation:
  assumes "f \<in> qbs_borel \<rightarrow>\<^sub>Q qbs_borel"
  shows "(\<integral>\<^sup>+\<^sub>Q x. f x \<partial>uniform_qbs lborel\<^sub>Q {a<..<b}) = (\<integral>\<^sup>+x \<in> {a<..<b}. f x \<partial>lborel) / (b - a)"
proof -
  have [measurable]: "f \<in> borel_measurable borel"
    using assms qbs_Mx_is_morphisms qbs_Mx_qbs_borel by blast
  show ?thesis
    by(auto simp: qbs_nn_integral_def2_l standard_borel_ne.qbs_l_uniform_qbs[of borel lborel_qbs] nn_integral_uniform_measure)
qed

end

subsubsection \<open> Bernoulli Distribution \<close>
abbreviation qbs_bernoulli :: "real \<Rightarrow> bool qbs_measure" where
"qbs_bernoulli \<equiv> (\<lambda>x. qbs_pmf (bernoulli_pmf x))"

lemma bernoulli_measurable:
 "(\<lambda>x. measure_pmf (bernoulli_pmf x)) \<in> borel \<rightarrow>\<^sub>M prob_algebra (count_space UNIV)"
proof(rule measurable_prob_algebra_generated[where \<Omega>=UNIV and G=UNIV])
  fix A :: "bool set"
  have "A \<subseteq> {True,False}"
    by auto
  then consider "A = {}" | "A = {True}" | "A = {False}" | "A = {False,True}"
    by auto
  thus "(\<lambda>a. emeasure (measure_pmf (bernoulli_pmf a)) A) \<in> borel_measurable borel"
    by(cases,simp_all add: emeasure_measure_pmf_finite bernoulli_pmf.rep_eq UNIV_bool[symmetric])
qed (auto simp add: sets_borel_eq_count_space Int_stable_def measure_pmf.prob_space_axioms)

lemma qbs_bernoulli_morphism: "qbs_bernoulli \<in> qbs_borel \<rightarrow>\<^sub>Q monadP_qbs (qbs_count_space UNIV)"
  using standard_borel_ne.measure_with_args_morphismP[OF _ bernoulli_measurable]
  by (simp add: qbs_pmf_def comp_def)

lemma qbs_bernoulli_expectation:
  assumes [simp]: "0 \<le> p" "p \<le> 1"
  shows "(\<integral>\<^sub>Q x. f x \<partial>qbs_bernoulli p) = f True * p + f False * (1 - p)"
  by(simp add: qbs_integral_def2_l)

end