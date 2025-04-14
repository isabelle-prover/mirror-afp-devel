theory MobiusGyroTarski
imports MobiusGeometry TarskiIsomorphism Poincare_Disc.Poincare_Tarski
begin

text \<open>This theory depends on the following AFP entries:

https://www.isa-afp.org/entries/Poincare\_Disc.html
https://www.isa-afp.org/entries/Complex\_Geometry.html

They must be downloaded in order to check this theory.
\<close>

(* -------------------------------------------------------------- *)
text \<open>The following lemmas can be moved to the cited AFP entries.\<close>


lemma eqArgLessCmod:
  assumes "u \<noteq> 0" "v \<noteq> 0"
  shows "Arg u = Arg v \<and> cmod u \<le> cmod v \<longleftrightarrow> (\<exists>k. k \<ge> 0 \<and> k \<le> 1 \<and> u = cor k * v)"
proof 
  assume "Arg u = Arg v \<and> cmod u \<le> cmod v"
  then show "\<exists>k. k \<ge> 0 \<and> k \<le> 1 \<and> u = cor k * v"
    using cmod_cis[OF \<open>u \<noteq> 0\<close>] cmod_cis[OF \<open>v \<noteq> 0\<close>] assms
    by (rule_tac x="cmod u / cmod v" in exI)
       (smt (verit, ccfv_threshold) divide_le_eq_1_pos divide_nonneg_nonneg mult.assoc mult_cancel_right2 nonzero_eq_divide_eq norm_ge_zero of_real_divide of_real_eq_1_iff)
next
  assume "(\<exists>k. k \<ge> 0 \<and> k \<le> 1 \<and> u = cor k * v)"
  then show "Arg u = Arg v \<and> cmod u \<le> cmod v"
    by (metis abs_of_nonneg arg_mult_real_positive assms(1) mult.commute mult_eq_0_iff mult_left_le norm_ge_zero norm_mult norm_of_real zero_less_norm_iff)
qed

(* -------------------------------------------------------------- *)

lift_definition p_blaschke :: "p_point \<Rightarrow> p_isometry" is "\<lambda> a. (moebius_pt (blaschke (to_complex a)))"
  by (metis blaschke_unit_disc_fix inf_notin_unit_disc of_complex_to_complex unit_disc_fix_f_moebius_pt unit_disc_iff_cmod_lt_1)

lemma p_between_p_isometry_pt [simp]:
  shows "p_between (p_isometry_pt f a) (p_isometry_pt f b) (p_isometry_pt f c)  \<longleftrightarrow> p_between a b c"
  by transfer (auto simp add: unit_disc_fix_f_def)

lemma p_blaschke_id [simp]:
  shows "p_isometry_pt (p_blaschke x) x = p_zero"
  by transfer (metis blaschke_a_to_zero inversion_infty inversion_noteq_unit_disc less_irrefl of_complex_to_complex unit_disc_iff_cmod_lt_1 zero_in_unit_disc)

lemma p_between_0uv:
  shows "p_between p_zero u v \<longleftrightarrow> 
        (\<exists>k\<ge>0. k \<le> 1 \<and> to_complex (Rep_p_point u) = cor k * to_complex (Rep_p_point v))"
proof transfer
  fix u v
  assume uv: "u \<in> unit_disc" "v \<in> unit_disc"
  then show "poincare_between 0\<^sub>h u v =
             (\<exists>k\<ge>0. k \<le> 1 \<and> to_complex u = cor k * to_complex v)"
  proof (cases "u = 0\<^sub>h \<or> v = 0\<^sub>h")
    case True
    then show ?thesis
      by (metis dual_order.refl inf_notin_unit_disc linordered_nonzero_semiring_class.zero_le_one mult_cancel_left1 mult_zero_class.mult_zero_right of_complex_to_complex of_complex_zero of_real_0 poincare_between_nonstrict(1) poincare_between_sandwich to_complex_zero_zero uv(1) zero_in_unit_disc)
  next
    case False
    then have z: "u \<noteq> 0\<^sub>h" "v \<noteq> 0\<^sub>h"
      by auto
    let ?u = "to_complex u" and ?v = "to_complex v"
    have "poincare_between 0\<^sub>h u v \<longleftrightarrow> Arg ?u = Arg ?v \<and> cmod ?u \<le> cmod ?v"
      using poincare_between_0uv[OF uv z]
      by (auto simp add: Let_def)
    also have "\<dots> \<longleftrightarrow> (\<exists>k\<ge>0. k \<le> 1 \<and> ?u = cor k * ?v)"
      by (metis False eqArgLessCmod to_complex_zero_zero unit_disc_to_complex_inj uv(1) uv(2) zero_in_unit_disc)
    finally show ?thesis
      .
  qed
qed

(* -------------------------------------------------------------- *)
text \<open>A bijection between AFP type representing the Poincare disc (based on complex homogenous coordinates) 
and our type for poincare disc (based on ordinary complex numbers) \<close>

lift_definition \<phi> :: "p_point \<Rightarrow> PoincareDisc" is to_complex
  by (metis inf_notin_unit_disc of_complex_to_complex unit_disc_iff_cmod_lt_1)

lemma distance_m_p_dist:
  shows "distance_m (PoincareDisc.to_complex (\<phi> x)) (PoincareDisc.to_complex (\<phi> y)) = p_dist x y"
  unfolding \<phi>.rep_eq
proof transfer
  fix x y
  assume "x \<in> unit_disc" "y \<in> unit_disc"
  then show "distance_m (Homogeneous_Coordinates.to_complex x) (Homogeneous_Coordinates.to_complex y) =
        poincare_distance x y"
    by (simp add: distance_m_def poincare_distance_formula)
qed

definition blaschke' :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "blaschke' a z = (z - a) / (1 - cnj a * z)"

lemma blaschke'_translation:
  fixes a z :: complex
  shows "blaschke' a z = oplus_m' (ominus_m' a) z"
  unfolding blaschke'_def oplus_m'_def ominus_m'_def
  by (simp add: minus_divide_left)

lift_definition blaschke_g :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" is blaschke'
  using blaschke'_translation ominus_m'_in_disc oplus_m'_in_disc by presburger

lemma blaschke_translation: 
  "blaschke_g a z = (\<ominus>\<^sub>m a) \<oplus>\<^sub>m z"
  by transfer (simp add: blaschke'_translation)

text \<open>Isomorphism between hyperbolic geometry of Poincare disc defined in AFP entry, and hyperbolic 
geometry in Mobius gyrovector space. Since these two are isomorphic, the geometry of Mobius gyrovector  
space satisfies Tarski axioms. \<close>

interpretation MobiusGyroTarskiIso: ElementaryTarskiHyperbolicIso p_congruent p_between \<phi> cong\<^sub>m Mobius_pre_gyrovector_space.between
proof
  show "bij \<phi>"
    unfolding bij_def inj_def surj_def
    by transfer (metis inf_notin_unit_disc mem_Collect_eq of_complex_to_complex to_complex_of_complex unit_disc_iff_cmod_lt_1)
next
  fix x y z w
  show "cong\<^sub>m (\<phi> x) (\<phi> y) (\<phi> z) (\<phi> w) \<longleftrightarrow> p_congruent x y z w"
    unfolding cong\<^sub>m_def distance\<^sub>m_equiv p_congruent_def
    by (simp add: distance_m_p_dist)
next
  fix x y z
  show "Mobius_pre_gyrovector_space.between (\<phi> x) (\<phi> y) (\<phi> z) \<longleftrightarrow> p_between x y z"
  proof-
    let ?f = "\<lambda> a. \<ominus> (\<phi> x) \<oplus> a"
    let ?f' = "\<lambda> a. p_isometry_pt (p_blaschke x) a"

    have *: "\<forall> a. PoincareDisc.to_complex (?f (\<phi> a)) = to_complex (Rep_p_point (?f' a))"
      unfolding gyroplus_PoincareDisc_def gyroinv_PoincareDisc_def blaschke_translation[symmetric]
    proof (transfer, safe)
      fix x a
      assume "x \<in> unit_disc" "a \<in> unit_disc"
      then have *: "to_complex (moebius_pt (blaschke (to_complex x)) a) = 
                ((to_complex a - to_complex x) / (1 - cnj (to_complex x) * to_complex a))"
        using moebius_pt_blaschke[of "to_complex x" "to_complex a"]
        by (smt (verit) blaschke_a_to_zero complex_cnj_zero_iff diff_zero div_by_0 div_by_1 inf_notin_unit_disc inversion_noteq_unit_disc inversion_of_complex mult_eq_0_iff of_complex_to_complex to_complex_of_complex to_complex_zero_zero unit_disc_iff_cmod_lt_1)

      show "blaschke' (to_complex x) (to_complex a) = to_complex (moebius_pt (blaschke (to_complex x)) a)"
        unfolding * blaschke'_def
        by simp
    qed

    have "Mobius_pre_gyrovector_space.between (\<phi> x) (\<phi> y) (\<phi> z) \<longleftrightarrow> 
          Mobius_pre_gyrovector_space.between 0\<^sub>m (?f (\<phi> y)) (?f (\<phi> z))"
      by (metis Mobius_pre_gyrovector_space.between_translate Mobius_pre_gyrovector_space.translate_def gyro_left_inv gyrozero_PoincareDisc_def)
    also have "\<dots> \<longleftrightarrow> (\<exists>k\<ge>0. k \<le> 1 \<and> PoincareDisc.to_complex (?f (\<phi> y)) = More_Complex.cor k * PoincareDisc.to_complex (?f (\<phi> z)))"
      using mobius_between_0uv
      by simp
    also have "\<dots> \<longleftrightarrow> (\<exists>k\<ge>0. k \<le> 1 \<and> to_complex (Rep_p_point (?f' y)) = More_Complex.cor k * to_complex (Rep_p_point (?f' z)))"
      using *
      by auto
    also have "\<dots> \<longleftrightarrow> p_between p_zero (?f' y) (?f' z)"
      using p_between_0uv
      by blast
    also have "\<dots> \<longleftrightarrow> p_between (?f' x) (?f' y) (?f' z)"
      by simp
    finally show ?thesis
      using p_between_p_isometry_pt by blast
  qed
qed

interpretation MobiusGyroTarski: ElementaryTarskiHyperbolic cong\<^sub>m Mobius_pre_gyrovector_space.between
  by (simp add: MobiusGyroTarskiIso.ElementaryTarskiHyperbolic_axioms)


end
