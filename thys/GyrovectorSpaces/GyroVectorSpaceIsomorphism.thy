theory GyroVectorSpaceIsomorphism
  imports GyroVectorSpace
begin

locale gyrocarrier_isomorphism' =
       gyrocarrier_norms_embed' to_carrier +
       gyrocarrier to_carrier + 
   G:  gyrocarrier_norms_embed' to_carrier'
   for to_carrier :: "'a::gyrocommutative_gyrogroup \<Rightarrow> 'b::{real_inner, real_normed_algebra_1}" and
       to_carrier' :: "'c::gyrocommutative_gyrogroup \<Rightarrow> 'd::{real_inner, real_normed_algebra_1}"  +
 fixes \<phi> :: "'a \<Rightarrow> 'c"
begin

definition \<phi>\<^sub>R :: "real \<Rightarrow> real" where 
  "\<phi>\<^sub>R x = G.to_real' (\<phi> (of_real' x))"

end

locale gyrocarrier_isomorphism = gyrocarrier_isomorphism' +
  assumes \<phi>bij [simp]:
    "bij \<phi>"
  assumes \<phi>plus [simp]:
    "\<And> u v :: 'a. \<phi> (u \<oplus> v) = \<phi> u \<oplus> \<phi> v"
  assumes \<phi>inner_unit:
    "\<And> u v :: 'a. \<lbrakk>u \<noteq> 0\<^sub>g; v \<noteq> 0\<^sub>g\<rbrakk> \<Longrightarrow>
                    inner (to_carrier' (\<phi> u) /\<^sub>R G.gyronorm (\<phi> u)) (to_carrier' (\<phi> v) /\<^sub>R G.gyronorm (\<phi> v)) = 
                    inner (to_carrier u /\<^sub>R gyronorm u) (to_carrier v /\<^sub>R gyronorm v)"
  assumes \<phi>\<^sub>Rgyronorm [simp]:
    "\<And> a. \<phi>\<^sub>R (gyronorm a) = G.gyronorm (\<phi> a)"
begin

lemma \<phi>inv\<phi> [simp]:
  shows "\<phi> (inv \<phi> a) = a"
  by (meson \<phi>bij bij_inv_eq_iff)

lemma inv\<phi>\<phi> [simp]:
  shows "(inv \<phi>) (\<phi> a) = a"
  by (metis \<phi>bij bij_inv_eq_iff)

lemma \<phi>zero [simp]:
  shows "\<phi> 0\<^sub>g = 0\<^sub>g"
  by (metis \<phi>plus gyro_left_cancel gyro_right_id)

lemma \<phi>minus [simp]:
  shows "\<phi> (\<ominus> a) = \<ominus> (\<phi> a)"
  by (metis \<phi>plus \<phi>zero gyro_equation_left gyro_left_inv)

lemma inv\<phi>plus[simp]:
  shows "(inv \<phi>)(a \<oplus> b) = inv \<phi> a \<oplus> inv \<phi> b"
  by (metis \<phi>bij \<phi>plus bij_inv_eq_iff)

lemma \<phi>gyr [simp]:
  shows "\<phi> (gyr u v a) = gyr (\<phi> u) (\<phi> v) (\<phi> a)"
  by (simp add: gyr_def)

lemma inv\<phi>gyr [simp]:
  shows "(inv \<phi>) (gyr u v a) = gyr (inv \<phi> u) (inv \<phi> v) (inv \<phi> a)"
  by (metis \<phi>bij \<phi>gyr bij_inv_eq_iff)

lemma \<phi>inner:
  assumes "u \<noteq> 0\<^sub>g" "v \<noteq> 0\<^sub>g"
  shows "G.gyroinner (\<phi> u) (\<phi> v) =
         (G.gyronorm (\<phi> u) / gyronorm u) *\<^sub>R (G.gyronorm (\<phi> v) / gyronorm v) *\<^sub>R gyroinner u v"
proof-
  have "\<phi> u \<noteq> 0\<^sub>g" "\<phi> v \<noteq> 0\<^sub>g"
    by (metis \<phi>bij \<phi>zero assms(1) bij_inv_eq_iff)
       (metis \<phi>bij \<phi>zero assms(2) bij_inv_eq_iff)
  then have "G.gyronorm (\<phi> u) \<noteq> 0" "G.gyronorm (\<phi> v) \<noteq> 0"
    using G.norm_zero_iff 
    by blast+
  then have "inner (to_carrier' (\<phi> u)) (to_carrier' (\<phi> v)) = 
        G.gyronorm (\<phi> u) *\<^sub>R G.gyronorm (\<phi> v) *\<^sub>R inner (to_carrier' (\<phi> u) /\<^sub>R G.gyronorm (\<phi> u)) (to_carrier' (\<phi> v) /\<^sub>R G.gyronorm (\<phi> v))"
    by (smt (verit, ccfv_threshold) divideR_right inner_commute inner_scaleR_right real_scaleR_def)
  also have "\<dots> = G.gyronorm (\<phi> u) *\<^sub>R G.gyronorm (\<phi> v) *\<^sub>R inner (to_carrier u /\<^sub>R gyronorm u) (to_carrier v /\<^sub>R gyronorm v)"
    using \<phi>inner_unit[OF assms]
    by simp
  finally show ?thesis
    unfolding G.gyroinner_def gyroinner_def
    by (simp add: divide_inverse_commute)
qed

lemma gyronorm'gyr:
  shows "G.gyronorm (gyr u v a) = G.gyronorm a"
proof (cases "a = 0\<^sub>g")
  case True
  then show ?thesis
    by (simp add: gyr_id_3)
next
  case False
  then show ?thesis
    by (metis \<phi>\<^sub>Rgyronorm \<phi>inv\<phi> inv\<phi>gyr norm_gyr)
qed

end

sublocale gyrocarrier_isomorphism \<subseteq> gyrocarrier to_carrier'
proof
  fix u v a b
  show "G.gyroinner (gyr u v a) (gyr u v b) = G.gyroinner a b"
  proof (cases "a = 0\<^sub>g \<or> b = 0\<^sub>g")
    case True
    then show ?thesis
      by (metis G.gyroinner_def G.to_carrier_zero gyr_id_3 inner_zero_left inner_zero_right)
  next
    case False

    let ?Ga = "gyr (inv \<phi> u) (inv \<phi> v) (inv \<phi> a)" and ?Gb = "gyr (inv \<phi> u) (inv \<phi> v) (inv \<phi> b)"

    have "G.gyroinner (gyr u v a) (gyr u v b) = G.gyroinner (\<phi> ?Ga) (\<phi> ?Gb)"
      using inv\<phi>gyr 
      by simp
    also have "\<dots> = (G.gyronorm (\<phi> ?Ga) / \<llangle>?Ga\<rrangle>) *\<^sub>R (G.gyronorm (\<phi> ?Gb) / \<llangle>?Gb\<rrangle>) *\<^sub>R ?Ga \<cdot> ?Gb" 
    proof (subst \<phi>inner)
      show "gyr (inv \<phi> u) (inv \<phi> v) (inv \<phi> a) \<noteq> 0\<^sub>g"
        by (metis False \<phi>inv\<phi> \<phi>zero gyr_id_3 gyr_inj)
    next
      show "gyr (inv \<phi> u) (inv \<phi> v) (inv \<phi> b) \<noteq> 0\<^sub>g"
        by (metis False \<phi>inv\<phi> \<phi>zero gyr_id_3 gyr_inj)
    qed simp
    also have "\<dots> = (G.gyronorm (\<phi> ?Ga) / \<llangle>?Ga\<rrangle>) *\<^sub>R (G.gyronorm (\<phi> ?Gb) / \<llangle>?Gb\<rrangle>) *\<^sub>R (inv \<phi> a) \<cdot> (inv \<phi> b)"
      using inner_gyroauto_invariant
      by presburger
    finally have "G.gyroinner (gyr u v a) (gyr u v b) = (G.gyronorm (gyr u v a) / gyronorm ?Ga) *\<^sub>R (G.gyronorm (gyr u v b) / gyronorm ?Gb) *\<^sub>R (inv \<phi> a) \<cdot> (inv \<phi> b)"
      by auto

    moreover

    have "G.gyroinner a b = (G.gyronorm a / \<llangle>inv \<phi> a\<rrangle>) *\<^sub>R (G.gyronorm b / \<llangle>inv \<phi> b\<rrangle>) *\<^sub>R inv \<phi> a \<cdot> inv \<phi> b"
      using \<phi>inner[of "inv \<phi> a" "inv \<phi> b"] 
      by (metis False \<phi>inv\<phi> \<phi>zero)

    moreover
    have "\<llangle>gyr (inv \<phi> u) (inv \<phi> v) (inv \<phi> a)\<rrangle> = \<llangle>inv \<phi> a\<rrangle>"
         "\<llangle>gyr (inv \<phi> u) (inv \<phi> v) (inv \<phi> b)\<rrangle> = \<llangle>inv \<phi> b\<rrangle>"
      by (auto simp add: norm_gyr)

    moreover

    have "G.gyronorm (gyr u v a) = G.gyronorm a"
         "G.gyronorm (gyr u v b) = G.gyronorm b"
      using gyronorm'gyr
      by auto
 
    ultimately

    show ?thesis
      by simp
  qed
qed

locale pre_gyrovector_space_isomorphism' = 
    pre_gyrovector_space to_carrier scale + 
    gyrocarrier_norms_embed' to_carrier + 
  GC: gyrocarrier_norms_embed' to_carrier'  
  for to_carrier :: "'a::gyrocommutative_gyrogroup \<Rightarrow> 'b::{real_inner, real_normed_algebra_1}" and
      to_carrier' :: "'c::gyrocommutative_gyrogroup \<Rightarrow> 'd::{real_inner, real_normed_algebra_1}" and
      scale :: "real \<Rightarrow> 'a \<Rightarrow> 'a" and 
      scale' :: "real \<Rightarrow> 'c \<Rightarrow> 'c"  +
  fixes \<phi> :: "'a \<Rightarrow> 'c"

sublocale pre_gyrovector_space_isomorphism' \<subseteq> gyrocarrier_isomorphism'
  ..

locale pre_gyrovector_space_isomorphism = 
   pre_gyrovector_space_isomorphism' +
   gyrocarrier_isomorphism +
   assumes \<phi>scale [simp]:
      "\<And> r :: real. \<And> u :: 'a. \<phi> (scale r u) = scale' r (\<phi> u)"
begin

lemma scale'_1:
  shows "scale' 1 a = a"
  using \<phi>scale[of 1 "(inv \<phi>) a"]
  by (simp add: scale_1)

lemma scale'_distrib:
  shows "scale' (r1 + r2) a = scale' r1 a \<oplus> scale' r2 a"
  using \<phi>scale[symmetric, of "r1 + r2" "(inv \<phi>) a"]
  using scale_distrib
  by auto

lemma scale'_assoc:
  shows "scale' (r1 * r2) a = scale' r1 (scale' r2 a)"
  using \<phi>scale[symmetric, of "r1 * r2" "(inv \<phi>) a"]
  using scale_assoc 
  by force

lemma scale'_gyroauto_id:
  shows "gyr (scale' r1 v) (scale' r2 v) = id"
proof
  fix x
  show "gyr (scale' r1 v) (scale' r2 v) x = id x"
    using \<phi>scale[symmetric, of r1 "(inv \<phi>) v"] \<phi>scale[symmetric, of r2 "(inv \<phi>) v"]
    by (metis \<phi>inv\<phi> gyroauto_id id_apply inv\<phi>\<phi> inv\<phi>gyr)
qed

lemma scale'_gyroauto_property:
  shows "gyr u v (scale' r a) = scale' r (gyr u v a)"
  using \<phi>scale[of r "inv \<phi> (gyr u v a)"]
  using \<phi>scale[of r "inv \<phi> a"]
  by (metis \<phi>bij bij_inv_eq_iff gyroauto_property inv\<phi>gyr)

end

locale gyrovector_space_isomorphism' = 
  pre_gyrovector_space_isomorphism + 
  gyrovector_space_norms_embed scale +
  GC: gyrocarrier_norms_embed to_carrier' scale' +
  assumes \<phi>reals:
    "\<phi> ` reals = GC.reals"
begin

lemma \<phi>\<^sub>Rnorms:
  assumes "a \<in> norms"
  shows "\<phi>\<^sub>R a \<in> GC.norms"
  using assms
  by (metis GC.bij_betw_to_real' \<phi>\<^sub>R_def \<phi>reals bij_betw_iff_bijections bij_reals_norms image_iff)

lemma \<phi>of_real'[simp]:
  assumes "a \<in> norms"
  shows "\<phi> (of_real' a) = GC.of_real' (\<phi>\<^sub>R a)"
  using assms
  by (metis GC.of_real' \<phi>\<^sub>R_def \<phi>reals bij_betwE bij_reals_norms image_iff)

lemma \<phi>gyronorm [simp]:
  shows "\<phi> (of_real' (gyronorm a)) = GC.of_real' (GC.gyronorm (\<phi> a))"
  by simp

lemma \<phi>\<^sub>Rplus [simp]:
  assumes "a \<in> norms" "b \<in> norms"
  shows "\<phi>\<^sub>R (a \<oplus>\<^sub>R b) = GC.oplusR (\<phi>\<^sub>R a) (\<phi>\<^sub>R b)"
proof-
  have "\<phi>\<^sub>R (a \<oplus>\<^sub>R b) = GC.to_real' (\<phi> (of_real' a) \<oplus> \<phi> (of_real' b))"
    unfolding \<phi>\<^sub>R_def oplusR_def
  proof (subst of_real')
    show "of_real' a \<oplus> of_real' b \<in> reals"
      by (meson assms(1) assms(2) bij_betwE bij_reals_norms oplus_reals)
  qed simp
  then show ?thesis
    using assms
    unfolding GC.oplusR_def
    by simp
qed

lemma \<phi>\<^sub>Rplus' [simp]:
  "\<phi>\<^sub>R ((\<llangle>a\<rrangle>) \<oplus>\<^sub>R (\<llangle>b\<rrangle>)) = GC.oplusR (\<phi>\<^sub>R (\<llangle>a\<rrangle>)) (\<phi>\<^sub>R (\<llangle>b\<rrangle>))"
  by (simp add: GC.oplusR_def \<phi>\<^sub>R_def)

lemma \<phi>\<^sub>Rtimes [simp]:
  assumes "a \<in> norms"
  shows "\<phi>\<^sub>R (r \<otimes>\<^sub>R a) = GC.otimesR r (\<phi>\<^sub>R a)"
proof-
  have "\<phi>\<^sub>R (r \<otimes>\<^sub>R a) = GC.to_real' (\<phi> (of_real' (to_real' (scale r (of_real' a)))))"
    unfolding \<phi>\<^sub>R_def otimesR_def
    by simp
  also have "\<dots> = GC.to_real' (\<phi> (scale r (of_real' a)))"
    using assms
    by (metis bij_betwE bij_reals_norms of_real' otimes_reals)    
  finally show ?thesis
    using assms
    unfolding GC.otimesR_def
    by simp
qed

lemma \<phi>\<^sub>Rtimes' [simp]:
  shows "\<phi>\<^sub>R (r \<otimes>\<^sub>R (\<llangle>a\<rrangle>)) = GC.otimesR r (\<phi>\<^sub>R (\<llangle>a\<rrangle>))"
  by (simp add: GC.otimesR_def \<phi>\<^sub>R_def)

lemma \<phi>\<^sub>Rinv [simp]:
  assumes "a \<in> norms"
  shows "\<phi>\<^sub>R (\<ominus>\<^sub>R a) = GC.oinvR (\<phi>\<^sub>R a)"
proof-
  have "\<phi>\<^sub>R (\<ominus>\<^sub>R a) = GC.to_real' (\<phi> (of_real' (to_real' (\<ominus> (of_real' a)))))"
    unfolding \<phi>\<^sub>R_def oinvR_def
    by simp
  also have "\<dots> = GC.to_real' (\<phi> (\<ominus> (of_real' a)))"
    by (metis assms bij_betwE bij_reals_norms of_real' oinv_reals)
  finally show ?thesis
    using assms
    unfolding GC.oinvR_def
    by simp
qed

lemma \<phi>\<^sub>Rinv' [simp]:
  "\<phi>\<^sub>R (\<ominus>\<^sub>R (\<llangle>a\<rrangle>)) = GC.oinvR (\<phi>\<^sub>R (\<llangle>a\<rrangle>))"
  by (simp add: \<phi>\<^sub>R_def GC.oinvR_def)


lemma scale'_prop1':
  assumes "u \<noteq> 0\<^sub>g" "r \<noteq> 0"
  shows "to_carrier' (\<phi> (scale \<bar>r\<bar> u)) /\<^sub>R GC.gyronorm (\<phi> (scale \<bar>r\<bar> u)) = 
         (to_carrier' (\<phi> u) /\<^sub>R GC.gyronorm (\<phi> u))" (is "?a = ?b")
proof-
  have "\<llangle>scale r u\<rrangle> = \<llangle>scale (abs r) u\<rrangle>"
    using homogeneity by force

  have "inner ?b ?a =
        inner (to_carrier u /\<^sub>R \<llangle>u\<rrangle>) (to_carrier (scale \<bar>r\<bar> u) /\<^sub>R \<llangle>scale \<bar>r\<bar> u\<rrangle>)"
    using \<phi>inner_unit[where u=u and v="scale (abs r) u"] 
    by fastforce
  also have "\<dots> = inner (to_carrier u /\<^sub>R \<llangle>u\<rrangle>) (to_carrier u /\<^sub>R \<llangle>u\<rrangle>)"
    using scale_prop1[of r u] \<open>u \<noteq> 0\<^sub>g\<close> \<open>r \<noteq> 0\<close> \<open>\<llangle>scale r u\<rrangle> = \<llangle>scale (abs r) u\<rrangle>\<close>
    by simp
  finally have "inner ?b ?a = 1"
    by (smt (verit, ccfv_threshold) \<phi>inner_unit assms(1) gyronorm_def inverse_nonnegative_iff_nonnegative inverse_nonzero_iff_nonzero left_inverse norm_eq norm_eq_1 norm_le_zero_iff norm_scaleR norm_zero_iff scaleR_eq_0_iff to_carrier_zero_iff)
    
  show ?thesis
  proof (rule inner_eq_1)
    show "inner ?a ?b = 1"
      using \<open>inner ?b ?a = 1\<close>
      by (simp add: inner_commute)
  next
    show "norm ?a = 1"
      by (smt (verit, ccfv_threshold) \<phi>inner_unit assms(1) assms(2) gyronorm_def scale_prop1 inverse_nonnegative_iff_nonnegative inverse_nonzero_iff_nonzero left_inverse local.norm_zero norm_eq norm_ge_zero norm_scaleR norm_zero_iff scaleR_eq_0_iff to_carrier_zero_iff)
  next
    show "norm ?b = 1"
      using GC.norm_zero_iff \<phi>zero assms(1) GC.gyronorm_def inv\<phi>\<phi> inverse_negative_iff_negative left_inverse norm_not_less_zero norm_scaleR
      by (smt (verit, del_insts))
  qed
qed 

lemma scale'_prop1:
  assumes "a \<noteq> 0\<^sub>g" "r \<noteq> 0"
  shows "to_carrier' (scale' \<bar>r\<bar> a) /\<^sub>R GC.gyronorm (scale' r a) = to_carrier' a /\<^sub>R GC.gyronorm a"
proof-
  from assms have *: "inv \<phi> a \<noteq> 0\<^sub>g" "r \<noteq> 0"
    by (metis \<phi>inv\<phi> \<phi>zero, simp)
  show ?thesis
    using scale'_prop1'[OF *]
    by (metis \<phi>\<^sub>Rgyronorm \<phi>inv\<phi> \<phi>scale abs_idempotent homogeneity)
qed

lemma scale'_homogeneity:
  shows "GC.gyronorm (scale' r a) = GC.otimesR \<bar>r\<bar> (GC.gyronorm a)"
proof-
  have "GC.gyronorm (scale' r a) = GC.gyronorm (\<phi> (scale r (inv \<phi> a)))"
    using \<phi>scale[of r "inv \<phi> a"]
    by simp
  also have "\<dots> = \<phi>\<^sub>R (gyronorm (scale r (inv \<phi> a)))"
    by simp
  also have "\<dots> = \<phi>\<^sub>R (\<bar>r\<bar> \<otimes>\<^sub>R (\<llangle>inv \<phi> a\<rrangle>))"
    using homogeneity
    by simp
  also have "\<dots> =  \<phi>\<^sub>R (to_real' (scale \<bar>r\<bar> (of_real' (\<llangle>inv \<phi> a\<rrangle>))))"
    unfolding otimesR_def
    by simp
  also have "\<dots> = GC.to_real' (\<phi> (scale \<bar>r\<bar> (of_real' (gyronorm (inv \<phi> a)))))"
    using GC.otimesR_def \<phi>\<^sub>Rtimes otimesR_def
    by force
  also have "\<dots> = GC.to_real' (scale' \<bar>r\<bar> (\<phi> (of_real' (gyronorm (inv \<phi> a)))))"
    using \<phi>scale
    by simp
  also have "\<dots> = GC.to_real' (scale' \<bar>r\<bar> (GC.of_real' (GC.gyronorm (\<phi> (inv \<phi> a)))))"
    by (subst \<phi>gyronorm, simp)
  finally
  show "GC.gyronorm (scale' r a) = GC.otimesR \<bar>r\<bar> (GC.gyronorm a)"
    unfolding GC.otimesR_def
    by simp
qed

end

sublocale gyrovector_space_isomorphism' \<subseteq> GV: pre_gyrovector_space to_carrier' scale'
  by (meson gyrocarrier_axioms scale'_prop1  pre_gyrovector_space.intro pre_gyrovector_space_axioms.intro scale'_1 scale'_assoc scale'_distrib scale'_gyroauto_id scale'_gyroauto_property)

locale gyrovector_space_isomorphism = 
  gyrovector_space_isomorphism' + 
  assumes \<phi>\<^sub>Rmono:
    "\<And> a b. \<lbrakk>a \<in> norms; b \<in> norms; 0 \<le> a; a \<le> b\<rbrakk> \<Longrightarrow> \<phi>\<^sub>R a \<le> \<phi>\<^sub>R b" 
begin

lemma scale'_triangle:
  shows  "GC.gyronorm (a \<oplus> b) \<le> GC.oplusR (GC.gyronorm a) (GC.gyronorm b)"
proof-
  have "GC.gyronorm (a \<oplus> b) = \<phi>\<^sub>R (\<llangle>inv \<phi> a \<oplus> inv \<phi> b\<rrangle>)"
    by simp
  moreover
  have "GC.oplusR (GC.gyronorm a) (GC.gyronorm b) = \<phi>\<^sub>R ((\<llangle>inv \<phi> a\<rrangle>) \<oplus>\<^sub>R (\<llangle>inv \<phi> b\<rrangle>))"
    by simp
  moreover
  have "\<phi>\<^sub>R (\<llangle>inv \<phi> a \<oplus> inv \<phi> b\<rrangle>) \<le> \<phi>\<^sub>R ((\<llangle>inv \<phi> a\<rrangle>) \<oplus>\<^sub>R (\<llangle>inv \<phi> b\<rrangle>))"
  proof (rule \<phi>\<^sub>Rmono)
    show "\<llangle>inv \<phi> a \<oplus> inv \<phi> b\<rrangle> \<in> norms"
      unfolding norms_def
      by auto
  next
    show "\<llangle>inv \<phi> a\<rrangle> \<oplus>\<^sub>R (\<llangle>inv \<phi> b\<rrangle>) \<in> norms"
    proof (rule oplusR_norms)
      show "\<llangle>inv \<phi> a\<rrangle> \<in> norms" "\<llangle>inv \<phi> b\<rrangle> \<in> norms"
        unfolding norms_def
        by auto
    qed
  next
    show "0 \<le> \<llangle>inv \<phi> a \<oplus> inv \<phi> b\<rrangle>"
      by (simp add: gyronorm_def)
  next
    show "\<llangle>inv \<phi> a \<oplus> inv \<phi> b\<rrangle> \<le> (\<llangle>inv \<phi> a\<rrangle>) \<oplus>\<^sub>R (\<llangle>inv \<phi> b\<rrangle>)"
      by (simp add: gyrotriangle)
  qed
  ultimately
  show  "GC.gyronorm (a \<oplus> b) \<le> GC.oplusR (GC.gyronorm a) (GC.gyronorm b)"
    by simp
qed

end

sublocale gyrovector_space_isomorphism \<subseteq> gyrovector_space_norms_embed scale' to_carrier'
  by (meson GC.gyrocarrier_norms_embed_axioms GV.pre_gyrovector_space_axioms gyrocarrier_axioms gyrovector_space_isomorphism.scale'_triangle gyrovector_space_isomorphism_axioms gyrovector_space_norms_embed_axioms.intro gyrovector_space_norms_embed_def scale'_homogeneity)

(* ------------------------------------------------------------ *)

locale gyrocarrier_isomorphism_norms_embed' = gyrovector_space_norms_embed scale to_carrier + 
             GC: gyrocarrier_norms_embed' to_carrier'
  for to_carrier :: "'a::gyrocommutative_gyrogroup \<Rightarrow> 'b::{real_inner, real_normed_algebra_1}" and
      to_carrier' :: "'c::gyrocommutative_gyrogroup \<Rightarrow> 'd::{real_inner, real_normed_algebra_1}" and
      scale :: "real \<Rightarrow> 'a \<Rightarrow> 'a" + 
  fixes scale' :: "real \<Rightarrow> 'c \<Rightarrow> 'c" 
  fixes \<phi> :: "'a \<Rightarrow> 'c"
begin

definition \<phi>\<^sub>R :: "real \<Rightarrow> real" where 
  "\<phi>\<^sub>R x = GC.to_real' (\<phi> (of_real' x))"

end

locale gyrocarrier_isomorphism_norms_embed = gyrocarrier_isomorphism_norms_embed' +
  assumes \<phi>bij:
    "bij \<phi>"
  assumes \<phi>plus [simp]:
    "\<And> u v :: 'a. \<phi> (u \<oplus> v) = \<phi> u \<oplus> \<phi> v"
  assumes \<phi>scale [simp]:
    "\<And> r :: real. \<And> u :: 'a. \<phi> (scale r u) = scale' r (\<phi> u)"
  assumes \<phi>reals:
    "\<phi> ` reals = GC.reals"
  assumes \<phi>\<^sub>Rgyronorm [simp]:
    "\<And> a. \<phi>\<^sub>R (gyronorm a) = GC.gyronorm (\<phi> a)"
  assumes GCoinvRminus:
    "\<And> a. a \<in> GC.norms \<Longrightarrow> GC.oinvR a = -a"
begin

lemma \<phi>inv\<phi> [simp]:
  shows "\<phi> (inv \<phi> a) = a"
  by (meson \<phi>bij bij_inv_eq_iff)

lemma \<phi>zero [simp]:
  shows "\<phi> 0\<^sub>g = 0\<^sub>g"
  by (metis \<phi>plus gyro_left_cancel gyro_right_id)

lemma \<phi>minus [simp]:
  shows "\<phi> (\<ominus> a) = \<ominus> (\<phi> a)"
  by (metis \<phi>plus \<phi>zero gyro_equation_left gyro_left_inv)

lemma \<phi>gyronorm [simp]:
  shows "\<phi> (of_real' (gyronorm a)) = GC.of_real' (GC.gyronorm (\<phi> a))"
  by (metis (no_types, opaque_lifting) GC.of_real' \<phi>\<^sub>R_def \<phi>\<^sub>Rgyronorm \<phi>reals bij_betwE bij_reals_norms image_eqI norm_in_norms)

lemma \<phi>\<^sub>Rinv' [simp]:
  "\<phi>\<^sub>R (\<ominus>\<^sub>R (\<llangle>a\<rrangle>)) = GC.oinvR (\<phi>\<^sub>R (\<llangle>a\<rrangle>))"
  by (simp add: GC.oinvR_def \<phi>\<^sub>R_def)
end

sublocale gyrocarrier_isomorphism_norms_embed \<subseteq> GV': gyrocarrier_norms_embed to_carrier' scale'
proof
  fix a b
  assume "a \<in> GC.reals" "b \<in> GC.reals"
  then obtain x y where 
    "a = GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<or> a = GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))" 
    "b = GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>)) \<or> b = GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>))"
    unfolding GC.reals_def GC.norms_def GC.of_real'_def
    by fastforce
  then have "a \<oplus> b = GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<oplus> GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>)) \<or>
             a \<oplus> b = GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<oplus> GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>)) \<or> 
             a \<oplus> b = GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<oplus> GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>)) \<or> 
             a \<oplus> b = GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<oplus> GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>))"
    by auto
  then have "a \<oplus> b = GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<oplus> GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>)) \<or>
             a \<oplus> b = GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<oplus> GC.of_real' (\<phi>\<^sub>R (\<ominus>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>))) \<or> 
             a \<oplus> b = GC.of_real' (\<phi>\<^sub>R (\<ominus>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))) \<oplus> GC.of_real' (\<phi>\<^sub>R (\<ominus>\<^sub>R ((\<llangle>inv \<phi> y\<rrangle>)))) \<or> 
             a \<oplus> b = GC.of_real' (\<phi>\<^sub>R (\<ominus>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))) \<oplus> GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> y\<rrangle>))"
    by (simp add: GCoinvRminus)
  then show "a \<oplus> b \<in> GC.reals"
    by (smt (verit, del_insts) \<open>a \<in> GC.reals\<close> \<open>b \<in> GC.reals\<close> \<phi>plus \<phi>reals image_iff oplus_reals)
next
  fix a
  assume "a \<in> GC.reals"
  then obtain x where 
    "a = GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<or> a = GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))" 
    unfolding GC.reals_def GC.norms_def GC.of_real'_def
    by fastforce
  then have "\<ominus> a = \<ominus> (GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))) \<or>
             \<ominus> a = \<ominus> (GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)))"
    by auto
  then have "\<ominus> a = \<ominus> (GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))) \<or>
             \<ominus> a = \<ominus> (GC.of_real' (\<phi>\<^sub>R (\<ominus>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))))"
    by (simp add: GCoinvRminus)
  then show "\<ominus> a \<in> GC.reals"
    by (metis (no_types, opaque_lifting) \<open>a \<in> GC.reals\<close> \<phi>minus \<phi>reals image_iff oinv_reals)
next
  fix a r
  assume "a \<in> GC.reals"
  then obtain x where 
    "a = GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)) \<or> a = GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))" 
    unfolding GC.reals_def GC.norms_def GC.of_real'_def
    by fastforce
  then have "scale' r a = scale' r (GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))) \<or>
             scale' r a = scale' r (GC.of_real' (- \<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>)))"
    by auto
  then have "scale' r a = scale' r (GC.of_real' (\<phi>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))) \<or>
             scale' r a = scale' r (GC.of_real' (\<phi>\<^sub>R (\<ominus>\<^sub>R (\<llangle>inv \<phi> x\<rrangle>))))"
    by (simp add: GCoinvRminus)
  then show "scale' r a \<in> GC.reals"
    by (smt (verit, best) \<open>a \<in> GC.reals\<close> \<phi>reals \<phi>scale image_iff otimes_reals)
qed

end