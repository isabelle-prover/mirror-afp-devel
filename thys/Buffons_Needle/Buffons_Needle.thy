(*
  File:    Buffons_Needle.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  A formal solution of Buffon's needle problem.
*)
section \<open>Buffon's Needle Problem\<close>
theory Buffons_Needle
  imports "HOL-Probability.Probability"
begin

subsection \<open>Auxiliary material\<close>

lemma sin_le_zero': "sin x \<le> 0" if "x \<ge> -pi" "x \<le> 0" for x
  by (metis minus_le_iff neg_0_le_iff_le sin_ge_zero sin_minus that(1) that(2))


subsection \<open>Problem definition\<close>

text \<open>
  Consider a needle of length $l$ whose centre has the $x$-coordinate $x$. The following then
  defines the set of all $x$-coordinates that the needle covers 
  (i.e. the projection of the needle onto the $x$-axis.)
\<close>
definition needle :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real set" where
  "needle l x \<phi> = closed_segment (x - l / 2 * sin \<phi>) (x + l / 2 * sin \<phi>)"

text \<open>
  Buffon's Needle problem is then this: Assuming the needle's $x$ position is chosen uniformly
  at random in a strip of width $d$ centred at the origin, what is the probability that the 
  needle crosses at least one of the left/right boundaries of that strip (located at 
  $x = \pm\frac{1}{2}d$)?
\<close>

locale Buffon =
  fixes d l :: real
  assumes d: "d > 0" and l: "l > 0"
begin

definition Buffon :: "(real \<times> real) measure" where
  "Buffon = uniform_measure lborel ({-d/2..d/2} \<times> {-pi..pi})"

lemma space_Buffon [simp]: "space Buffon = UNIV"
  by (simp add: Buffon_def)

definition Buffon_set :: "(real \<times> real) set" where
  "Buffon_set = {(x,\<phi>) \<in> {-d/2..d/2} \<times> {-pi..pi}. needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}}"


subsection \<open>Derivation of the solution\<close>

text \<open>
  The following form is a bit easier to handle.
\<close>
lemma Buffon_set_altdef1:
  "Buffon_set =
     {(x,\<phi>) \<in> {-d/2..d/2} \<times> {-pi..pi}.
         let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
         in  min a b + d/2 \<le> 0 \<and> max a b + d/2 \<ge> 0 \<or> min a b - d/2 \<le> 0 \<and> max a b - d/2 \<ge> 0}"
proof -
  have "(\<lambda>(x,\<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}) =
      (\<lambda>(x,\<phi>). let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
               in  -d/2 \<ge> min a b \<and> -d/2 \<le> max a b \<or> min a b \<le> d/2 \<and> max a b \<ge> d/2)"
    by (auto simp: needle_def Let_def closed_segment_eq_real_ivl min_def max_def)
  also have "\<dots> = 
    (\<lambda>(x,\<phi>). let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
             in  min a b + d/2 \<le> 0 \<and> max a b + d/2 \<ge> 0 \<or> min a b - d/2 \<le> 0 \<and> max a b - d/2 \<ge> 0)"
    by (auto simp add: algebra_simps Let_def)
  finally show ?thesis unfolding Buffon_set_def case_prod_unfold
    by (intro Collect_cong conj_cong refl) meson
qed

lemma Buffon_set_altdef2:
  "Buffon_set = {(x,\<phi>) \<in> {-d/2..d/2} \<times> {-pi..pi}. abs x \<ge> d / 2 - abs (sin \<phi>) * l / 2}"
  unfolding Buffon_set_altdef1
proof (intro Collect_cong prod.case_cong refl conj_cong)
  fix x \<phi>
  assume *: "(x, \<phi>) \<in> {-d/2..d/2} \<times> {-pi..pi}"
  let ?P = "\<lambda>x \<phi>. let a = x - l / 2 * sin \<phi>; b = x + l / 2 * sin \<phi>
               in  min a b + d/2 \<le> 0 \<and> max a b + d/2 \<ge> 0 \<or> min a b - d/2 \<le> 0 \<and> max a b - d/2 \<ge> 0"

  show "?P x \<phi> \<longleftrightarrow> (d / 2 - \<bar>sin \<phi>\<bar> * l / 2 \<le> \<bar>x\<bar>)"
  proof (cases "\<phi> \<ge> 0")
    case True
    have "x - l / 2 * sin \<phi> \<le> x + l / 2 * sin \<phi>" using l True *
      by (auto simp: sin_ge_zero)
    moreover from True and * have "sin \<phi> \<ge> 0" by (auto simp: sin_ge_zero)
    ultimately show ?thesis using * True
      by (force simp: field_simps Let_def min_def max_def case_prod_unfold abs_if)
  next
    case False
    with * have "x - l / 2 * sin \<phi> \<ge> x + l / 2 * sin \<phi>" using l
      by (auto simp: sin_le_zero' mult_nonneg_nonpos)
    moreover from False and * have "sin \<phi> \<le> 0" by (auto simp: sin_le_zero')
    ultimately show ?thesis using * False l d
      by (force simp: field_simps Let_def min_def max_def case_prod_unfold abs_if)
  qed
qed
  
    
text \<open>
  By using the symmetry inherent in the problem, we can reduce the problem to the following 
  set, which corresponds to one quadrant of the original set:
\<close>
definition Buffon_set' :: "(real \<times> real) set" where
  "Buffon_set' = {(x,\<phi>) \<in> {0..d/2} \<times> {0..pi}. x \<ge> d / 2 - sin \<phi> * l / 2}"

lemma closed_buffon_set [simp, intro, measurable]: "closed Buffon_set"
  proof -
  have "Buffon_set = ({-d/2..d/2} \<times> {-pi..pi}) \<inter> 
          (\<lambda>z. abs (fst z) + abs (sin (snd z)) * l / 2 - d / 2) -` {0..}" 
    (is "_ = ?A") unfolding Buffon_set_altdef2 by auto
  also have "closed \<dots>"
    by (intro closed_Int closed_vimage closed_Times) (auto intro!: continuous_intros)
  finally show ?thesis by simp
qed

lemma closed_buffon_set' [simp, intro, measurable]: "closed Buffon_set'"
proof -
  have "Buffon_set' = ({0..d/2} \<times> {0..pi}) \<inter> 
          (\<lambda>z. fst z + sin (snd z) * l / 2 - d / 2) -` {0..}" 
    (is "_ = ?A") unfolding Buffon_set'_def by auto
  also have "closed \<dots>"
    by (intro closed_Int closed_vimage closed_Times) (auto intro!: continuous_intros)
  finally show ?thesis by simp
qed

lemma measurable_buffon_set [measurable]: "Buffon_set \<in> sets borel" 
  by measurable

lemma measurable_buffon_set' [measurable]: "Buffon_set' \<in> sets borel" 
  by measurable


sublocale prob_space Buffon
  unfolding Buffon_def
proof -
  have "emeasure lborel ({- d / 2..d / 2} \<times> {- pi..pi}) = ennreal (2 * d * pi)"
    unfolding lborel_prod [symmetric] using d
    by (subst lborel.emeasure_pair_measure_Times)
       (auto simp: ennreal_mult mult_ac simp flip: ennreal_numeral)
  also have "\<dots> \<noteq> 0 \<and> \<dots> \<noteq> \<infinity>"
    using d by auto
  finally show "prob_space (uniform_measure lborel ({- d / 2..d / 2} \<times> {- pi..pi}))"
    by (intro prob_space_uniform_measure) auto
qed

lemma buffon_prob_aux:
  "emeasure Buffon {(x,\<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}} =
     emeasure lborel Buffon_set / ennreal (2 * d * pi)"
proof -
  have [measurable]: "A \<times> B \<in> sets borel" if "A \<in> sets borel" "B \<in> sets borel" 
    for A B :: "real set" using that unfolding borel_prod [symmetric] by simp
  have "{(x, \<phi>). needle l x \<phi> \<inter> {- d / 2, d / 2} \<noteq> {}} \<in> sets borel"
    by (intro pred_Collect_borel)
       (simp add: borel_prod [symmetric] needle_def closed_segment_eq_real_ivl case_prod_unfold)
  hence "emeasure Buffon {(x,\<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}} =
           emeasure lborel (({-d/2..d/2} \<times> {- pi..pi}) \<inter> {(x,\<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}}) /
           emeasure lborel ({-(d/2)..d/2} \<times> {-pi..pi})"
    unfolding Buffon_def Buffon_set_def by (subst emeasure_uniform_measure) simp_all
  also have "({-d/2..d/2} \<times> {- pi..pi}) \<inter> {(x, \<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}} = Buffon_set"
    unfolding Buffon_set_def by auto
  also have "emeasure lborel ({-(d/2)..d/2} \<times> {-pi..pi}) = ennreal (2 * d * pi)"
    using d by (simp flip: lborel_prod ennreal_mult add: lborel.emeasure_pair_measure_Times)
  finally show ?thesis .
qed

lemma emeasure_buffon_set_conv_buffon_set':
  "emeasure lborel Buffon_set = 4 * emeasure lborel Buffon_set'"
proof -
  have distr_lborel [simp]: "distr M lborel f = distr M borel f" for M and f :: "real \<Rightarrow> real"
    by (rule distr_cong) simp_all
    
  define A where "A = Buffon_set'"
  define B C D where "B = (\<lambda>x. (-fst x, snd x)) -` A" and "C = (\<lambda>x. (fst x, -snd x)) -` A" and
      "D = (\<lambda>x. (-fst x, -snd x)) -` A"
  have meas [measurable]:
     "(\<lambda>x::real \<times> real. (-fst x, snd x)) \<in> borel_measurable borel"
     "(\<lambda>x::real \<times> real. (fst x, -snd x)) \<in> borel_measurable borel"
     "(\<lambda>x::real \<times> real. (-fst x, -snd x)) \<in> borel_measurable borel"
    unfolding borel_prod [symmetric] by measurable
  have meas' [measurable]: "A \<in> sets borel" "B \<in> sets borel" "C \<in> sets borel" "D \<in> sets borel"
    unfolding A_def B_def C_def D_def by (rule measurable_buffon_set' measurable_sets_borel meas)+
  
  have *: "Buffon_set = A \<union> B \<union> C \<union> D"
  proof (intro equalityI subsetI, goal_cases)
    case (1 z)
    show ?case
    proof (cases "fst z \<ge> 0"; cases "snd z \<ge> 0")
      assume "fst z \<ge> 0" "snd z \<ge> 0"
      with 1 have "z \<in> A"
        by (auto split: prod.splits simp: Buffon_set_altdef2 Buffon_set'_def sin_ge_zero A_def B_def)
      thus ?thesis by blast   
    next
      assume "\<not>(fst z \<ge> 0)" "snd z \<ge> 0"
      with 1 have "z \<in> B"
        by (auto split: prod.splits simp: Buffon_set_altdef2 Buffon_set'_def sin_ge_zero A_def B_def)
      thus ?thesis by blast
    next    
      assume "fst z \<ge> 0" "\<not>(snd z \<ge> 0)"
      with 1 have "z \<in> C"
        by (auto split: prod.splits simp: Buffon_set_altdef2 Buffon_set'_def sin_le_zero' A_def B_def C_def)
      thus ?thesis by blast   
    next
      assume "\<not>(fst z \<ge> 0)" "\<not>(snd z \<ge> 0)"
      with 1 have "z \<in> D"
        by (auto split: prod.splits simp: Buffon_set_altdef2 Buffon_set'_def sin_le_zero' A_def B_def D_def)
      thus ?thesis by blast
    qed
  next
    case (2 z)
    thus ?case using d l
      by (auto simp: Buffon_set_altdef2 Buffon_set'_def sin_ge_zero sin_le_zero'  A_def B_def C_def D_def)
  qed
  
  have "A \<inter> B = {0} \<times> ({0..pi} \<inter> {\<phi>. sin \<phi> * l - d \<ge> 0})"
    using d l by (auto simp: Buffon_set'_def  A_def B_def C_def D_def)
  moreover have "emeasure lborel \<dots> = 0"
    unfolding lborel_prod [symmetric] by (subst lborel.emeasure_pair_measure_Times) simp_all
  ultimately have AB: "(A \<inter> B) \<in> null_sets lborel"
    unfolding lborel_prod [symmetric] by (simp add: null_sets_def)
  
  have "C \<inter> D = {0} \<times> ({-pi..0} \<inter> {\<phi>. -sin \<phi> * l - d \<ge> 0})"
    using d l by (auto simp: Buffon_set'_def  A_def B_def C_def D_def)
  moreover have "emeasure lborel \<dots> = 0"
    unfolding lborel_prod [symmetric] by (subst lborel.emeasure_pair_measure_Times) simp_all
  ultimately have CD: "(C \<inter> D) \<in> null_sets lborel"
    unfolding lborel_prod [symmetric] by (simp add: null_sets_def)

  have "A \<inter> D = {}" "B \<inter> C = {}" using d l 
    by (auto simp: Buffon_set'_def A_def D_def B_def C_def)
  moreover have "A \<inter> C = {(d/2, 0)}" "B \<inter> D = {(-d/2, 0)}"
    using d l by (auto simp: case_prod_unfold Buffon_set'_def A_def B_def C_def D_def)
  ultimately have AD: "A \<inter> D \<in> null_sets lborel" and BC: "B \<inter> C \<in> null_sets lborel" and
    AC: "A \<inter> C \<in> null_sets lborel" and BD: "B \<inter> D \<in> null_sets lborel" by auto
  
  note *
  also have "emeasure lborel (A \<union> B \<union> C \<union> D) = emeasure lborel (A \<union> B \<union> C) + emeasure lborel D"
    using AB AC AD BC BD CD by (intro emeasure_Un') (auto simp: Int_Un_distrib2)
  also have "emeasure lborel (A \<union> B \<union> C) = emeasure lborel (A \<union> B) + emeasure lborel C"
    using AB AC BC using AB AC AD BC BD CD by (intro emeasure_Un') (auto simp: Int_Un_distrib2)
  also have "emeasure lborel (A \<union> B) = emeasure lborel A + emeasure lborel B"
    using AB using AB AC AD BC BD CD by (intro emeasure_Un') (auto simp: Int_Un_distrib2)
  also have "emeasure lborel B = emeasure (distr lborel lborel (\<lambda>(x,y). (-x, y))) A"
    (is "_ = emeasure ?M _") unfolding B_def 
    by (subst emeasure_distr) (simp_all add: case_prod_unfold)
  also have "?M = lborel" unfolding lborel_prod [symmetric]
    by (subst pair_measure_distr [symmetric]) (simp_all add: sigma_finite_lborel lborel_distr_uminus)
  also have "emeasure lborel C = emeasure (distr lborel lborel (\<lambda>(x,y). (x, -y))) A"
    (is "_ = emeasure ?M _") unfolding C_def 
    by (subst emeasure_distr) (simp_all add: case_prod_unfold)
  also have "?M = lborel" unfolding lborel_prod [symmetric]
    by (subst pair_measure_distr [symmetric]) (simp_all add: sigma_finite_lborel lborel_distr_uminus)
  also have "emeasure lborel D = emeasure (distr lborel lborel (\<lambda>(x,y). (-x, -y))) A"
    (is "_ = emeasure ?M _") unfolding D_def 
    by (subst emeasure_distr) (simp_all add: case_prod_unfold)
  also have "?M = lborel" unfolding lborel_prod [symmetric]
    by (subst pair_measure_distr [symmetric]) (simp_all add: sigma_finite_lborel lborel_distr_uminus)
  finally have "emeasure lborel Buffon_set = 
                  of_nat (Suc (Suc (Suc (Suc 0)))) * emeasure lborel A"
    unfolding of_nat_Suc ring_distribs by simp
  also have "of_nat (Suc (Suc (Suc (Suc 0)))) = (4 :: ennreal)" by simp
  finally show ?thesis unfolding A_def .
qed 

text \<open>
  It only remains now to compute the measure of @{const Buffon_set'}. We first reduce this
  problem to a relatively simple integral:
\<close>
lemma emeasure_buffon_set':
  "emeasure lborel Buffon_set' = 
     ennreal (integral {0..pi} (\<lambda>x. min (d / 2) (sin x * l / 2)))"
  (is "emeasure lborel ?A = _")
proof -  
  have "emeasure lborel ?A = nn_integral lborel (\<lambda>x. indicator ?A x)"
    by (intro nn_integral_indicator [symmetric]) simp_all
  also have "(lborel :: (real \<times> real) measure) = lborel \<Otimes>\<^sub>M lborel" 
    by (simp only: lborel_prod)
  also have "nn_integral \<dots> (indicator ?A) = (\<integral>\<^sup>+\<phi>. \<integral>\<^sup>+x. indicator ?A (x, \<phi>) \<partial>lborel \<partial>lborel)"
    by (subst lborel_pair.nn_integral_snd [symmetric]) (simp_all add: lborel_prod borel_prod)
  also have "\<dots> = (\<integral>\<^sup>+\<phi>. \<integral>\<^sup>+x. indicator {0..pi} \<phi> * indicator {max 0 (d/2 - sin \<phi> * l / 2) .. d/2} x \<partial>lborel \<partial>lborel)"
    using d l by (intro nn_integral_cong) (auto simp: indicator_def field_simps Buffon_set'_def)
  also have "\<dots> = \<integral>\<^sup>+ \<phi>. indicator {0..pi} \<phi> * emeasure lborel {max 0 (d / 2 - sin \<phi> * l / 2)..d / 2} \<partial>lborel"
    by (subst nn_integral_cmult) simp_all
  also have "\<dots> = \<integral>\<^sup>+ \<phi>. ennreal (indicator {0..pi} \<phi> * min (d / 2) (sin \<phi> * l / 2)) \<partial>lborel"
    (is "_ = ?I") using d l by (intro nn_integral_cong) (auto simp: indicator_def sin_ge_zero max_def min_def)
  also have "integrable lborel (\<lambda>\<phi>. (d / 2) * indicator {0..pi} \<phi>)" by simp
  hence int: "integrable lborel (\<lambda>\<phi>. indicator {0..pi} \<phi> * min (d / 2) (sin \<phi> * l / 2))"
    by (rule Bochner_Integration.integrable_bound)
       (insert l d, auto intro!: AE_I2 simp: indicator_def min_def sin_ge_zero)
  hence "?I = set_lebesgue_integral lborel {0..pi} (\<lambda>\<phi>. min (d / 2) (sin \<phi> * l / 2))"
    by (subst nn_integral_eq_integral, assumption)
       (insert d l, auto intro!: AE_I2 simp: sin_ge_zero min_def indicator_def set_lebesgue_integral_def)
  also have "\<dots> = ennreal (integral {0..pi} (\<lambda>x. min (d / 2) (sin x * l / 2)))"
    (is "_ = ennreal ?I") using int by (subst set_borel_integral_eq_integral) (simp_all add: set_integrable_def)
  finally show ?thesis by (simp add: lborel_prod)
qed

  
text \<open>
  We now have to distinguish two cases: The first and easier one is that where the length 
  of the needle, $l$, is less than or equal to the strip width, $d$:
\<close>
context
  assumes l_le_d: "l \<le> d"
begin

lemma emeasure_buffon_set'_short: "emeasure lborel Buffon_set' = ennreal l"
proof -
  have "emeasure lborel Buffon_set' =
          ennreal (integral {0..pi} (\<lambda>x. min (d / 2) (sin x * l / 2)))" (is "_ = ennreal ?I")
    by (rule emeasure_buffon_set')
  also have *: "sin \<phi> * l \<le> d" if "\<phi> \<ge> 0" "\<phi> \<le> pi" for \<phi>
    using mult_mono[OF l_le_d sin_le_one _ sin_ge_zero] that d by (simp add: algebra_simps)
  have "?I = integral {0..pi} (\<lambda>x. (l / 2) * sin x)"
    using l d l_le_d  
    by (intro integral_cong) (auto dest: * simp: min_def sin_ge_zero)
  also have "\<dots> = l / 2 * integral {0..pi} sin" by simp
  also have "(sin has_integral (-cos pi - (- cos 0))) {0..pi}"
    by (intro fundamental_theorem_of_calculus)
       (auto intro!: derivative_eq_intros simp: has_field_derivative_iff_has_vector_derivative [symmetric])
  hence "integral {0..pi} sin = -cos pi - (-cos 0)"
    by (simp add: has_integral_iff)
  finally show ?thesis by (simp add: lborel_prod)
qed

lemma emeasure_buffon_set_short: "emeasure lborel Buffon_set = 4 * ennreal l"
  by (simp add: emeasure_buffon_set_conv_buffon_set' emeasure_buffon_set'_short l_le_d)

lemma prob_short_aux:
  "Buffon {(x, \<phi>). needle l x \<phi> \<inter> {- d / 2, d / 2} \<noteq> {}} = ennreal (2 * l / (d * pi))"
  unfolding buffon_prob_aux emeasure_buffon_set_short using d l
  by (simp flip: ennreal_mult ennreal_numeral add: divide_ennreal)

theorem prob_short: "\<P>((x,\<phi>) in Buffon. needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}) = 2 * l / (d * pi)"
  using prob_short_aux unfolding emeasure_eq_measure
  using l d by (subst (asm) ennreal_inj) auto

end


text \<open>
  The other case where the needle is at least as long as the strip width is more complicated:
\<close>
context
  assumes l_ge_d: "l \<ge> d"
begin

lemma emeasure_buffon_set'_long: 
  shows "l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d \<ge> 0"
  and   "emeasure lborel Buffon_set' =
           ennreal (l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d)"
proof -
  define \<phi>' where "\<phi>' = arcsin (d / l)"
  have \<phi>'_nonneg: "\<phi>' \<ge> 0" unfolding \<phi>'_def using d l l_ge_d arcsin_le_mono[of 0 "d/l"] 
    by (simp add: \<phi>'_def)
  have \<phi>'_le: "\<phi>' \<le> pi / 2" unfolding \<phi>'_def using arcsin_bounded[of "d/l"] d l l_ge_d
    by (simp add: field_simps)
  have ge_phi': "sin \<phi> \<ge> d / l" if "\<phi> \<ge> \<phi>'" "\<phi> \<le> pi / 2" for \<phi>
    using arcsin_le_iff[of "d / l" "\<phi>"] d l_ge_d that \<phi>'_nonneg by (auto simp: \<phi>'_def field_simps)
  have le_phi': "sin \<phi> \<le> d / l" if "\<phi> \<le> \<phi>'" "\<phi> \<ge> 0" for \<phi>
    using le_arcsin_iff[of "d / l" "\<phi>"] d l_ge_d that \<phi>'_le by (auto simp: \<phi>'_def field_simps)
  have "cos \<phi>' = sqrt (1 - (d / l)^2)"
    unfolding \<phi>'_def by (rule cos_arcsin) (insert d l l_ge_d, auto simp: field_simps)

  have "l * (1 - cos \<phi>') + arccos (d / l) * d \<ge> 0"
    using l d l_ge_d
    by (intro add_nonneg_nonneg mult_nonneg_nonneg arccos_lbound) (auto simp: field_simps)   
  thus "l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d \<ge> 0"
    by (simp add: \<open>cos \<phi>' = sqrt (1 - (d / l)^2)\<close>)

  let ?f = "(\<lambda>x. min (d / 2) (sin x * l / 2))"
  have "emeasure lborel Buffon_set' = ennreal (integral {0..pi} ?f)" (is "_ = ennreal ?I")
    by (rule emeasure_buffon_set')
  also have "?I = integral {0..pi/2} ?f + integral {pi/2..pi} ?f"
    by (rule Henstock_Kurzweil_Integration.integral_combine [symmetric]) (auto intro!: integrable_continuous_real continuous_intros)
  also have "integral {pi/2..pi} ?f = integral {-pi/2..0} (?f \<circ> (\<lambda>\<phi>. \<phi> + pi))"
    by (subst integral_shift) (auto intro!: continuous_intros)
  also have "\<dots> = integral {-(pi/2)..-0} (\<lambda>x. min (d / 2) (sin (-x) * l / 2))" by (simp add: o_def)
  also have "\<dots> = integral {0..pi/2} ?f" (is "_ = ?I") by (subst Henstock_Kurzweil_Integration.integral_reflect_real) simp_all
  also have "\<dots> + \<dots> = 2 * \<dots>" by simp
  also have "?I = integral {0..\<phi>'} ?f + integral {\<phi>'..pi/2} ?f"
    using l d l_ge_d \<phi>'_nonneg \<phi>'_le
    by (intro Henstock_Kurzweil_Integration.integral_combine [symmetric]) (auto intro!: integrable_continuous_real continuous_intros)
  also have "integral {0..\<phi>'} ?f = integral {0..\<phi>'} (\<lambda>x. l / 2 * sin x)"
    using l by (intro integral_cong) (auto simp: min_def field_simps dest: le_phi')
  also have "((\<lambda>x. l / 2 * sin x) has_integral (- (l / 2 * cos \<phi>') - (- (l / 2 * cos 0)))) {0..\<phi>'}"
    using \<phi>'_nonneg
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric] intro!: derivative_eq_intros)
  hence "integral {0..\<phi>'} (\<lambda>x. l / 2 * sin x) = (1 - cos \<phi>') * l / 2"
    by (simp add: has_integral_iff algebra_simps)
  also have "integral {\<phi>'..pi/2} ?f = integral {\<phi>'..pi/2} (\<lambda>_. d / 2)"
    using l by (intro integral_cong) (auto simp: min_def field_simps dest: ge_phi')
  also have "\<dots> = arccos (d / l) * d / 2" using \<phi>'_le d l l_ge_d 
    by (subst arccos_arcsin_eq) (auto simp: field_simps \<phi>'_def)
  also note \<open>cos \<phi>' = sqrt (1 - (d / l)^2)\<close>
  also have "2 * ((1 - sqrt (1 - (d / l)\<^sup>2)) * l / 2 + arccos (d / l) * d / 2) = 
               l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d"
    using d l by (simp add: field_simps)
  finally show "emeasure lborel Buffon_set' =
                  ennreal (l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d)" .
qed

lemma emeasure_set_long: "emeasure lborel Buffon_set = 
        4 * ennreal (l * (1 - sqrt (1 - (d / l)\<^sup>2)) + arccos (d / l) * d)"
  by (simp add: emeasure_buffon_set_conv_buffon_set' emeasure_buffon_set'_long l_ge_d)

lemma prob_long_aux: 
  shows "2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l)) \<ge> 0"
  and   "Buffon {(x, \<phi>). needle l x \<phi> \<inter> {- d / 2, d / 2} \<noteq> {}} = 
           ennreal (2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l)))"
  using emeasure_buffon_set'_long(1)
proof -
  have *: "l * sqrt ((l\<^sup>2 - d\<^sup>2) / l\<^sup>2) + 0 \<le> l + d * arccos (d / l)"
    using d l_ge_d by (intro add_mono mult_nonneg_nonneg arccos_lbound) (auto simp: field_simps)

  have "l / d \<ge> sqrt ((l / d)\<^sup>2 - 1)"
    using l d l_ge_d by (intro real_le_lsqrt) (auto simp: field_simps)
  thus "2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l)) \<ge> 0"
    using d l l_ge_d
    by (intro mult_nonneg_nonneg add_nonneg_nonneg arccos_lbound) (auto simp: field_simps)

  have "emeasure Buffon {(x,\<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}} = 
          ennreal (4 * (l - l * sqrt (1 - (d / l)\<^sup>2) + arccos (d / l) * d)) / ennreal (2 * d * pi)"
    using d l l_ge_d * unfolding buffon_prob_aux emeasure_set_long ennreal_numeral [symmetric]
    by (subst ennreal_mult [symmetric])
       (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg simp: field_simps)
  also have "\<dots> = ennreal ((4 * (l - l * sqrt (1 - (d / l)\<^sup>2) + arccos (d / l) * d)) / (2 * d * pi))"
    using d l * by (subst divide_ennreal) (auto simp: field_simps)
  also have "(4 * (l - l * sqrt (1 - (d / l)\<^sup>2) + arccos (d / l) * d)) / (2 * d * pi) =
               2 / pi * (l / d - l / d * sqrt ((d / l)^2 * ((l / d)^2 - 1)) + arccos (d / l))"
    using d l by (simp add: field_simps)
  also have "l / d * sqrt ((d / l)^2 * ((l / d)^2 - 1)) = sqrt ((l / d) ^ 2 - 1)"
    using d l l_ge_d unfolding real_sqrt_mult real_sqrt_abs by simp
  finally show "emeasure Buffon {(x,\<phi>). needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}} = 
                  ennreal (2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l)))" .
qed

theorem prob_long:
  "\<P>((x,\<phi>) in Buffon. needle l x \<phi> \<inter> {-d/2, d/2} \<noteq> {}) =
     2 / pi * ((l / d) - sqrt ((l / d)\<^sup>2 - 1) + arccos (d / l))"
  using prob_long_aux unfolding emeasure_eq_measure
  by (subst (asm) ennreal_inj) simp_all

end
end

end