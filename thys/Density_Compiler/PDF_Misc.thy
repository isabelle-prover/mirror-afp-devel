(*
  Theory: PDF_Misc.thy
  Authors: Manuel Eberl

  A cluttered mess of small auxiliary results that are not directly related to 
  the PDF language and too simple to deserve a file of their own.
  Someone should look through all of this stuff and find out if there is anything in here that
  should be included in HOL-Probability.
*)

section {* Auxiliary Measures *}

theory PDF_Misc
imports Interval_Integral
begin

subsection {* Null measure *}

definition "null_measure M = sigma (space M) (sets M)"

lemma space_null_measure[simp]: "space (null_measure M) = space M"
  by (simp add: null_measure_def)

lemma sets_null_measure[simp]: "sets (null_measure M) = sets M" 
  by (simp add: null_measure_def)

lemma emeasure_null_measure[simp]: "emeasure (null_measure M) X = 0"
  by (cases "X \<in> sets M", rule emeasure_measure_of)
     (auto simp: positive_def countably_additive_def emeasure_notin_sets null_measure_def
           dest: sets.sets_into_space)

lemma subprob_space_null_measure_iff:
    "subprob_space (null_measure M) \<longleftrightarrow> space M \<noteq> {}"
  by (auto intro!: subprob_spaceI dest: subprob_space.subprob_not_empty)

lemma null_measure_eq_density: "null_measure M = density M (\<lambda>_. 0)"
  by (intro measure_eqI) (simp_all add: emeasure_density)

lemma measurable_null_measure_eq1[simp]:
  "measurable (null_measure M) N = measurable M N"
  by (intro measurable_cong_sets) simp_all

lemma measurable_null_measure_eq2[simp]:
  "measurable M (null_measure N) = measurable M N"
  by (intro measurable_cong_sets) simp_all

lemma nn_integral_null_measure[simp]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>null_measure M) = 0"
  by (subst null_measure_eq_density, subst nn_integral_density) simp_all

lemma density_null_measure[simp]:
    "f \<in> borel_measurable M \<Longrightarrow> density (null_measure M) f = null_measure M"
  by (intro measure_eqI) (simp_all add: emeasure_density)
  

subsection {* Borel/Lebesgue on binary product spaces *}

lemma inner_pair_0: "x \<bullet> (0, b) = snd x \<bullet> b" "x \<bullet> (a, 0) = fst x \<bullet> a" by (cases x, simp)+

lemma interval_upperbound_Times: 
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "interval_upperbound (A \<times> B) = (interval_upperbound A, interval_upperbound B)"
proof-
  from assms have fst_image_times': "A = fst ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (SUP x:A \<times> B. x \<bullet> (i, 0)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (SUP x:A. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) fst_image_times') (simp del: fst_image_times add: o_def inner_pair_0)
  moreover from assms have snd_image_times': "B = snd ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (SUP x:A \<times> B. x \<bullet> (0, i)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (SUP x:B. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) snd_image_times') (simp del: snd_image_times add: o_def inner_pair_0)
  ultimately show ?thesis unfolding interval_upperbound_def
      by (subst setsum_Basis_prod_eq) (auto simp add: setsum_prod)
qed

lemma interval_lowerbound_Times: 
  assumes "A \<noteq> {}" and "B \<noteq> {}"
  shows "interval_lowerbound (A \<times> B) = (interval_lowerbound A, interval_lowerbound B)"
proof-
  from assms have fst_image_times': "A = fst ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (INF x:A \<times> B. x \<bullet> (i, 0)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (INF x:A. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) fst_image_times') (simp del: fst_image_times add: o_def inner_pair_0)
  moreover from assms have snd_image_times': "B = snd ` (A \<times> B)" by simp
  have "(\<Sum>i\<in>Basis. (INF x:A \<times> B. x \<bullet> (0, i)) *\<^sub>R i) = (\<Sum>i\<in>Basis. (INF x:B. x \<bullet> i) *\<^sub>R i)"
      by (subst (2) snd_image_times') (simp del: snd_image_times add: o_def inner_pair_0)
  ultimately show ?thesis unfolding interval_lowerbound_def
      by (subst setsum_Basis_prod_eq) (auto simp add: setsum_prod)
qed

lemma content_times[simp]: "content (A \<times> B) = content A * content B"
proof (cases "A \<times> B = {}")
  let ?ub1 = "interval_upperbound" and ?lb1 = "interval_lowerbound"
  let ?ub2 = "interval_upperbound" and ?lb2 = "interval_lowerbound"
  assume nonempty: "A \<times> B \<noteq> {}"
  hence "content (A \<times> B) = (\<Prod>i\<in>Basis. (?ub1 A, ?ub2 B) \<bullet> i - (?lb1 A, ?lb2 B) \<bullet> i)" 
      unfolding content_def by (simp add: interval_upperbound_Times interval_lowerbound_Times)
  also have "... = content A * content B" unfolding content_def using nonempty
    apply (subst Basis_prod_def, subst setprod.union_disjoint, force, force, force, simp)
    apply (subst (1 2) setprod.reindex, auto intro: inj_onI)
    done
  finally show ?thesis .
qed (auto simp: content_def)

lemma lborel_prod: "lborel \<Otimes>\<^sub>M lborel =
    (lborel :: ('a::ordered_euclidean_space \<times> 'b::ordered_euclidean_space) measure)"
proof (rule lborel_eqI[symmetric], clarify)
  fix la ua :: 'a and lb ub :: 'b
  assume lu: "\<And>a b. (a, b) \<in> Basis \<Longrightarrow> (la, lb) \<bullet> (a, b) \<le> (ua, ub) \<bullet> (a, b)"
  have [simp]:
    "\<And>b. b \<in> Basis \<Longrightarrow> la \<bullet> b \<le> ua \<bullet> b"
    "\<And>b. b \<in> Basis \<Longrightarrow> lb \<bullet> b \<le> ub \<bullet> b"
    "inj_on (\<lambda>u. (u, 0)) Basis" "inj_on (\<lambda>u. (0, u)) Basis"
    "(\<lambda>u. (u, 0)) ` Basis \<inter> (\<lambda>u. (0, u)) ` Basis = {}"
    "box (la, lb) (ua, ub) = box la ua \<times> box lb ub"
    using lu[of _ 0] lu[of 0] by (auto intro!: inj_onI simp add: Basis_prod_def ball_Un box_def)
  show "emeasure (lborel \<Otimes>\<^sub>M lborel) (box (la, lb) (ua, ub)) =
      ereal (setprod (op \<bullet> ((ua, ub) - (la, lb))) Basis)"
    by (simp add: lborel.emeasure_pair_measure_Times Basis_prod_def setprod.union_disjoint
                  setprod.reindex)
qed (simp add: borel_prod)


subsection {* Count spaces *}

lemma lborel_neq_count_space[simp]: "lborel \<noteq> count_space (A::('a::ordered_euclidean_space) set)"
proof
  assume asm: "lborel = count_space A"
  have "space lborel = UNIV" by simp
  hence [simp]: "A = UNIV" by (subst (asm) asm) (simp only: space_count_space)
  have "emeasure lborel {undefined::'a} = 1" 
      by (subst asm, subst emeasure_count_space_finite) auto
  moreover have "emeasure lborel {undefined} \<noteq> 1" by simp
  ultimately show False by contradiction
qed


lemma emeasure_count_space_image: 
  assumes "inj_on f X" and "X \<subseteq> N" and "f`X \<subseteq> M"
  shows "emeasure (count_space M) (f`X) = emeasure (count_space N) X"
proof (cases "finite X")
  assume "finite X"
  with assms show ?thesis by (auto simp: card_image)
next
  assume "\<not>finite X"
  with assms show ?thesis 
      by (subst emeasure_count_space_infinite) (auto dest: finite_imageD)
qed

lemma nn_integral_count_space_nat:
  assumes "\<And>x. 0 \<le> f x"
  shows "(\<integral>\<^sup>+x. f x \<partial>count_space UNIV) = (\<Sum>x. f x)"
proof -
  have "f = (\<lambda>i. SUP j. f i * indicator {..<j} i)"
  proof (rule sym, intro ext SUP_eqI)
    fix i y assume "\<And>j. j \<in> UNIV \<Longrightarrow> f i * indicator {..<j} i \<le> y"
    from this[of "Suc i"] show "f i \<le> y" by simp
  qed (simp add: assms split: split_indicator)
  hence "(\<integral>\<^sup>+x. f x \<partial>count_space UNIV) = (\<integral>\<^sup>+i. ... i \<partial>count_space UNIV)" by simp
  also from assms have "... = (SUP j. \<integral>\<^sup>+i. f i * indicator {..<j} i \<partial>count_space UNIV)"
      by (auto intro: nn_integral_monotone_convergence_SUP
               simp: incseq_def le_fun_def split: split_indicator)
  also have "... = (SUP j. \<Sum>i | f i * indicator {..<j} i > 0.  f i * indicator {..<j} i)"
      by (subst nn_integral_count_space)
         (auto intro!: finite_subset[OF _ finite_lessThan] split: split_indicator)
  also have "(\<lambda>j. (\<Sum>i|f i * indicator {..<j} i>0. f i*indicator {..<j} i)) = (\<lambda>j. (\<Sum>i<j. f i))"
  proof
    fix j
    have A: "{i. f i * indicator {..<j} i > 0} = {..<j} \<inter> {i. f i > 0}"
        by (auto split: split_indicator)
    hence "(\<Sum>i | f i * indicator {..<j} i > 0.  f i * indicator {..<j} i) =
              (\<Sum>i\<in>{..<j} \<inter> {i. f i > 0}.  f i * indicator {..<j} i)" by simp
    also have "... = (\<Sum>i<j. if f i > 0 then f i * indicator {..<j} i else 0)"
      by (subst setsum.inter_restrict) simp_all
    also from assms have "... = (\<Sum>i<j. f i)"
        by (intro setsum.cong) (auto simp: not_less eq_iff)
    finally show "(\<Sum>i | f i * indicator {..<j} i > 0.  f i * indicator {..<j} i) = (\<Sum>i<j. f i)" .
  qed
  also from assms have "(SUP j. ... j) = (\<Sum>i. f i)" by (simp add: suminf_ereal_eq_SUP)
  finally show ?thesis  .
qed

lemma integral_count_space_nat:
  assumes "integrable (count_space UNIV) (f :: _ \<Rightarrow> real)"
  shows "lebesgue_integral (count_space UNIV) f = (\<Sum>x. f x)"
proof-
  have "lebesgue_integral (count_space UNIV) f =
          real ((\<integral>\<^sup>+x. max 0 (ereal (f x)) \<partial>count_space UNIV)) - 
          real ((\<integral>\<^sup>+x. max 0 (ereal (-f x)) \<partial>count_space UNIV))"
    by (subst real_lebesgue_integral_def[OF assms], subst (1 2) nn_integral_max_0[symmetric])
       (simp_all add: max_def if_distrib zero_ereal_def) 
  also have I1: "(\<integral>\<^sup>+x. max 0 (ereal (f x)) \<partial>count_space UNIV) = (\<Sum>x. ereal (max 0 (f x)))"
    by (subst nn_integral_count_space_nat) (simp_all add: max_def if_distrib zero_ereal_def)
  also have "... = ereal (\<Sum>x. max 0 (f x))"
    by (rule suminf_ereal, simp, subst I1[symmetric])
       (insert assms, simp_all add: real_integrable_def nn_integral_max_0)
  also have I2: "(\<integral>\<^sup>+x. max 0 (ereal (-f x)) \<partial>count_space UNIV) = (\<Sum>x. ereal (max 0 (-f x)))"
    by (subst nn_integral_count_space_nat) (simp_all add: max_def if_distrib zero_ereal_def)
  also have "... = ereal (\<Sum>x. max 0 (-f x))"
    by (rule suminf_ereal, simp, subst I2[symmetric])
       (insert assms, simp_all add: real_integrable_def nn_integral_max_0)
  also have "real (ereal (\<Sum>x. max 0 (f x))) - real (ereal (\<Sum>x. max 0 (- f x))) =
               (\<Sum>x. max 0 (f x)) - (\<Sum>x. max 0 (-f x))" by simp
  also from assms have "... = (\<Sum>x. max 0 (f x) - max 0 (-f x))"
    by (intro suminf_diff summable_ereal)
       (simp, subst I1[symmetric], simp add: real_integrable_def nn_integral_max_0,
        simp, subst I2[symmetric], simp add: real_integrable_def nn_integral_max_0)
  also have "(\<lambda>x. max 0 (f x) - max 0 (-f x)) = f" by (rule ext) (simp add: max_def)
  finally show ?thesis .
qed

lemma count_space_image_restrict:
  assumes "inj f" "f`A \<subseteq> B"
  shows "restrict_space (count_space B) (f`A) = 
             distr (count_space A) (restrict_space (count_space B) (f`A)) f" (is "?M = ?N")
proof  (rule measure_eqI)
  from assms show "sets ?M = sets ?N" by (simp add: sets_restrict_space)
  fix X assume A: "X \<in> sets ?M"
  from A assms have "f ` A \<inter> X = X"  by (auto simp: sets_restrict_space)
  with A assms have "emeasure ?M X = emeasure (count_space B) X"
      by (auto simp: sets_restrict_space emeasure_restrict_space)
  also from A assms have "X = f ` (f -` X \<inter> A)" by (auto simp: sets_restrict_space)
  hence "emeasure (count_space B) X = emeasure (count_space B) (f ` (f -` X \<inter> A))" by simp
  also from assms have "... = emeasure (count_space A) (f -` X \<inter> A)"
      by (subst emeasure_count_space_image) (auto intro: inj_onI dest: injD)
  also from A and assms have "... = emeasure ?N X" 
    by (subst emeasure_distr) (simp_all add: space_restrict_space Int_absorb2)
  finally show "emeasure ?M X = emeasure ?N X" .
qed

lemma count_space_image:
  assumes "inj f"
  shows "count_space (f`A) = distr (count_space A) (count_space (f`A)) f" (is "?M = ?N")
proof-
  have A: "restrict_space (count_space (f`A)) (f`A) = count_space (f`A)"
    by (subst restrict_count_space) simp
  from assms show ?thesis 
      by (subst A[symmetric], subst count_space_image_restrict) (simp_all add: A)
qed

lemma emeasure_inter_arith_ereal:
    "indicator A x * indicator B x = (indicator (A \<inter> B) x :: ereal)"
  by (simp split: split_indicator)

lemma return_count_space_eq_density:
    "return (count_space M) x = density (count_space M) (indicator {x})" (is "?M1 = ?M2")
  by (rule measure_eqI) 
     (auto simp: emeasure_inter_arith_ereal emeasure_density split: split_indicator)


subsection {* Measurability *}

lemma measurable_If':
  assumes "f \<in> measurable M N"
  assumes "g \<in> measurable M N"
  assumes "Measurable.pred M p"
  shows "(\<lambda>x. if p x then f x else g x) \<in> measurable M N"
proof-
  from assms(3) have "p -` {True} \<inter> space M \<in> sets M" by (rule measurable_sets) simp
  also have " p -` {True} \<inter> space M = {x\<in>space M. p x}" by auto
  finally show ?thesis using assms(1,2) by (intro measurable_If)
qed

lemma measurable_sgn[measurable]: "(sgn :: real \<Rightarrow> real) \<in> borel_measurable borel"
  unfolding sgn_real_def[abs_def] by auto

lemma measurable_pow':
  shows "(\<lambda>(a::real,b). a ^ b) \<in> borel_measurable (borel \<Otimes>\<^sub>M count_space UNIV)" 
            (is "_ \<in> borel_measurable ?M")
proof-
  {
    fix f :: "real \<Rightarrow> real" and M :: "real measure"
    let ?M = "M \<Otimes>\<^sub>M count_space UNIV"
    assume assms: "f \<in> borel_measurable M" "\<And>x. x \<in> space M \<Longrightarrow> f x \<ge> (0 :: real)"
    def to_real_pair \<equiv> "\<lambda>x::_ \<times> nat. (f (fst x), real (snd x))"
    let ?h = "(\<lambda>x::real\<times>real. fst x powr snd x)"
    let ?h' = "(\<lambda>x. if to_real_pair x \<in> {0<..} \<times> UNIV then ?h (to_real_pair x) else 0)"
    let ?h'' = "(\<lambda>x. if x \<in> {x\<in>space M. f x = 0}\<times>{0} then 1 else ?h' x)"
    from borel_measurable_vimage[OF assms(1), of 0]
      have A: "{x\<in>space M. f x = 0}\<times>{0::nat} \<in> sets ?M" using assms(1)
          by (intro pair_measureI) auto
    have A: "{x\<in>space M. f x = 0} \<times> {0::nat} \<inter> space ?M \<in> sets ?M"
        by (intro sets.Int) (simp_all add: A)
    from assms(1) have "?h' \<in> borel_measurable (M \<Otimes>\<^sub>M count_space UNIV)"
        by (intro borel_measurable_continuous_on_open continuous_on_powr 
                  continuous_on_fst continuous_on_snd continuous_on_id)
           (auto simp: not_less open_Times to_real_pair_def)
    hence "?h'' \<in> borel_measurable ?M"
        by (rule_tac measurable_If_set) (simp, simp, rule A)
    also have A: "\<And>x. x \<in> space M \<Longrightarrow> f x \<le> 0 \<Longrightarrow> f x = 0" by (subst eq_iff) (blast intro: assms(2))
    have "\<And>x. x\<in>space ?M \<Longrightarrow> ?h'' x = (\<lambda>(a,b). f a ^ b) x"
        by (auto simp: powr_realpow to_real_pair_def not_less space_pair_measure dest: A)
    note measurable_cong[OF this]
    finally have "(\<lambda>(a,b). f a ^ b) \<in> borel_measurable (M \<Otimes>\<^sub>M count_space UNIV)" .
  } note aux = this

  let ?f = "\<lambda>(a::real,b). (abs a) ^ b" and ?g = "\<lambda>(a::real,b). sgn a * abs a ^ b"
  have [measurable]: "?f \<in> borel_measurable ?M" by (auto intro: aux)
  have [measurable]: "?g \<in> borel_measurable ?M" 
    apply (subst measurable_split_conv)
    apply (intro borel_measurable_times measurable_compose[OF _ measurable_sgn] measurable_fst)
    apply (subst measurable_split_conv[symmetric], rule aux, simp_all)
    done
  have "(\<lambda>(a,b). a ^ b) = (\<lambda>x. if even (snd x) then ?f x else ?g x)"
      by (rule ext) (auto simp: power_even_abs sgn_real_def abs_real_def odd_pos)
  also have "... \<in> borel_measurable ?M" using assms by measurable
  finally show ?thesis .
qed

lemma measurable_pow[measurable]:
  assumes "(f :: _ \<Rightarrow> real) \<in> measurable M borel" and "g \<in> measurable M (count_space UNIV)"
  shows "(\<lambda>x. f x ^ g x) \<in> borel_measurable M" 
proof-
  have "(\<lambda>x. f x ^ g x) = (\<lambda>(a,b). a^b) \<circ> (\<lambda>x. (f x, g x))"
      by (rule ext) (simp add: o_def)
  also from assms have "... \<in> borel_measurable M"
      by (blast intro: measurable_comp measurable_Pair measurable_pow')
  finally show ?thesis .
qed


subsection {* Miscellaneous *}

lemma density_1: "density M (\<lambda>_. 1) = M"
  by (intro measure_eqI) (auto simp: emeasure_density)

lemma emeasure_density_add:
  assumes X: "X \<in> sets M" 
  assumes Mf[measurable]: "f \<in> borel_measurable M"
  assumes Mg[measurable]: "g \<in> borel_measurable M"
  assumes nonnegf: "\<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0"
  assumes nonnegg: "\<And>x. x \<in> space M \<Longrightarrow> g x \<ge> 0"
  shows "emeasure (density M f) X + emeasure (density M g) X = 
           emeasure (density M (\<lambda>x. f x + g x)) X"
  using assms
  apply (subst (1 2 3) emeasure_density, simp_all) []
  apply (subst nn_integral_add[symmetric], simp_all) []
  apply (intro nn_integral_cong, simp split: split_indicator)
  done

lemma lborel_distr_uminus: "distr lborel borel uminus = (lborel :: real measure)"
  by (subst lborel_real_affine[of "-1" 0]) 
     (auto simp: density_1 one_ereal_def[symmetric])

lemma lborel_distr_mult: 
  assumes "(c::real) \<noteq> 0"
  shows "distr lborel borel (op * c) = density lborel (\<lambda>_. inverse \<bar>c\<bar>)"
proof-
  have "distr lborel borel (op * c) = distr lborel lborel (op * c)" by (simp cong: distr_cong)
  also from assms have "... = density lborel (\<lambda>_. inverse \<bar>c\<bar>)"
    by (subst lborel_real_affine[of "inverse c" 0]) (auto simp: o_def distr_density_distr)
  finally show ?thesis .
qed

lemma lborel_distr_mult': 
  assumes "(c::real) \<noteq> 0"
  shows "lborel = density (distr lborel borel (op * c)) (\<lambda>_. abs c)"
proof-
  have "lborel = density lborel (\<lambda>_. 1)" by (rule density_1[symmetric])
  also from assms have "(\<lambda>_. 1 :: ereal) = (\<lambda>_. inverse (abs c) * abs c)" by (intro ext) simp
  also have "density lborel ... = density (density lborel (\<lambda>_. inverse (abs c))) (\<lambda>_. abs c)"
    by (subst density_density_eq) auto
  also from assms have "density lborel (\<lambda>_. inverse (abs c)) = distr lborel borel (op * c)"
    by (rule lborel_distr_mult[symmetric])
  finally show ?thesis .
qed

lemma lborel_distr_plus: "distr lborel borel (op + c) = (lborel :: real measure)"
  by (subst lborel_real_affine[of 1 c]) (auto simp: density_1 one_ereal_def[symmetric])

lemma distr_lborel: "distr M lborel f = distr M borel f"
  by (simp cong: distr_cong)

lemma DERIV_inverse'':
  assumes "x \<noteq> 0"
  shows "(inverse has_real_derivative (-inverse x * inverse x)) (at x within S)"
proof- 
  from assms have "(inverse has_real_derivative -(inverse x ^ Suc (Suc 0))) (at x within S)"
    by (rule DERIV_inverse)
  also have "inverse x ^ Suc (Suc 0) = inverse x * inverse x" by (simp add: field_simps)
  finally show ?thesis by simp
qed

lemma DERIV_neg_inverse'':
  assumes "x \<noteq> 0"
  shows "((\<lambda>x. -inverse x) has_real_derivative (inverse x * inverse x)) (at x within S)"
  using DERIV_minus[OF DERIV_inverse''[OF assms], of S] by simp

lemma range_exp: "range (exp :: real \<Rightarrow> real) = {x. x > 0}"
proof (intro equalityI subsetI)
  fix x :: real assume "x \<in> {x. x > 0}"
  hence "x = exp (ln x)" by simp
  thus "x \<in> range exp" by blast
qed auto

(* TODO Move? *)
lemma countable_imp_null_set_lborel: "countable A \<Longrightarrow> A \<in> null_sets lborel"
proof (cases "A = {}")
  assume A: "A \<noteq> {}" "countable A"
  from range_from_nat_into[OF this] have B: "A = (\<Union>i. {from_nat_into A i})" by auto
  have "emeasure lborel A = 0" "A \<in> sets lborel" by (subst B, force intro: emeasure_UN_eq_0)+
  thus ?thesis by blast
qed simp

lemma finite_imp_null_set_lborel: "finite A \<Longrightarrow> A \<in> null_sets lborel"
  by (intro countable_imp_null_set_lborel countable_finite)

lemma measurableI:
  "\<lbrakk>f \<in> space M \<rightarrow> space N; \<And>X. X \<in> sets N \<Longrightarrow> f -` X \<inter> space M \<in> sets M\<rbrakk> \<Longrightarrow> f \<in> measurable M N"
unfolding measurable_def by blast

lemma measurableD:
  assumes "f \<in> measurable M N"
  shows "f \<in> space M \<rightarrow> space N" "X \<in> sets N \<Longrightarrow> f -` X \<inter> space M \<in> sets M"
using assms unfolding measurable_def by blast+

lemma sets_PiM_cong:
    "\<lbrakk>I = J; \<And>x. x \<in> I \<Longrightarrow> M x = N x\<rbrakk> \<Longrightarrow> sets (PiM I M) = sets (PiM J N)"
  by (simp add: sets_PiM cong: PiE_cong prod_algebra_cong)

lemma Pi_cong_sets:
    "\<lbrakk>I = J; \<And>x. x \<in> I \<Longrightarrow> M x = N x\<rbrakk> \<Longrightarrow> Pi I M = Pi J N"
  unfolding Pi_def by auto 

lemma extend_measure_cong:
  assumes "\<Omega> = \<Omega>'" "I = I'" "G = G'" "\<And>i. i \<in> I' \<Longrightarrow> \<mu> i = \<mu>' i"
  shows "extend_measure \<Omega> I G \<mu> = extend_measure \<Omega>' I' G' \<mu>'"
  unfolding extend_measure_def by (auto simp add: assms)

lemma PiM_cong:
  assumes "I = J" "\<And>x. x \<in> I \<Longrightarrow> M x = N x"
  shows "PiM I M = PiM J N"
unfolding PiM_def
proof (rule extend_measure_cong)
  case goal1 show ?case using assms
    by (subst assms(1), intro PiE_cong[of J "\<lambda>i. space (M i)" "\<lambda>i. space (N i)"]) simp_all
next
  case goal2
  have "\<And>K. K \<subseteq> J \<Longrightarrow> (\<Pi> j\<in>K. sets (M j)) = (\<Pi> j\<in>K. sets (N j))"
    using assms by (intro Pi_cong_sets) auto
  thus ?case by (auto simp: assms)
next
  case goal3 show ?case using assms 
    by (intro ext) (auto simp: prod_emb_def dest: PiE_mem)
next
  case (goal4 x)
  thus ?case using assms 
    by (auto intro!: setprod.cong split: split_if_asm)
qed

lemma measurable_restrict_subset':
  assumes "J \<subseteq> L" "\<And>x. x \<in> J \<Longrightarrow> M x = N x"
  shows "(\<lambda>f. restrict f J) \<in> measurable (Pi\<^sub>M L M) (Pi\<^sub>M J N)"
proof-
  from assms(1) have "(\<lambda>f. restrict f J) \<in> measurable (Pi\<^sub>M L M) (Pi\<^sub>M J M)"
    by (rule measurable_restrict_subset)
  also from assms(2) have "measurable (Pi\<^sub>M L M) (Pi\<^sub>M J M) = measurable (Pi\<^sub>M L M) (Pi\<^sub>M J N)"
    by (intro sets_PiM_cong measurable_cong_sets) simp_all
  finally show ?thesis .
qed

lemma measurable_fun_upd:
  assumes "y \<in> space (M i)"
  shows "(\<lambda>\<sigma>. \<sigma>(i := y)) \<in> measurable (PiM I M) (PiM (insert i I) M)"
proof-
  have "(\<lambda>\<sigma>. \<sigma>(i := y)) = (\<lambda>(\<sigma>,y). \<sigma>(i := y)) \<circ> (\<lambda>\<sigma>. (\<sigma>, y))" by auto
  also have "... \<in> measurable (PiM I M) (PiM (insert i I) M)"
    by (rule measurable_comp, rule measurable_Pair2'[OF assms], rule measurable_add_dim)
  finally show ?thesis .
qed  

lemma merge_upd:
    "merge (insert x I) J (\<sigma>(x := y), \<rho>) = (merge I J (\<sigma>,\<rho>))(x := y)"
  by (intro ext) (auto simp: merge_def)

lemma merge_upd':
    " x \<in> I \<Longrightarrow> merge I J (\<sigma>(x := y), \<rho>) = (merge (I-{x}) J (\<sigma>,\<rho>))(x := y)"
  by (intro ext) (auto simp: merge_def)

lemma (in pair_sigma_finite) Fubini':
  assumes "split f \<in> borel_measurable (M1 \<Otimes>\<^sub>M M2)"
  shows "(\<integral>\<^sup>+ y. \<integral>\<^sup>+ x. f x y \<partial>M1 \<partial>M2) = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. f x y \<partial>M2 \<partial>M1)"
  using Fubini[OF assms] by simp

lemma (in prob_space) prob_space_density_1:
    "prob_space (density M (\<lambda>_. 1))"
  by (rule prob_spaceI) (simp add: emeasure_density emeasure_space_1)

lemma subprob_space_imp_sigma_finite: "subprob_space M \<Longrightarrow> sigma_finite_measure M"
proof-
  assume "subprob_space M"
  thus "sigma_finite_measure M" unfolding subprob_space_def finite_measure_def by simp
qed

lemma prob_space_imp_sigma_finite: "prob_space M \<Longrightarrow> sigma_finite_measure M"
proof-
  assume "prob_space M"
  thus "sigma_finite_measure M" unfolding prob_space_def finite_measure_def by simp
qed

lemma nn_integral_count_space_singleton:
    "f y \<ge> 0 \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>count_space {y}) = f y"
  by (subst nn_integral_count_space_finite) (auto simp: max_def)

lemma prob_space_count_space_singleton[simp]: "prob_space (count_space {x})"
  by (rule prob_spaceI) auto

lemma indicator_neq_infty[simp]: "indicator A x \<noteq> (\<infinity> :: ereal)" 
    by (auto split: split_indicator)

lemma nn_integral_over_space: 
    "(\<integral>\<^sup>+x. f x * indicator (space M) x \<partial>M) = (\<integral>\<^sup>+x. f x \<partial>M)"
  by (rule nn_integral_cong) simp

lemma emeasure_density_space: 
    "f \<in> borel_measurable M \<Longrightarrow> emeasure (density M f) (space M) = \<integral>\<^sup>+x. f x\<partial>M"
  by (subst emeasure_density) (simp_all add: nn_integral_over_space)

lemma space_PiM_insert:
  assumes "j \<notin> I"
  shows "space (\<Pi>\<^sub>M i\<in>insert j I. M i) = {\<sigma>(j := x) |\<sigma> x. \<sigma> \<in> space (\<Pi>\<^sub>M i\<in>I. M i) \<and> x \<in> space (M j)}"
      (is "?S1 = ?S2")
proof (intro equalityI subsetI)
  fix \<sigma> assume "\<sigma> \<in> ?S1"
  with assms have "\<sigma>(j := undefined) \<in> space (\<Pi>\<^sub>M i\<in>I. M i)" "\<sigma> j \<in> space (M j)"
      by (auto simp add: space_PiM PiE_mem)
  moreover have "\<sigma> = (\<sigma>(j := undefined))(j := \<sigma> j)" by simp
  ultimately show "\<sigma> \<in> ?S2" by blast
next
  fix \<sigma> assume "\<sigma> \<in> ?S2"
  then obtain \<sigma>' x where "\<sigma> = \<sigma>'(j := x)" "\<sigma>' \<in> space (\<Pi>\<^sub>M i\<in>I. M i)" "x \<in> space (M j)" by blast
  hence "\<sigma>'(j := x) \<in> (\<Pi>\<^sub>E j\<in>insert j I. space (M j))" 
      by (intro PiE_fun_upd) (simp_all add: space_PiM)
  thus "\<sigma> \<in> ?S1" by (simp add: space_PiM `\<sigma> = \<sigma>'(j := x)`)
qed

context product_sigma_finite
begin

lemma product_nn_integral_insert':
  assumes "finite I" "i \<notin> I" "f \<in> borel_measurable (Pi\<^sub>M (insert i I) M)"
  shows "(\<integral>\<^sup>+\<sigma>. f \<sigma> \<partial>Pi\<^sub>M (insert i I) M) = \<integral>\<^sup>+x. \<integral>\<^sup>+\<sigma>. f (\<sigma>(i := x)) \<partial>Pi\<^sub>M I M \<partial>M i"
proof-
  interpret pair_sigma_finite "M i" "Pi\<^sub>M I M"
    unfolding pair_sigma_finite_def using assms(1)
    by (intro conjI sigma_finite_measures sigma_finite)
  def f' \<equiv> "\<lambda>(x,\<sigma>). f (\<sigma>(i := x))"
  from measurable_compose[OF measurable_add_dim assms(3)] 
    have measurable_f': "f' \<in> borel_measurable (M i \<Otimes>\<^sub>M Pi\<^sub>M I M)" 
    by (subst measurable_pair_swap_iff) (simp add: case_prod_distrib f'_def)
  from assms have "(\<integral>\<^sup>+\<sigma>. f \<sigma> \<partial>Pi\<^sub>M (insert i I) M) = \<integral>\<^sup>+\<sigma>. \<integral>\<^sup>+x. f (\<sigma>(i := x)) \<partial>M i \<partial>Pi\<^sub>M I M"
    by (rule product_nn_integral_insert)
  also have "... = \<integral>\<^sup>+\<sigma>. \<integral>\<^sup>+x. f'(x,\<sigma>) \<partial>M i \<partial>Pi\<^sub>M I M" unfolding f'_def by simp
  also from measurable_f' have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+\<sigma>. f' (x, \<sigma>) \<partial>Pi\<^sub>M I M \<partial>M i"
    by (simp add: Fubini)
  finally show ?thesis by (simp add: f'_def)
qed

lemma product_nn_integral_pair:
  assumes [measurable]: "split f \<in> borel_measurable (M x \<Otimes>\<^sub>M M y)"
  assumes xy: "x \<noteq> y"
  shows "(\<integral>\<^sup>+\<sigma>. f (\<sigma> x) (\<sigma> y) \<partial>PiM {x, y} M) = (\<integral>\<^sup>+z. f (fst z) (snd z) \<partial>(M x \<Otimes>\<^sub>M M y))"
proof-
  interpret psm: pair_sigma_finite "M x" "M y"
    unfolding pair_sigma_finite_def using sigma_finite_measures by simp_all
  have "{x, y} = {y, x}" by auto
  also have "(\<integral>\<^sup>+\<sigma>. f (\<sigma> x) (\<sigma> y) \<partial>PiM {y, x} M) = (\<integral>\<^sup>+y. \<integral>\<^sup>+\<sigma>. f (\<sigma> x) y \<partial>PiM {x} M \<partial>M y)"
    using xy by (subst product_nn_integral_insert') simp_all
  also have "... = (\<integral>\<^sup>+y. \<integral>\<^sup>+x. f x y \<partial>M x \<partial>M y)"
    by (intro nn_integral_cong, subst product_nn_integral_singleton) simp_all
  also have "... = (\<integral>\<^sup>+z. f (fst z) (snd z) \<partial>(M x \<Otimes>\<^sub>M M y))"
    by (subst psm.nn_integral_snd[symmetric]) simp_all
  finally show ?thesis .
qed

end

(* TODO: Move and possibly rename.*)
lemma measurable_add_dim':
  "(\<lambda>(f, y). f(i := y)) \<in> measurable (Pi\<^sub>M I M \<Otimes>\<^sub>M N) (Pi\<^sub>M (insert i I) (M(i := N)))"
    (is "?f \<in> measurable ?P ?I")
proof (rule measurable_PiM_single)
  fix j A assume j: "j \<in> insert i I" and A: "A \<in> sets ((M(i:=N)) j)"
  hence "{\<omega> \<in> space ?P. (\<lambda>(f, x). fun_upd f i x) \<omega> j \<in> A} = 
             (if j = i then space (Pi\<^sub>M I M) \<times> A else ((\<lambda>x. x j) \<circ> fst) -` A \<inter> space ?P)"
      using sets.sets_into_space[OF A] by (auto simp: space_pair_measure)
  also have "\<dots> \<in> sets ?P" using A j 
      by (cases "j = i") (auto intro!: measurable_sets[OF measurable_comp, 
                                           OF _ measurable_component_singleton])
  finally show "{\<omega> \<in> space ?P. case_prod (\<lambda>f. fun_upd f i) \<omega> j \<in> A} \<in> sets ?P" .
qed (auto simp: space_pair_measure space_PiM PiE_def)

(* The current measurable_add_dim is a special case of the measurable_add_dim' above: *)
lemma "(\<lambda>(f, y). f(i := y)) \<in> measurable (Pi\<^sub>M I M \<Otimes>\<^sub>M M i) (Pi\<^sub>M (insert i I) M)"
    using measurable_add_dim'[where M = M and N = "M i"] by simp

lemma measurable_add_dim'':
  "i \<in> I \<Longrightarrow> (\<lambda>(f, y). f(i := y)) \<in> measurable (Pi\<^sub>M I M \<Otimes>\<^sub>M N) (Pi\<^sub>M I (M(i := N)))"
    by (subst (2) insert_absorb[symmetric], assumption) (rule measurable_add_dim')

(* End TODO *)

lemma range_int: "range int = {n. n \<ge> 0}"
proof (intro equalityI subsetI)
  fix n :: int assume "n \<in> {n. n \<ge> 0}"
  hence "n = int (nat n)" by simp
  thus "n \<in> range int" by blast
qed auto

lemma nn_integral_nat_int:
  assumes "\<And>x. (x::int) < 0 \<Longrightarrow> f x = 0" "\<And>x. f x \<ge> 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>count_space UNIV) = (\<integral>\<^sup>+x. f x \<partial>count_space (UNIV :: nat set))"
proof-
  let ?M = "restrict_space (count_space UNIV) (int`UNIV)"
  have "(\<integral>\<^sup>+x. f x \<partial>count_space (UNIV :: nat set)) = (\<integral>\<^sup>+x. f x \<partial>distr (count_space UNIV) ?M int)"
            by (rule nn_integral_distr[symmetric]) 
               (auto intro: measurable_restrict_space1 simp: space_restrict_space)
  also have "distr (count_space UNIV) ?M int = restrict_space (count_space UNIV) (range int)"
      by (rule count_space_image_restrict[symmetric]) (auto intro: injI)
  also from assms have "(\<integral>\<^sup>+x. f x \<partial>...) = (\<integral>\<^sup>+x. f x * indicator (range int) x \<partial>count_space UNIV)"
    by (intro nn_integral_restrict_space) (auto simp: range_int)
  also from assms have "... = (\<integral>\<^sup>+x. f x \<partial>count_space UNIV)" 
    by (intro nn_integral_cong) (auto split: split_indicator simp: range_int)
  finally show ?thesis ..
qed

lemma suminf_ereal_finite:
  assumes "summable f"
  shows "(\<Sum>x. ereal (f x)) \<noteq> \<infinity>" "(\<Sum>x. ereal (f x)) \<noteq> -\<infinity>"
proof-
  from assms obtain x where "f sums x" by blast
  hence "(\<lambda>x. ereal (f x)) sums ereal x" by (simp add: sums_ereal)
  from sums_unique[OF this] have "(\<Sum>x. ereal (f x)) = ereal x" ..
  thus "(\<Sum>x. ereal (f x)) \<noteq> \<infinity>" "(\<Sum>x. ereal (f x)) \<noteq> -\<infinity>" by simp_all
qed

lemma nn_integral_count_space_singleton':
  assumes "y \<in> A" "f y \<ge> 0"
  shows "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>count_space A) = f y"
proof-
  have "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>count_space A) = (\<integral>\<^sup>+x. f y * indicator {y} x \<partial>count_space A)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also from assms have "... = f y * (\<integral>\<^sup>+x. indicator {y} x \<partial>count_space A)"
    by (intro nn_integral_cmult) auto
  also from assms have "... = f y * emeasure (count_space A) {y}" 
    by (subst nn_integral_indicator) auto
  also from assms have "... = f y" 
    by (subst emeasure_count_space_finite) (auto simp: one_ereal_def[symmetric])
  finally show ?thesis .
qed

lemma measure_discrete_eqI:
  assumes "countable (space M)"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> {x} \<in> sets M"
  assumes "sets M = sets N"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> emeasure M {x} = emeasure N {x}"
  shows "M = N"
proof (rule measure_eqI)
  show "sets M = sets N" by fact
  fix X assume X: "X \<in> sets M"
  hence subset: "X \<subseteq> space M" by (rule sets.sets_into_space)
  have X_UN: "X = (\<Union>x\<in>X. {x})" by simp
  from assms have "countable (space M \<inter> X)" by simp
  also from X have "space M \<inter> X = X" by simp
  finally have countable: "countable X" .
  hence "emeasure M X = \<integral>\<^sup>+i. emeasure M {i} \<partial>count_space X" using subset
    by (subst X_UN, subst emeasure_UN_countable) 
       (auto simp: disjoint_family_on_def intro!: assms(2)) 
  also from subset have "... = \<integral>\<^sup>+i. emeasure N {i} \<partial>count_space X"
    by (intro nn_integral_cong assms(4)) auto
  also from countable have "... = emeasure N X" using subset assms
    by (subst X_UN, subst emeasure_UN_countable) (auto simp: disjoint_family_on_def)
  finally show "emeasure M X = emeasure N X" .
qed

lemma density_discrete:
  assumes "countable A" "sets N = Pow A" "\<And>x. f x \<ge> 0"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = emeasure N {x}"
  shows "density (count_space A) f = N"
proof (rule measure_discrete_eqI)
  fix x assume x: "x \<in> space (density (count_space A) f)"
  with assms have "emeasure (density (count_space A) f) {x} = f x"
    by (subst emeasure_density, simp, simp, subst nn_integral_count_space_singleton') auto
  also from x and assms have "... = emeasure N {x}" by simp
  finally show "emeasure (density (count_space A) f) {x} = emeasure N {x}" .
qed (insert assms, auto)

lemma distr_density_discrete:
  assumes "countable A"
  assumes "g \<in> measurable M (count_space A)"
  defines "f \<equiv> \<lambda>x. \<integral>\<^sup>+t. (if g t = x then 1 else 0) \<partial>M"
  assumes "\<And>x.  x \<in> space M \<Longrightarrow> g x \<in> A"
  shows "density (count_space A) f = distr M (count_space A) g"
proof (rule density_discrete)
  fix x assume x: "x \<in> A"
  have "f x = integral\<^sup>N M (indicator (g -` {x} \<inter> space M))" (is "_ = ?I") unfolding f_def
    by (intro nn_integral_cong) (simp split: split_indicator)
  also from x have "g -` {x} \<inter> space M \<in> sets M" by (intro measurable_sets[OF assms(2)]) simp
  hence "?I = emeasure M (g -` {x} \<inter> space M)" unfolding f_def
    by (subst nn_integral_indicator[symmetric]) blast+
  also from x and assms have "... = emeasure (distr M (count_space A) g) {x}"
    by (subst emeasure_distr) simp_all
  finally show "f x = emeasure (distr M (count_space A) g) {x}" .
qed (insert assms, auto simp: nn_integral_nonneg)

lemma distr_density_discrete':
  fixes f'
  assumes "countable A"
  assumes "f' \<in> borel_measurable M"
  assumes "g \<in> measurable M (count_space A)"
  defines "f \<equiv> \<lambda>x. \<integral>\<^sup>+t. (if g t = x then 1 else 0) * f' t \<partial>M"
  assumes "\<And>x.  x \<in> space M \<Longrightarrow> g x \<in> A"
  shows "density (count_space A) (\<lambda>x. f x) = distr (density M f') (count_space A) g"
proof (rule density_discrete)
  fix x assume x: "x \<in> A"
  have "f x = \<integral>\<^sup>+t. indicator (g -` {x} \<inter> space M) t * f' t \<partial>M" (is "_ = ?I") unfolding f_def
    by (intro nn_integral_cong) (simp split: split_indicator)
  also from x have in_sets: "g -` {x} \<inter> space M \<in> sets M" 
    by (intro measurable_sets[OF assms(3)]) simp
  have "?I = emeasure (density M f') (g -` {x} \<inter> space M)" unfolding f_def
    by (subst emeasure_density[OF assms(2) in_sets], subst mult.commute) (rule refl)
  also from assms(3) x have "... = emeasure (distr (density M f') (count_space A) g) {x}"
    by (subst emeasure_distr) simp_all
  finally show "f x = emeasure (distr (density M f') (count_space A) g) {x}" .
qed (insert assms, auto simp: nn_integral_nonneg)


lemma strict_mono_inv:
  fixes f :: "('a::linorder) \<Rightarrow> ('b::linorder)"
  assumes "strict_mono f" and "surj f" and inv: "\<And>x. g (f x) = x"
  shows "strict_mono g"
proof
  fix x y :: 'b assume "x < y"
  from `surj f` obtain x' y' where [simp]: "x = f x'" "y = f y'" by blast
  with `x < y` and `strict_mono f` have "x' < y'" by (simp add: strict_mono_less)
  with inv show "g x < g y" by simp
qed

definition "mono_on f A \<equiv> \<forall>r s. r \<in> A \<and> s \<in> A \<and> r \<le> s \<longrightarrow> f r \<le> f s"

lemma mono_onI:
  "(\<And>r s. r \<in> A \<Longrightarrow> s \<in> A \<Longrightarrow> r \<le> s \<Longrightarrow> f r \<le> f s) \<Longrightarrow> mono_on f A"
  unfolding mono_on_def by simp

lemma mono_onD:
  "\<lbrakk>mono_on f A; r \<in> A; s \<in> A; r \<le> s\<rbrakk> \<Longrightarrow> f r \<le> f s"
  unfolding mono_on_def by simp

lemma mono_imp_mono_on: "mono f \<Longrightarrow> mono_on f A"
  unfolding mono_def mono_on_def by auto

lemma mono_on_subset: "mono_on f A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> mono_on f B"
  unfolding mono_on_def by auto

definition "strict_mono_on f A \<equiv> \<forall>r s. r \<in> A \<and> s \<in> A \<and> r < s \<longrightarrow> f r < f s"

lemma strict_mono_onI:
  "(\<And>r s. r \<in> A \<Longrightarrow> s \<in> A \<Longrightarrow> r < s \<Longrightarrow> f r < f s) \<Longrightarrow> strict_mono_on f A"
  unfolding strict_mono_on_def by simp

lemma strict_mono_onD:
  "\<lbrakk>strict_mono_on f A; r \<in> A; s \<in> A; r < s\<rbrakk> \<Longrightarrow> f r < f s"
  unfolding strict_mono_on_def by simp

lemma mono_on_greaterD:
  assumes "mono_on g A" "x \<in> A" "y \<in> A" "g x > (g (y::_::linorder) :: _ :: linorder)"
  shows "x > y"
proof (rule ccontr)
  assume "\<not>x > y"
  hence "x \<le> y" by (simp add: not_less)
  from assms(1-3) and this have "g x \<le> g y" by (rule mono_onD)
  with assms(4) show False by simp
qed

lemma nn_integral_indicator_singleton[simp]:
  "(\<integral>\<^sup>+(x::real). f x * indicator {y} x \<partial>lborel) = 0"
proof-
  have "(\<integral>\<^sup>+(x::real). f x * indicator {y} x \<partial>lborel) = (\<integral>\<^sup>+(x::real). 0 \<partial>lborel)"
    by (intro nn_integral_cong_AE AE_I'[of "{y}"] finite_imp_null_set_lborel)
       (auto split: split_indicator)
  thus ?thesis by simp
qed

lemma nn_integral_indicator_singleton'[simp]:
  "(\<integral>\<^sup>+(x::real). ereal ((f x :: real) * indicator {y} x) \<partial>lborel) = 0"
proof-
  have "(\<integral>\<^sup>+(x::real). ereal (f x * indicator {y} x) \<partial>lborel) =
          (\<integral>\<^sup>+(x::real). ereal (f x) * indicator {y} x \<partial>lborel)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  thus ?thesis by simp
qed

lemma set_borel_measurable_singleton[simp]:
  "set_borel_measurable borel {a} (f :: real \<Rightarrow> real)"
proof-
  have "(\<lambda>x. f a * indicator {a} x) \<in> borel_measurable borel"
    by (rule borel_measurable_times) simp_all
  also have "(\<lambda>x. f a * indicator {a} x) = (\<lambda>x. f x * indicator {a} x)"
    by (intro ext) (simp split: split_indicator)
  finally show ?thesis by (simp add: mult.commute)
qed

lemma set_borel_measurable_singleton'[simp]:
  "(\<lambda>x. (f :: real \<Rightarrow> ereal) x * indicator {a} x) \<in> borel_measurable borel"
proof-
  have "(\<lambda>x. f a * indicator {a} x) \<in> borel_measurable borel"
    by (rule borel_measurable_ereal_times) simp_all
  also have "(\<lambda>x. f a * indicator {a} x) = (\<lambda>x. f x * indicator {a} x)"
    by (intro ext) (simp split: split_indicator)
  finally show ?thesis .
qed


lemma strict_mono_on_imp_inj_on:
  assumes "strict_mono_on (f :: (_ :: linorder) \<Rightarrow> (_ :: preorder)) A"
  shows "inj_on f A"
proof (rule inj_onI)
  fix x y assume "x \<in> A" "y \<in> A" "f x = f y"
  thus "x = y"
    by (cases x y rule: linorder_cases)
       (auto dest: strict_mono_onD[OF assms, of x y] strict_mono_onD[OF assms, of y x]) 
qed

lemma strict_mono_on_leD:
  assumes "strict_mono_on (f :: (_ :: linorder) \<Rightarrow> _ :: preorder) A" "x \<in> A" "y \<in> A" "x \<le> y"
  shows "f x \<le> f y"
proof (insert le_less_linear[of y x], elim disjE)
  assume "x < y"
  with assms have "f x < f y" by (rule_tac strict_mono_onD[OF assms(1)]) simp_all
  thus ?thesis by (rule less_imp_le)
qed (insert assms, simp)

lemma strict_mono_on_imp_mono_on: 
  "strict_mono_on (f :: (_ :: linorder) \<Rightarrow> _ :: preorder) A \<Longrightarrow> mono_on f A"
  by (rule mono_onI, rule strict_mono_on_leD)

lemma continuous_image_atLeastAtMost:
  assumes "continuous_on {a::real..b} f" "mono_on f {a..b}" "a \<le> b"
  shows "f ` {a..b} = {f a..f b :: real}"
proof (intro equalityI subsetI)
  fix y assume "y \<in> {f a..f b}"
  hence "y \<ge> f a" "y \<le> f b" by auto
  from IVT'[OF this `a \<le> b` assms(1)] obtain x where "x \<ge> a" "x \<le> b" "y = f x" by blast
  thus "y \<in> f ` {a..b}" by simp
qed (insert `a \<le> b`, auto intro!: mono_onD[OF assms(2)])

lemma strict_mono_on_eqD:
  fixes f :: "(_ :: linorder) \<Rightarrow> (_ :: preorder)"
  assumes "strict_mono_on f A" "f x = f y" "x \<in> A" "y \<in> A"
  shows "y = x"
  using assms by (rule_tac linorder_cases[of x y]) (auto dest: strict_mono_onD)


lemma mono_on_imp_deriv_nonneg:
  assumes mono: "mono_on f A" and deriv: "(f has_real_derivative D) (at x)"
  assumes "x \<in> interior A"
  shows "D \<ge> 0"
proof (rule tendsto_le_const)
  let ?A' = "(\<lambda>y. y - x) ` interior A"
  from deriv show "((\<lambda>h. (f (x + h) - f x) / h) ---> D) (at 0)"
      by (simp add: field_has_derivative_at has_field_derivative_def)
  from mono have mono': "mono_on f (interior A)" by (rule mono_on_subset) (rule interior_subset)

  show "eventually (\<lambda>h. (f (x + h) - f x) / h \<ge> 0) (at 0)"
  proof (subst eventually_at_topological, intro exI conjI ballI impI)
    have "open (interior A)" by simp
    hence "open (op + (-x) ` interior A)" by (rule open_translation)
    also have "(op + (-x) ` interior A) = ?A'" by auto
    finally show "open ?A'" .
  next
    from `x \<in> interior A` show "0 \<in> ?A'" by auto
  next
    fix h assume "h \<in> ?A'"
    hence "x + h \<in> interior A" by auto
    with mono' and `x \<in> interior A` show "(f (x + h) - f x) / h \<ge> 0"
      by (cases h rule: linorder_cases[of _ 0])
         (simp_all add: divide_nonpos_neg divide_nonneg_pos mono_onD field_simps)
  qed
qed simp


lemma closure_Iii: 
  assumes "a < b"
  shows "closure {a<..<b::real} = {a..b}"
proof-
  have "{a<..<b} = ball ((a+b)/2) ((b-a)/2)" by (auto simp: dist_real_def field_simps not_less)
  also from assms have "closure ... = cball ((a+b)/2) ((b-a)/2)" by (intro closure_ball) simp
  also have "... = {a..b}" by (auto simp: dist_real_def field_simps not_less)
  finally show ?thesis .
qed

lemma continuous_ge_on_Iii:
  assumes "continuous_on {c..d} g" "\<And>x. x \<in> {c<..<d} \<Longrightarrow> g x \<ge> a" "c < d" "x \<in> {c..d}"
  shows "g (x::real) \<ge> (a::real)"
proof-
  from assms(3) have "{c..d} = closure {c<..<d}" by (rule closure_Iii[symmetric])
  also from assms(2) have "{c<..<d} \<subseteq> (g -` {a..} \<inter> {c..d})" by auto
  hence "closure {c<..<d} \<subseteq> closure (g -` {a..} \<inter> {c..d})" by (rule closure_mono)
  also from assms(1) have "closed (g -` {a..} \<inter> {c..d})"
    by (auto simp: continuous_on_closed_vimage)
  hence "closure (g -` {a..} \<inter> {c..d}) = g -` {a..} \<inter> {c..d}" by simp
  finally show ?thesis using `x \<in> {c..d}` by auto 
qed 


lemma measurable_sets_borel:
    "\<lbrakk>f \<in> measurable borel M; A \<in> sets M\<rbrakk> \<Longrightarrow> f -` A \<in> sets borel"
  by (drule (1) measurable_sets) simp

(* TODO: maybe this should be a simp lemma *)
lemma nn_integral_set_ereal:
    "(\<integral>\<^sup>+x. ereal (f x) * indicator A x \<partial>M) = (\<integral>\<^sup>+x. ereal (f x * indicator A x) \<partial>M)"
  by (rule nn_integral_cong) (simp split: split_indicator)

lemma continuous_on_imp_isCont:
    "\<lbrakk>continuous_on A f; x \<in> A; open A\<rbrakk> \<Longrightarrow> isCont f x"
  unfolding isCont_def continuous_on_def
  by (subst Lim_within_open[symmetric]) auto


(* TODO MOVE *)
lemma borel_set_induct[consumes 1, case_names interval compl union]:
  assumes "A \<in> sets borel" 
  assumes int: "\<And>a b. P {a..b}" and compl: "\<And>A. A \<in> sets borel \<Longrightarrow> P A \<Longrightarrow> P (-A)" and
          un: "\<And>f. disjoint_family f \<Longrightarrow> (\<And>i. f i \<in> sets borel) \<Longrightarrow>  (\<And>i. P (f i)) \<Longrightarrow> P (\<Union>i::nat. f i)"
  shows "P (A::real set)"
proof-
  let ?G = "range (\<lambda>(a,b). {a..b::real})"
  have "Int_stable ?G" "?G \<subseteq> Pow UNIV" "A \<in> sigma_sets UNIV ?G" 
      using assms(1) by (auto simp add: borel_eq_atLeastAtMost Int_stable_def)
  thus ?thesis using int[of 1 0]
  proof (induction rule: sigma_sets_induct_disjoint) 
    case (union f)
      from union.hyps(2) have "\<And>i. f i \<in> sets borel" by (auto simp: borel_eq_atLeastAtMost)
      with union show ?case by (auto intro: un)
  qed (auto intro: int compl simp: Compl_eq_Diff_UNIV[symmetric] borel_eq_atLeastAtMost)
qed

lemma borel_set_induct'[consumes 1, case_names empty interval compl union]:
  assumes "A \<in> sets borel" "P {}" "\<And>a b. a \<le> b \<Longrightarrow> P {a..b}" "\<And>A. A \<in> sets borel \<Longrightarrow> P A \<Longrightarrow> P (-A)" 
          "\<And>f. disjoint_family f \<Longrightarrow> (\<And>i. f i \<in> sets borel) \<Longrightarrow>  (\<And>i. P (f i)) \<Longrightarrow> P (\<Union>i::nat. f i)"
  shows "P (A::real set)"
proof (insert assms(1), induction rule: borel_set_induct)
  case (interval a b)
    show ?case by (cases "a \<le> b") (auto intro: assms)
qed (auto intro: assms)
(* END TODO *)


(* TODO MOVE *)
lemma closure_contains_Sup:
  fixes S :: "real set"
  assumes "S \<noteq> {}" "bdd_above S"
  shows "Sup S \<in> closure S"
proof-
  have "Inf (uminus ` S) \<in> closure (uminus ` S)" 
      using assms by (intro closure_contains_Inf) auto
  also have "Inf (uminus ` S) = -Sup S" by (simp add: Inf_real_def)
  also have "closure (uminus ` S) = uminus ` closure S"
      by (rule sym, intro closure_injective_linear_image) (auto intro: linearI)
  finally show ?thesis by auto
qed

lemma closed_contains_Sup:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> closed S \<Longrightarrow> Sup S \<in> S"
  by (subst closure_closed[symmetric], assumption, rule closure_contains_Sup)
(* END TODO *)

lemma set_integral_eq_nn_integral:
  assumes "(\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0)" "(\<lambda>x. max (f x) 0 * indicator A x) \<in> borel_measurable M"
  shows  "LINT x:A|M. f x = real (\<integral>\<^sup>+ x. ereal (f x) * indicator A x \<partial>M)"
proof-
  have "LINT x:A|M. f x = LINT x:A|M. max (f x) 0"
    by (intro integral_cong) (auto split: split_indicator dest: assms(1))
  also from assms have "... = real (\<integral>\<^sup>+ x. ereal (max (f x) 0 * indicator A x) \<partial>M)"
    by (subst integral_eq_nn_integral) (simp_all add: mult.commute)
  also have "(\<integral>\<^sup>+ x. ereal (max (f x) 0 * indicator A x) \<partial>M) = (\<integral>\<^sup>+ x. ereal (f x) * indicator A x \<partial>M)"
    by (intro nn_integral_cong) (auto split: split_indicator simp del: ereal_max dest: assms(1))
  finally show ?thesis .
qed

lemma continuous_on_ivl_vimage_sets_borel:
  assumes "continuous_on {a..b} f" "B \<in> sets borel" "(a::real) \<le> b"
  shows "f -` B \<inter> {a..b} \<in> sets borel"
proof-
  let ?f' = "\<lambda>x. if x < a then f a else if x > b then f b else f x"
  have "continuous_on ({..a} \<union> ({b..} \<union> {a..b})) ?f'" using assms
      by (intro continuous_on_If) (auto intro: continuous_on_subset[OF continuous_on_const])
  also have "{..a} \<union> ({b..} \<union> {a..b}) = UNIV" by auto
  finally have "?f' \<in> borel_measurable borel" by (rule borel_measurable_continuous_on1)
  from this and `B \<in> sets borel` have "?f' -` B \<in> sets borel" by (rule measurable_sets_borel)
  hence "?f' -` B \<inter> {a..b} \<in> sets borel" by simp
  also have "?f' -` B \<inter> {a..b} = f -` B \<inter> {a..b}" by (auto split: split_if) 
  finally show ?thesis .
qed

lemma set_measurable_continuous_on_ivl:
  assumes "continuous_on {a..b} (f :: real \<Rightarrow> real)"
  shows "set_borel_measurable borel {a..b} f"
proof (cases "a \<le> b")
  assume "a \<le> b"
  show ?thesis
  proof (rule borel_measurableI)
    fix A :: "real set" assume "open A"
    hence A_borel: "A \<in> sets borel" by simp
    let ?f = "\<lambda>x. indicator {a..b} x *\<^sub>R f x"
    have "?f -` A = f -` A \<inter> {a..b} \<union> (if 0 \<in> A then -{a..b} else {})"
        by (auto simp: indicator_def split: split_if_asm)
    also have "... \<in> sets borel" using assms A_borel `a \<le> b`
        by (intro sets.Un, blast intro: continuous_on_ivl_vimage_sets_borel, auto)
    finally show "?f -` A \<inter> space borel \<in> sets borel" by simp
  qed
qed simp

lemma real_of_ereal_SUP:
  assumes not_empty: "A \<noteq> {}" and f_nonneg: "\<And>x. f x \<ge> 0" and not_inf: "(SUP x:A. f x) \<noteq> \<infinity>"
  shows "real (SUP x:A. f x) = (SUP x:A. real (f x :: ereal))"
proof (rule antisym)
  from not_empty obtain y where "y \<in> A" by blast
  have A: "\<And>x. x \<in> A \<Longrightarrow> real (SUP x:A. f x) \<ge> real (f x)"
      by (intro real_of_ereal_positive_mono assms SUP_upper)
  have sup_nonneg: "(SUP x:A. f x) \<ge> 0"
      by (rule order.trans, rule f_nonneg, rule SUP_upper, rule `y \<in> A`)

  from A show "real (SUP x:A. f x) \<ge> (SUP x:A. real (f x))"  
      by (intro cSUP_least not_empty) 
  from A have bdd: "bdd_above ((\<lambda>x. real (f x)) ` A)" by (auto simp: bdd_above_def)
  have "ereal (SUP x:A. real (f x)) \<ge> (SUP x:A. f x)"
  proof (rule SUP_least)
    fix x assume "x \<in> A"
    hence not_inf': "f x \<noteq> \<infinity>" by (subst ereal_infty_less[symmetric])
                                  (rule order.strict_trans1, erule SUP_upper[of x], simp add: not_inf)
    from `x \<in> A` have "ereal (SUP x:A. real (f x)) \<ge> ereal (real (f x))" 
        by (auto intro: cSUP_upper assms bdd)
    hence "ereal (SUP x:A. real (f x)) \<ge> ereal (real (f x))" by simp
    also have "ereal (real (f x)) = f x" by (subst ereal_real') (auto simp: not_inf' f_nonneg)
    finally show "f x \<le> ereal (SUP x:A. real (f x))" .
  qed
  hence "real (ereal (SUP x:A. real (f x))) \<ge> real (SUP x:A. f x)" 
      by (intro real_of_ereal_positive_mono sup_nonneg) simp_all
  thus "(SUP x:A. real (f x)) \<ge> real (SUP x:A. f x)" by simp
qed

lemma interior_real_semiline':
  fixes a :: real
  shows "interior {..a} = {..<a}"
proof -
  {
    fix y
    assume "a > y"
    then have "y \<in> interior {..a}"
      apply (simp add: mem_interior)
      apply (rule_tac x="(a-y)" in exI)
      apply (auto simp add: dist_norm)
      done
  }
  moreover
  {
    fix y
    assume "y \<in> interior {..a}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {..a}"
      using mem_interior_cball[of y "{..a}"] by auto
    moreover from e have "y + e \<in> cball y e"
      by (auto simp add: cball_def dist_norm)
    ultimately have "a \<ge> y + e" by auto
    then have "a > y" using e by auto
  }
  ultimately show ?thesis by auto
qed

lemma interior_atLeastAtMost_real: "interior {a..b} = {a<..<b :: real}"
proof-
  have "{a..b} = {a..} \<inter> {..b}" by auto
  also have "interior ... = {a<..} \<inter> {..<b}" 
    by (simp add: interior_real_semiline interior_real_semiline')
  also have "... = {a<..<b}" by auto
  finally show ?thesis .
qed

lemma has_real_derivative_imp_continuous_on:
  assumes "\<And>x. x \<in> A \<Longrightarrow> (f has_real_derivative f' x) (at x)"
  shows "continuous_on A f"
  apply (intro differentiable_imp_continuous_on, unfold differentiable_on_def)
  apply (intro ballI Deriv.differentiableI)
  apply (rule has_field_derivative_subset[OF assms])
  apply simp_all
  done

end
