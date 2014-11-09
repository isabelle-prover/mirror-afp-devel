(*
  Theory: Measure_Embeddings.thy
  Authors: Manuel Eberl

  Defines measure embeddings with injective functions, i.e. lifting a measure on some values 
  to a measure on "tagged" values (e.g. embed_measure M Inl lifts a measure on values 'a to a 
  measure on the left part of the sum type 'a + 'b)
*)

section {* Embed Measure Spaces with a Function *}

theory Measure_Embeddings
imports Probability Density_Predicates PDF_Misc
begin

lemma vimage_algebra_cong: 
  assumes "X = Y"
  assumes "\<And>x. x \<in> Y \<Longrightarrow> f x = g x"
  assumes "sets M = sets N"
  shows "vimage_algebra X f M = vimage_algebra Y g N"
  by (auto simp: vimage_algebra_def assms simple_image intro!: arg_cong2[where f=sigma])

definition embed_measure :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b measure" where
  "embed_measure M f = measure_of (f ` space M) {f ` A |A. A \<in> sets M} 
                           (\<lambda>A. emeasure M (f -` A \<inter> space M))"

lemma space_embed_measure: "space (embed_measure M f) = f ` space M"
  unfolding embed_measure_def 
  by (subst space_measure_of) (auto dest: sets.sets_into_space)

lemma sets_embed_measure':
  assumes inj: "inj_on f (space M)" 
  shows "sets (embed_measure M f) = {f ` A |A. A \<in> sets M}"
  unfolding embed_measure_def
proof (intro sigma_algebra.sets_measure_of_eq sigma_algebra_iff2[THEN iffD2] conjI allI ballI impI)
  fix s assume "s \<in> {f ` A |A. A \<in> sets M}"
  then obtain s' where s'_props: "s = f ` s'" "s' \<in> sets M" by auto
  hence "f ` space M - s = f ` (space M - s')" using inj
    by (auto dest: inj_onD sets.sets_into_space)
  also have "... \<in> {f ` A |A. A \<in> sets M}" using s'_props by auto
  finally show "f ` space M - s \<in> {f ` A |A. A \<in> sets M}" .
next
  fix A :: "nat \<Rightarrow> _" assume "range A \<subseteq> {f ` A |A. A \<in> sets M}"
  then obtain A' where "\<And>i. A i = f ` A' i" "\<And>i. A' i \<in> sets M"
    by (auto simp: subset_eq choice_iff)
  moreover from this have "(\<Union>x. f ` A' x) = f ` (\<Union>x. A' x)" by blast
  ultimately show "(\<Union>i. A i) \<in> {f ` A |A. A \<in> sets M}" by blast
qed (auto dest: sets.sets_into_space)

lemma the_inv_into_vimage:
  "inj_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> the_inv_into X f -` A \<inter> (f`X) = f ` A"
  by (auto simp: the_inv_into_f_f)

lemma sets_embed_eq_vimage_algebra:
  assumes "inj_on f (space M)"
  shows "sets (embed_measure M f) = sets (vimage_algebra (f`space M) (the_inv_into (space M) f) M)"
  by (auto simp: sets_embed_measure'[OF assms] Pi_iff the_inv_into_f_f assms sets_vimage_algebra2 simple_image
           dest: sets.sets_into_space
           intro!: image_cong the_inv_into_vimage[symmetric])

lemma emeasure_sigma[simp]: "emeasure (sigma \<Omega> A) = (\<lambda>_. 0)"
  unfolding measure_of_def emeasure_def
  by (subst Abs_measure_inverse)
     (auto simp: measure_space_def sigma_algebra_trivial sigma_algebra_sigma_sets
                 positive_def countably_additive_def)

lemma vimage_algebra_Sup_sigma:
  assumes [simp]: "MM \<noteq> {}" and "\<And>M. M \<in> MM \<Longrightarrow> f \<in> X \<rightarrow> space M"
  shows "vimage_algebra X f (Sup_sigma MM) = Sup_sigma (vimage_algebra X f ` MM)"
proof (rule measure_eqI)
  show "sets (vimage_algebra X f (Sup_sigma MM)) = sets (Sup_sigma (vimage_algebra X f ` MM))"
    apply (intro antisym[of "sets A" for A] sets_image_in_sets sets_Sup_in_sets)
    apply (subst space_Sup_sigma)
    using assms
    apply simp
    apply (rule measurable_Sup_sigma2)
    apply simp
    apply (rule measurable_Sup_sigma1)
    apply (rule imageI)
    apply assumption
    apply (rule measurable_vimage_algebra1)
    apply fact
    apply auto []
    apply simp
    apply (auto simp: sets_vimage_algebra2 assms(2))
    apply (rule in_vimage_algebra)
    apply (rule in_Sup_sigma)
    apply assumption +
    done
qed (simp add: vimage_algebra_def Sup_sigma_def)

lemma vimage_algebra_vimage_algebra:
  assumes "f \<in> X \<rightarrow> Y" "g \<in> Y \<rightarrow> space M"
  shows "vimage_algebra X f (vimage_algebra Y g M) = vimage_algebra X (\<lambda>x. g (f x)) M" (is "?L = ?R")  
proof (rule measure_eqI)
  have fg: "(\<lambda>x. g (f x)) \<in> X \<rightarrow> space M" "\<And>A. f -` g -` A \<inter> f -` Y \<inter> X = (\<lambda>x. g (f x)) -` A \<inter> X"
    using assms by auto
  show "sets ?L = sets ?R"
    by (simp add: sets_vimage_algebra2 assms fg simple_image image_comp comp_def del: ex_simps)
qed (simp add: vimage_algebra_def Sup_sigma_def)

lemma sets_embed_measure:
  assumes inj: "inj f" 
  shows "sets (embed_measure M f) = {f ` A |A. A \<in> sets M}"
  using assms by (subst sets_embed_measure') (auto intro!: inj_onI dest: injD)

lemma in_sets_embed_measure: "A \<in> sets M \<Longrightarrow> f ` A \<in> sets (embed_measure M f)"
  unfolding embed_measure_def
  by (intro in_measure_of) (auto dest: sets.sets_into_space)

lemma measurable_embed_measure1[measurable (raw)]:
  assumes g: "(\<lambda>x. g (f x)) \<in> measurable M N" 
  shows "g \<in> measurable (embed_measure M f) N"
  unfolding measurable_def
proof safe
  fix A assume "A \<in> sets N"
  with g have "(\<lambda>x. g (f x)) -` A \<inter> space M \<in> sets M"
    by (rule measurable_sets)
  then have "f ` ((\<lambda>x. g (f x)) -` A \<inter> space M) \<in> sets (embed_measure M f)"
    by (rule in_sets_embed_measure)
  also have "f ` ((\<lambda>x. g (f x)) -` A \<inter> space M) = g -` A \<inter> space (embed_measure M f)"
    by (auto simp: space_embed_measure)
  finally show "g -` A \<inter> space (embed_measure M f) \<in> sets (embed_measure M f)" .
qed (insert measurable_space[OF assms], auto simp: space_embed_measure)

lemma measurable_embed_measure2':
  assumes "inj_on f (space M)" 
  shows "f \<in> measurable M (embed_measure M f)"
proof-
  {
    fix A assume A: "A \<in> sets M"
    also from this have "A = A \<inter> space M" by auto
    also have "... = f -` f ` A \<inter> space M" using A assms
      by (auto dest: inj_onD sets.sets_into_space)
    finally have "f -` f ` A \<inter> space M \<in> sets M" .
  }
  thus ?thesis using assms unfolding embed_measure_def
    by (intro measurable_measure_of) (auto dest: sets.sets_into_space)
qed

lemma measurable_embed_measure2[measurable]:
  assumes [simp]: "inj f" shows "f \<in> measurable M (embed_measure M f)"
  by (auto simp: inj_vimage_image_eq embed_measure_def
           intro!: measurable_measure_of dest: sets.sets_into_space)

lemma embed_measure_eq_distr':
  assumes "inj_on f (space M)"
  shows "embed_measure M f = distr M (embed_measure M f) f"
proof-
  have "distr M (embed_measure M f) f = 
            measure_of (f ` space M) {f ` A |A. A \<in> sets M}
                       (\<lambda>A. emeasure M (f -` A \<inter> space M))" unfolding distr_def
      by (simp add: space_embed_measure sets_embed_measure'[OF assms])
  also have "... = embed_measure M f" unfolding embed_measure_def ..
  finally show ?thesis ..
qed

lemma embed_measure_eq_distr:
    "inj f \<Longrightarrow> embed_measure M f = distr M (embed_measure M f) f"
  by (rule embed_measure_eq_distr') (auto intro!: inj_onI dest: injD)


lemma emeasure_embed_measure':
    assumes "inj_on f (space M)" "A \<in> sets (embed_measure M f)"
    shows "emeasure (embed_measure M f) A = emeasure M (f -` A \<inter> space M)"
  by (subst embed_measure_eq_distr'[OF assms(1)])
     (simp add: emeasure_distr[OF measurable_embed_measure2'[OF assms(1)] assms(2)])

lemma emeasure_embed_measure:
    assumes "inj f" "A \<in> sets (embed_measure M f)"
    shows "emeasure (embed_measure M f) A = emeasure M (f -` A \<inter> space M)"
 using assms by (intro emeasure_embed_measure') (auto intro!: inj_onI dest: injD)

lemma embed_measure_comp: 
  assumes [simp]: "inj f" "inj g"
  shows "embed_measure (embed_measure M f) g = embed_measure M (g \<circ> f)"
proof-
  have [simp]: "inj (\<lambda>x. g (f x))" by (subst o_def[symmetric]) (auto intro: inj_comp)
  have "embed_measure (embed_measure M f) g = 
            distr M (embed_measure (embed_measure M f) g) (g \<circ> f)"
      by (subst (1 2) embed_measure_eq_distr) 
         (simp_all add: distr_distr sets_embed_measure cong: distr_cong)
  also have "... = embed_measure M (g \<circ> f)"
      by (subst (3) embed_measure_eq_distr, simp add: o_def, rule distr_cong)
         (auto simp: sets_embed_measure o_def image_image[symmetric] 
               intro: inj_comp cong: distr_cong)
  finally show ?thesis .
qed

lemma sigma_finite_embed_measure:
  assumes "sigma_finite_measure M" and inj: "inj f"
  shows "sigma_finite_measure (embed_measure M f)"
proof
  case goal1
  from assms(1) interpret sigma_finite_measure M .
  from sigma_finite_countable obtain A where
      A_props: "countable A" "A \<subseteq> sets M" "\<Union>A = space M" "\<And>X. X\<in>A \<Longrightarrow> emeasure M X \<noteq> \<infinity>" by blast
  show ?case
  proof (intro exI[of _ "op ` f`A"] conjI allI)
    from A_props show "countable (op ` f`A)" by auto
    from inj and A_props show "op ` f`A \<subseteq> sets (embed_measure M f)" 
      by (auto simp: sets_embed_measure)
    from A_props and inj show "\<Union>(op ` f`A) = space (embed_measure M f)"
      by (auto simp: space_embed_measure intro!: imageI)
    from A_props and inj show "\<forall>a\<in>op ` f ` A. emeasure (embed_measure M f) a \<noteq> \<infinity>"
      by (intro ballI, subst emeasure_embed_measure)
         (auto simp: inj_vimage_image_eq intro: in_sets_embed_measure)
  qed
qed

lemma embed_measure_count_space: 
    "inj f \<Longrightarrow> embed_measure (count_space A) f = count_space (f`A)"
apply (subst count_space_image, assumption)
apply (subst (1) embed_measure_eq_distr, assumption)
apply (rule distr_cong, simp, subst sets_embed_measure)
apply (auto elim: subset_imageE)
done

lemma sets_embed_measure_alt:
    "inj f \<Longrightarrow> sets (embed_measure M f) = (op`f) ` sets M"
  by (auto simp: sets_embed_measure)

lemma emeasure_embed_measure_image':
  assumes "inj_on f (space M)" "X \<in> sets M"
  shows "emeasure (embed_measure M f) (f`X) = emeasure M X"
proof-
  from assms have "emeasure (embed_measure M f) (f`X) = emeasure M (f -` f ` X \<inter> space M)"
    by (subst emeasure_embed_measure') (auto simp: sets_embed_measure')
  also from assms have "f -` f ` X \<inter> space M = X" by (auto dest: inj_onD sets.sets_into_space)
  finally show ?thesis .
qed

lemma emeasure_embed_measure_image:
    "inj f \<Longrightarrow> X \<in> sets M \<Longrightarrow> emeasure (embed_measure M f) (f`X) = emeasure M X"
  by (simp_all add: emeasure_embed_measure in_sets_embed_measure inj_vimage_image_eq)

lemma embed_measure_eq_iff:
  assumes "inj f"
  shows "embed_measure A f = embed_measure B f \<longleftrightarrow> A = B" (is "?M = ?N \<longleftrightarrow> _")
proof
  from assms have I: "inj (op` f)" by (auto intro: injI dest: injD)
  assume asm: "?M = ?N"
  hence "sets (embed_measure A f) = sets (embed_measure B f)" by simp
  with assms have "sets A = sets B" by (simp only: I inj_image_eq_iff sets_embed_measure_alt)
  moreover {
    fix X assume "X \<in> sets A"
    from asm have "emeasure ?M (f`X) = emeasure ?N (f`X)" by simp
    with `X \<in> sets A` and `sets A = sets B` and assms 
        have "emeasure A X = emeasure B X" by (simp add: emeasure_embed_measure_image)
  }
  ultimately show "A = B" by (rule measure_eqI)
qed simp

lemma the_inv_into_in_Pi: "inj_on f A \<Longrightarrow> the_inv_into A f \<in> f ` A \<rightarrow> A"
  by (auto simp: the_inv_into_f_f)

lemma map_prod_image: "map_prod f g ` (A \<times> B) = (f`A) \<times> (g`B)"
  using map_prod_surj_on[OF refl refl] .

lemma map_prod_vimage: "map_prod f g -` (A \<times> B) = (f-`A) \<times> (g-`B)"
  by auto

lemma embed_measure_prod:
  assumes f: "inj f" and g: "inj g" and [simp]: "sigma_finite_measure M" "sigma_finite_measure N"
  shows "embed_measure M f \<Otimes>\<^sub>M embed_measure N g = embed_measure (M \<Otimes>\<^sub>M N) (\<lambda>(x, y). (f x, g y))"
    (is "?L = _")
  unfolding map_prod_def[symmetric]
proof (rule pair_measure_eqI)
  have fg[simp]: "\<And>A. inj_on (map_prod f g) A" "\<And>A. inj_on f A" "\<And>A. inj_on g A"
    using f g by (auto simp: inj_on_def)
  
  show sets: "sets ?L = sets (embed_measure (M \<Otimes>\<^sub>M N) (map_prod f g))"
    unfolding map_prod_def[symmetric]
    apply (simp add: sets_pair_eq_sets_fst_snd sets_embed_eq_vimage_algebra
      cong: vimage_algebra_cong)
    apply (subst vimage_algebra_Sup_sigma)
    apply (simp_all add: space_pair_measure[symmetric])
    apply (auto simp add: the_inv_into_f_f
                simp del: map_prod_simp
                del: prod_fun_imageE) []
    apply (subst (1 2 3 4 ) vimage_algebra_vimage_algebra)
    apply (simp_all add: the_inv_into_in_Pi Pi_iff[of snd] Pi_iff[of fst] space_pair_measure)
    apply (simp_all add: Pi_iff[of snd] Pi_iff[of fst] the_inv_into_in_Pi vimage_algebra_vimage_algebra
       space_pair_measure[symmetric] map_prod_image[symmetric])
    apply (intro arg_cong[where f=sets] arg_cong[where f=Sup_sigma] arg_cong2[where f=insert] vimage_algebra_cong)
    apply (auto simp: map_prod_image the_inv_into_f_f
                simp del: map_prod_simp del: prod_fun_imageE)
    apply (simp_all add: the_inv_into_f_f space_pair_measure)
    done

  fix A B assume AB: "A \<in> sets (embed_measure M f)" "B \<in> sets (embed_measure N g)"
  moreover have "f -` A \<times> g -` B \<inter> space (M \<Otimes>\<^sub>M N) = (f -` A \<inter> space M) \<times> (g -` B \<inter> space N)"
    by (auto simp: space_pair_measure)
  ultimately show "emeasure (embed_measure M f) A * emeasure (embed_measure N g) B =
                     emeasure (embed_measure (M \<Otimes>\<^sub>M N) (map_prod f g)) (A \<times> B)"
    by (simp add: map_prod_vimage sets[symmetric] emeasure_embed_measure
                  sigma_finite_measure.emeasure_pair_measure_Times)
qed (insert assms, simp_all add: sigma_finite_embed_measure)

lemma density_embed_measure:
  assumes inj: "inj f" and Mg[measurable]: "g \<in> borel_measurable (embed_measure M f)"
  shows "density (embed_measure M f) g = embed_measure (density M (g \<circ> f)) f" (is "?M1 = ?M2")
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets ?M1"
  from inj have Mf[measurable]: "f \<in> measurable M (embed_measure M f)" 
    by (rule measurable_embed_measure2)
  from Mg and X have "emeasure ?M1 X = \<integral>\<^sup>+ x. g x * indicator X x \<partial>embed_measure M f" 
    by (subst emeasure_density) simp_all
  also from X have "... = \<integral>\<^sup>+ x. g (f x) * indicator X (f x) \<partial>M"
    by (subst embed_measure_eq_distr[OF inj], subst nn_integral_distr)
       (auto intro!: borel_measurable_ereal_times borel_measurable_indicator)
  also have "... = \<integral>\<^sup>+ x. g (f x) * indicator (f -` X \<inter> space M) x \<partial>M"
    by (intro nn_integral_cong) (auto split: split_indicator)
  also from X have "... = emeasure (density M (g \<circ> f)) (f -` X \<inter> space M)"
    by (subst emeasure_density) (simp_all add: measurable_comp[OF Mf Mg] measurable_sets[OF Mf])
  also from X and inj have "... = emeasure ?M2 X" 
    by (subst emeasure_embed_measure) (simp_all add: sets_embed_measure)
  finally show "emeasure ?M1 X = emeasure ?M2 X" .
qed (simp_all add: sets_embed_measure inj)

lemma density_embed_measure':
  assumes inj: "inj f" and inv: "\<And>x. f' (f x) = x" and Mg[measurable]: "g \<in> borel_measurable M"
  shows "density (embed_measure M f) (g \<circ> f') = embed_measure (density M g) f"
proof-
  have "density (embed_measure M f) (g \<circ> f') = embed_measure (density M (g \<circ> f' \<circ> f)) f"
    by (rule density_embed_measure[OF inj])
       (rule measurable_comp, rule measurable_embed_measure1, subst measurable_cong, 
        rule inv, rule measurable_ident_sets, simp, rule Mg)
  also have "density M (g \<circ> f' \<circ> f) = density M g"
    by (intro density_cong) (subst measurable_cong, simp add: o_def inv, simp_all add: Mg inv)
  finally show ?thesis .
qed

lemma inj_on_image_subset_iff:
  assumes "inj_on f C" "A \<subseteq> C"  "B \<subseteq> C"
  shows "f ` A \<subseteq> f ` B \<longleftrightarrow> A \<subseteq> B"
proof (intro iffI subsetI)
  fix x assume A: "f ` A \<subseteq> f ` B" and B: "x \<in> A"
  from B have "f x \<in> f ` A" by blast
  with A have "f x \<in> f ` B" by blast
  then obtain y where "f x = f y" and "y \<in> B" by blast
  with assms and B have "x = y" by (auto dest: inj_onD)
  with `y \<in> B` show "x \<in> B" by simp
qed auto
  

lemma AE_embed_measure':
  assumes inj: "inj_on f (space M)"
  shows "(AE x in embed_measure M f. P x) \<longleftrightarrow> (AE x in M. P (f x))"
proof
  let ?M = "embed_measure M f"
  assume "AE x in ?M. P x"
  then obtain A where A_props: "A \<in> sets ?M" "emeasure ?M A = 0" "{x\<in>space ?M. \<not>P x} \<subseteq> A"
    by (force elim: AE_E)
  then obtain A' where A'_props: "A = f ` A'" "A' \<in> sets M" by (auto simp: sets_embed_measure' inj)
  moreover have B: "{x\<in>space ?M. \<not>P x} = f ` {x\<in>space M. \<not>P (f x)}" 
    by (auto simp: inj space_embed_measure)
  from A_props(3) have "{x\<in>space M. \<not>P (f x)} \<subseteq> A'"
    by (subst (asm) B, subst (asm) A'_props, subst (asm) inj_on_image_subset_iff[OF inj])
       (insert A'_props, auto dest: sets.sets_into_space)
  moreover from A_props A'_props have "emeasure M A' = 0"
    by (simp add: emeasure_embed_measure_image' inj)
  ultimately show "AE x in M. P (f x)" by (intro AE_I)
next
  let ?M = "embed_measure M f"
  assume "AE x in M. P (f x)"
  then obtain A where A_props: "A \<in> sets M" "emeasure M A = 0" "{x\<in>space M. \<not>P (f x)} \<subseteq> A"
    by (force elim: AE_E)
  hence "f`A \<in> sets ?M" "emeasure ?M (f`A) = 0" "{x\<in>space ?M. \<not>P x} \<subseteq> f`A"
    by (auto simp: space_embed_measure emeasure_embed_measure_image' sets_embed_measure' inj)
  thus "AE x in ?M. P x" by (intro AE_I)
qed

lemma AE_embed_measure:
  assumes inj: "inj f"
  shows "(AE x in embed_measure M f. P x) \<longleftrightarrow> (AE x in M. P (f x))"
  using assms by (intro AE_embed_measure') (auto intro!: inj_onI dest: injD)


lemma has_density_embed_measure:
  assumes inj: "inj f" and inv: "\<And>x. x \<in> space N \<Longrightarrow> f' (f x) = x"
  shows "has_density (embed_measure M f) (embed_measure N f) (\<delta> \<circ> f') \<longleftrightarrow> has_density M N \<delta>"
        (is "has_density ?M' ?N' ?\<delta>' \<longleftrightarrow> has_density M N \<delta>")
proof
  assume dens: "has_density ?M' ?N' ?\<delta>'"
  show "has_density M N \<delta>"
  proof
    from dens show "space N \<noteq> {}" by (auto simp: space_embed_measure dest: has_densityD)
    from dens have M\<delta>f': "\<delta> \<circ> f' \<in> borel_measurable ?N'" by (rule has_densityD)
    hence M\<delta>f'f: "\<delta> \<circ> f' \<circ> f \<in> borel_measurable N" 
      by (rule_tac measurable_comp, rule_tac measurable_embed_measure2[OF inj])
    thus M\<delta>: "\<delta> \<in> borel_measurable N" by (simp cong: measurable_cong add: inv)
    from dens have "embed_measure M f = density (embed_measure N f) (\<delta> \<circ> f')" by (rule has_densityD)
    also have "... = embed_measure (density N (\<delta> \<circ> f' \<circ> f)) f" 
      by (simp only: density_embed_measure[OF inj M\<delta>f'])
    also have "density N (\<delta> \<circ> f' \<circ> f) = density N \<delta>"
      by (intro density_cong[OF M\<delta>f'f M\<delta>]) (simp_all add: inv)
    finally show "M = density N \<delta>" by (simp add: embed_measure_eq_iff[OF inj])
    fix x assume x: "x \<in> space N"
    with inv have "\<delta> x = ?\<delta>' (f x)" by simp
    also from x have "... \<ge> 0" by (intro has_densityD[OF dens]) (simp add: space_embed_measure)
    finally show "\<delta> x \<ge> 0" .
  qed
next
  assume dens: "has_density M N \<delta>"
  show "has_density ?M' ?N' ?\<delta>'"
  proof
    from dens show "space ?N' \<noteq> {}" by (auto simp: space_embed_measure dest: has_densityD)
    have Mf'f: "(\<lambda>x. f' (f x)) \<in> measurable N N" by (subst measurable_cong[OF inv]) simp_all
    from dens have M\<delta>: "\<delta> \<in> borel_measurable N" by (auto dest: has_densityD)
    from Mf'f and dens show M\<delta>f': "\<delta> \<circ> f' \<in> borel_measurable (embed_measure N f)"
      by (intro measurable_comp) (erule measurable_embed_measure1, rule has_densityD)
    have "embed_measure M f = embed_measure (density N \<delta>) f"
      by (simp only: has_densityD[OF dens])
    also from inv and dens and measurable_comp[OF Mf'f M\<delta>] 
      have "density N \<delta> = density N (?\<delta>' \<circ> f)"
      by (intro density_cong[OF M\<delta>]) (simp add: o_def, simp add: inv o_def)
    also have "embed_measure (density N (?\<delta>' \<circ> f)) f = density (embed_measure N f) (\<delta> \<circ> f')" 
      by (simp only: density_embed_measure[OF inj M\<delta>f', symmetric])
    finally show "embed_measure M f = density (embed_measure N f) (\<delta> \<circ> f')" .
    fix x assume "x \<in> space (embed_measure N f)"
    hence "f' x \<in> space N" by (auto simp: space_embed_measure inv)
    with dens show "?\<delta>' x \<ge> 0" by (auto dest: has_densityD)
  qed
qed

lemma has_density_embed_measure':
  assumes inj: "inj f" and inv: "\<And>x. x \<in> space N \<Longrightarrow> f' (f x) = x" and
          sets_M: "sets M = sets (embed_measure N f)"
  shows "has_density (distr M N f') N (\<delta> \<circ> f) \<longleftrightarrow> has_density M (embed_measure N f) \<delta>"
proof-
  have sets': "sets (embed_measure (distr M N f') f) = sets (embed_measure N f)"
    by (simp add: sets_embed_measure[OF inj])
  have Mff': "(\<lambda>x. f' (f x)) \<in> measurable N N" by (subst measurable_cong[OF inv]) simp_all
  have inv': "\<And>x. x \<in> space M \<Longrightarrow> f (f' x) = x"
    by (subst (asm) sets_eq_imp_space_eq[OF sets_M]) (auto simp: space_embed_measure inv)
  have "M = distr M (embed_measure (distr M N f') f) (\<lambda>x. f (f' x))" 
    by (subst distr_cong[OF refl _ inv', of _ M]) (simp_all add: sets_embed_measure inj sets_M)
  also have "... = embed_measure (distr M N f') f"
    apply (subst (2) embed_measure_eq_distr[OF inj], subst distr_distr)
    apply (subst measurable_cong_sets[OF refl sets'], rule measurable_embed_measure2[OF inj])
    apply (subst measurable_cong_sets[OF sets_M refl], rule measurable_embed_measure1, rule Mff')
    apply (simp cong: distr_cong add: inv)
    done
  finally have M: "M = embed_measure (distr M N f') f" .
  show ?thesis by (subst (2) M, subst has_density_embed_measure[OF inj inv, symmetric])
                  (auto simp: space_embed_measure inv intro!: has_density_cong)
qed

lemma has_density_embed_measure'':
  assumes inj: "inj f" and inv: "\<And>x. x \<in> space N \<Longrightarrow> f' (f x) = x" and
          "has_density M (embed_measure N f) \<delta>"
  shows "has_density (distr M N f') N (\<delta> \<circ> f)"
proof (subst has_density_embed_measure')
  from assms(3) show "sets M = sets (embed_measure N f)" by (auto dest: has_densityD)
qed (insert assms)

lemma has_subprob_density_embed_measure'':
  assumes inj: "inj f" and inv: "\<And>x. x \<in> space N \<Longrightarrow> f' (f x) = x" and
          "has_subprob_density M (embed_measure N f) \<delta>"
  shows "has_subprob_density (distr M N f') N (\<delta> \<circ> f)"
proof (unfold has_subprob_density_def, intro conjI)
  from assms show "has_density (distr M N f') N (\<delta> \<circ> f)"
    by (intro has_density_embed_measure'' has_subprob_density_imp_has_density)
  from assms(3) have "sets M = sets (embed_measure N f)" by (auto dest: has_subprob_densityD)
  hence M: "measurable M = measurable (embed_measure N f)"
    by (intro ext measurable_cong_sets) simp_all
  have "(\<lambda>x. f' (f x)) \<in> measurable N N" by (simp cong: measurable_cong add: inv)
  moreover from assms have "space (embed_measure N f) \<noteq> {}" 
    unfolding has_subprob_density_def has_density_def by simp
  ultimately show "subprob_space (distr M N f')" using assms
    by (intro subprob_space.subprob_space_distr has_subprob_densityD)
       (auto simp: M space_embed_measure intro!: measurable_embed_measure1 dest: has_subprob_densityD)
qed (insert assms)

end
