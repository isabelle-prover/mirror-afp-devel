section \<open>Indexed Products of Probability Mass Functions\<close>

theory Product_PMF_Ext
  imports Main Probability_Ext "HOL-Probability.Product_PMF" Universal_Hash_Families.Universal_Hash_Families_More_Independent_Families
begin

hide_const "Isolated.discrete"

text \<open>This section introduces a restricted version of @{term "Pi_pmf"} where the default value is @{term "undefined"}
and contains some additional results about that case in addition to @{theory "HOL-Probability.Product_PMF"}\<close>

abbreviation prod_pmf where "prod_pmf I M \<equiv> Pi_pmf I undefined M"

lemma pmf_prod_pmf: 
  assumes "finite I"
  shows "pmf (prod_pmf I M) x = (if x \<in> extensional I then \<Prod>i \<in> I. (pmf (M i)) (x i) else 0)"
  by (simp add:  pmf_Pi[OF assms(1)] extensional_def)

lemma PiE_defaut_undefined_eq: "PiE_dflt I undefined M = PiE I M" 
  by (simp add:PiE_dflt_def PiE_def extensional_def Pi_def set_eq_iff) blast

lemma set_prod_pmf:
  assumes "finite I"
  shows "set_pmf (prod_pmf I M) = PiE I (set_pmf \<circ> M)"
  by (simp add:set_Pi_pmf[OF assms] PiE_defaut_undefined_eq)

text \<open>A more general version of @{thm [source] "measure_Pi_pmf_Pi"}.\<close>
lemma prob_prod_pmf': 
  assumes "finite I"
  assumes "J \<subseteq> I"
  shows "measure (measure_pmf (Pi_pmf I d M)) (Pi J A) = (\<Prod> i \<in> J. measure (M i) (A i))"
proof -
  have a:"Pi J A = Pi I (\<lambda>i. if i \<in> J then A i else UNIV)"
    using assms by (simp add:Pi_def set_eq_iff, blast)
  show ?thesis
    using assms
    by (simp add:if_distrib  a measure_Pi_pmf_Pi[OF assms(1)] prod.If_cases[OF assms(1)] Int_absorb1)
qed

lemma prob_prod_pmf_slice:
  assumes "finite I"
  assumes "i \<in> I"
  shows "measure (measure_pmf (prod_pmf I M)) {\<omega>. P (\<omega> i)} = measure (M i) {\<omega>. P \<omega>}"
  using prob_prod_pmf'[OF assms(1), where J="{i}" and M="M" and A="\<lambda>_. Collect P"]
  by (simp add:assms Pi_def)


definition restrict_dfl where "restrict_dfl f A d = (\<lambda>x. if x \<in> A then f x else d)"

lemma pi_pmf_decompose:
  assumes "finite I"
  shows "Pi_pmf I d M = map_pmf (\<lambda>\<omega>. restrict_dfl (\<lambda>i. \<omega> (f i) i) I d) (Pi_pmf (f ` I) (\<lambda>_. d) (\<lambda>j. Pi_pmf (f -` {j} \<inter> I) d M))"
proof -
  have fin_F_I:"finite (f ` I)" using assms by blast

  have "finite I \<Longrightarrow> ?thesis"
    using fin_F_I
  proof (induction "f ` I" arbitrary: I rule:finite_induct)
    case empty
    then show ?case by (simp add:restrict_dfl_def)
  next
    case (insert x F)
    have a: "(f -` {x} \<inter> I) \<union> (f -` F \<inter> I) = I"
      using insert(4) by blast
    have b: "F = f `  (f -` F \<inter> I) " using insert(2,4) 
      by (auto simp add:set_eq_iff image_def vimage_def) 
    have c: "finite (f -` F \<inter> I)" using insert by blast
    have d: "\<And>j. j \<in> F \<Longrightarrow> (f -` {j} \<inter> (f -` F \<inter> I)) = (f -` {j} \<inter> I)"
      using insert(4) by blast 

    have " Pi_pmf I d M = Pi_pmf ((f -` {x} \<inter> I) \<union> (f -` F \<inter> I)) d M"
      by (simp add:a)
    also have "... = map_pmf (\<lambda>(g, h) i. if i \<in> f -` {x} \<inter> I then g i else h i) 
      (pair_pmf (Pi_pmf (f -` {x} \<inter> I) d M) (Pi_pmf (f -` F \<inter> I) d M))"
      using insert by (subst Pi_pmf_union) auto
    also have "... = map_pmf (\<lambda>(g,h) i. if f i = x \<and> i \<in> I then g i else if f i \<in> F \<and> i \<in> I then h (f i) i else d)
      (pair_pmf (Pi_pmf (f -` {x} \<inter> I) d M) (Pi_pmf F (\<lambda>_. d) (\<lambda>j. Pi_pmf (f -` {j} \<inter> (f -` F \<inter> I)) d M)))"
      by (simp add:insert(3)[OF b c] map_pmf_comp case_prod_beta' apsnd_def map_prod_def 
          pair_map_pmf2 b[symmetric] restrict_dfl_def) (metis fst_conv snd_conv)
    also have "... = map_pmf (\<lambda>(g,h) i. if i \<in> I then (h(x := g)) (f i) i else d) 
      (pair_pmf (Pi_pmf (f -` {x} \<inter> I) d M) (Pi_pmf F (\<lambda>_. d) (\<lambda>j. Pi_pmf (f -` {j} \<inter> I) d M)))" 
      using insert(4) d
      by (intro arg_cong2[where f="map_pmf"] ext) (auto simp add:case_prod_beta' cong:Pi_pmf_cong) 
    also have "... = map_pmf (\<lambda>\<omega> i. if i \<in> I then \<omega> (f i) i else d) (Pi_pmf (insert x F) (\<lambda>_. d) (\<lambda>j. Pi_pmf (f -` {j} \<inter> I) d M))"
      by (simp add:Pi_pmf_insert[OF insert(1,2)] map_pmf_comp case_prod_beta')
    finally show ?case by (simp add:insert(4) restrict_dfl_def)
  qed
  thus ?thesis using assms by blast
qed

lemma restrict_dfl_iter: "restrict_dfl (restrict_dfl f I d) J d = restrict_dfl f (I \<inter> J) d"
  by (rule ext, simp add:restrict_dfl_def)

lemma indep_vars_restrict':
  assumes "finite I"
  shows "prob_space.indep_vars (Pi_pmf I d M) (\<lambda>_. discrete) (\<lambda>i \<omega>. restrict_dfl \<omega> (f -` {i} \<inter> I) d) (f ` I)"
proof -
  let ?Q = "(Pi_pmf (f ` I) (\<lambda>_. d) (\<lambda>i. Pi_pmf (I \<inter> f -` {i}) d M))"
  have a:"prob_space.indep_vars ?Q (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) (f ` I)"
    using assms by (intro indep_vars_Pi_pmf, blast)
  have b: "AE x in measure_pmf ?Q. \<forall>i\<in>f ` I. x i = restrict_dfl (\<lambda>i. x (f i) i) (I \<inter> f -` {i}) d"
    using assms
    by (auto simp add:PiE_dflt_def restrict_dfl_def AE_measure_pmf_iff set_Pi_pmf comp_def Int_commute)
  have "prob_space.indep_vars ?Q (\<lambda>_. discrete) (\<lambda>i x. restrict_dfl (\<lambda>i. x (f i) i) (I \<inter> f -` {i}) d) (f ` I)"
    by (rule prob_space.indep_vars_cong_AE[OF prob_space_measure_pmf b a],  simp)
  thus ?thesis
    using prob_space_measure_pmf 
    by (auto intro!:prob_space.indep_vars_distr simp:pi_pmf_decompose[OF assms, where f="f"]  
        map_pmf_rep_eq comp_def restrict_dfl_iter Int_commute) 
qed

lemma indep_vars_restrict_intro':
  assumes "finite I"
  assumes "\<And>i \<omega>. i \<in> J \<Longrightarrow> X' i \<omega> = X' i (restrict_dfl \<omega> (f -` {i} \<inter> I) d)"
  assumes "J = f ` I"
  assumes "\<And>\<omega> i. i \<in> J \<Longrightarrow>  X' i \<omega> \<in> space (M' i)"
  shows "prob_space.indep_vars (measure_pmf (Pi_pmf I d p)) M' (\<lambda>i \<omega>. X' i \<omega>) J"
proof -
  define M where "M \<equiv> measure_pmf (Pi_pmf I d p)"
  interpret prob_space "M"
    using M_def prob_space_measure_pmf by blast
  have "indep_vars (\<lambda>_. discrete) (\<lambda>i x. restrict_dfl x (f -` {i} \<inter> I) d) (f ` I)" 
    unfolding M_def  by (rule indep_vars_restrict'[OF assms(1)])
  hence "indep_vars M' (\<lambda>i \<omega>. X' i (restrict_dfl \<omega> ( f -` {i} \<inter> I) d)) (f ` I)"
    using assms(4)
    by (intro indep_vars_compose2[where Y="X'" and N="M'" and M'="\<lambda>_. discrete"])  (auto simp:assms(3))
  hence "indep_vars M' (\<lambda>i \<omega>. X' i \<omega>) (f ` I)"
    using assms(2)[symmetric]
    by (simp add:assms(3) cong:indep_vars_cong)
  thus ?thesis
    unfolding M_def using assms(3) by simp 
qed

lemma  
  fixes f :: "'b \<Rightarrow> ('c :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "i \<in> I"
  assumes "integrable (measure_pmf (M i)) f"
  shows  integrable_Pi_pmf_slice: "integrable (Pi_pmf I d M) (\<lambda>x. f (x i))"
  and expectation_Pi_pmf_slice: "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. f (x i)) = integral\<^sup>L (M i) f"
proof -
  have a:"distr (Pi_pmf I d M) (M i) (\<lambda>\<omega>. \<omega> i) = distr (Pi_pmf I d M) discrete (\<lambda>\<omega>. \<omega> i)"
    by (rule distr_cong, auto)

  have b: "measure_pmf.random_variable (M i) borel f"
    using assms(3) by simp

  have c:"integrable (distr (Pi_pmf I d M) (M i) (\<lambda>\<omega>. \<omega> i)) f" 
    using assms(1,2,3)
    by (subst a, subst map_pmf_rep_eq[symmetric], subst Pi_pmf_component, auto)

  show "integrable (Pi_pmf I d M) (\<lambda>x. f (x i))"
    by (rule integrable_distr[where f="f" and M'="M i"])  (auto intro: c)

  have "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. f (x i)) = integral\<^sup>L (distr (Pi_pmf I d M) (M i) (\<lambda>\<omega>. \<omega> i)) f"
    using b by (intro integral_distr[symmetric], auto)
  also have "... =  integral\<^sup>L (map_pmf (\<lambda>\<omega>. \<omega> i) (Pi_pmf I d M)) f"
    by (subst a, subst map_pmf_rep_eq[symmetric], simp)
  also have "... =  integral\<^sup>L (M i) f"
    using assms(1,2) by (simp add: Pi_pmf_component)
  finally show "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. f (x i)) = integral\<^sup>L (M i) f" by simp
qed

text \<open>This is an improved version of @{thm [source] "expectation_prod_Pi_pmf"}.
It works for general normed fields instead of non-negative real functions .\<close>

lemma expectation_prod_Pi_pmf: 
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> ('c :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable (measure_pmf (M i)) (f i)"
  shows   "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i))) = (\<Prod> i \<in> I. integral\<^sup>L (M i) (f i))"
proof -
  have a: "prob_space.indep_vars (measure_pmf (Pi_pmf I d M)) (\<lambda>_. borel) (\<lambda>i \<omega>. f i (\<omega> i)) I"
    by (intro prob_space.indep_vars_compose2[where Y="f" and M'="\<lambda>_. discrete"] 
        prob_space_measure_pmf indep_vars_Pi_pmf assms(1)) auto
  have "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i))) = (\<Prod> i \<in> I. integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. f i (x i)))"
    by (intro prob_space.indep_vars_lebesgue_integral prob_space_measure_pmf assms(1,2) 
        a integrable_Pi_pmf_slice) auto
  also have "... = (\<Prod> i \<in> I. integral\<^sup>L (M i) (f i))"
    by (intro prod.cong expectation_Pi_pmf_slice assms(1,2)) auto
  finally show ?thesis by simp
qed

lemma variance_prod_pmf_slice:
  fixes f :: "'a \<Rightarrow> real"
  assumes "i \<in> I" "finite I"
  assumes "integrable (measure_pmf (M i)) (\<lambda>\<omega>. f \<omega>^2)"
  shows "prob_space.variance (Pi_pmf I d M) (\<lambda>\<omega>. f (\<omega> i)) = prob_space.variance (M i) f"
proof -
  have a:"integrable (measure_pmf (M i)) f"
    using assms(3) measure_pmf.square_integrable_imp_integrable by auto
  have b:" integrable (measure_pmf (Pi_pmf I d M)) (\<lambda>x. (f (x i))\<^sup>2)"
    by (rule integrable_Pi_pmf_slice[OF assms(2) assms(1)], metis assms(3))
  have c:" integrable (measure_pmf (Pi_pmf I d M)) (\<lambda>x. (f (x i)))"
    by (rule integrable_Pi_pmf_slice[OF assms(2) assms(1)], metis a)

  have "measure_pmf.expectation (Pi_pmf I d M) (\<lambda>x. (f (x i))\<^sup>2) - (measure_pmf.expectation (Pi_pmf I d M) (\<lambda>x. f (x i)))\<^sup>2 =
      measure_pmf.expectation (M i) (\<lambda>x. (f x)\<^sup>2) - (measure_pmf.expectation (M i) f)\<^sup>2"
    using assms a b c by ((subst expectation_Pi_pmf_slice[OF assms(2,1)])?, simp)+

  thus ?thesis
    using assms a b c by (simp add: measure_pmf.variance_eq)
qed

lemma Pi_pmf_bind_return:
  assumes "finite I"
  shows "Pi_pmf I d (\<lambda>i. M i \<bind> (\<lambda>x. return_pmf (f i x))) = Pi_pmf I d' M \<bind> (\<lambda>x. return_pmf (\<lambda>i. if i \<in> I then f i (x i) else d))"
  using assms by (simp add: Pi_pmf_bind[where d'="d'"])

end
