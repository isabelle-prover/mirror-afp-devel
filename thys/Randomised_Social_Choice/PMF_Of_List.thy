(*  
  Title:    PMF_OF_List.thy
  Author:   Manuel Eberl, TU München

  Creating PMFs from lists
*)

section \<open>Creating PMFs from lists\<close>

theory PMF_Of_List
imports Complex_Main "~~/src/HOL/Probability/Probability"
begin

(* TODO Move *)
lemma listsum_nonneg: "(\<And>x. x \<in> set xs \<Longrightarrow> (x :: 'a :: linordered_idom) \<ge> 0) \<Longrightarrow> listsum xs \<ge> 0"
  by (induction xs) simp_all

lemma listsum_map_filter:
  "listsum (map f (filter P xs)) = listsum (map (\<lambda>x. if P x then f x else 0) xs)"
  by (induction xs) simp_all

lemma listsum_cong:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x = g x"
  shows    "listsum (map f xs) = listsum (map g xs)"
  using assms by (induction xs) simp_all

lemma ereal_listsum: "listsum (map (\<lambda>x. ereal (f x)) xs) = ereal (listsum (map f xs))"
  by (induction xs) simp_all
(* END TODO *)


definition pmf_of_list ::" ('a \<times> real) list \<Rightarrow> 'a pmf" where 
  "pmf_of_list xs = embed_pmf (\<lambda>x. listsum (map snd (filter (\<lambda>z. fst z = x) xs)))"

definition pmf_of_list_wf where
  "pmf_of_list_wf xs \<longleftrightarrow> (\<forall>x\<in>set (map snd xs) . x \<ge> 0) \<and> listsum (map snd xs) = 1"

lemma pmf_of_list_wfI:
  "(\<And>x. x \<in> set (map snd xs) \<Longrightarrow> x \<ge> 0) \<Longrightarrow> listsum (map snd xs) = 1 \<Longrightarrow> pmf_of_list_wf xs"
  unfolding pmf_of_list_wf_def by simp

lemma pmf_of_list_aux:
  assumes "\<And>x. x \<in> set (map snd xs) \<Longrightarrow> x \<ge> 0"
  assumes "listsum (map snd xs) = 1"
  shows "(\<integral>\<^sup>+ x. ereal (listsum (map snd [z\<leftarrow>xs . fst z = x])) \<partial>count_space UNIV) = 1"
proof -
  have "(\<integral>\<^sup>+ x. ereal (listsum (map snd (filter (\<lambda>z. fst z = x) xs))) \<partial>count_space UNIV) =
            (\<integral>\<^sup>+ x. ereal (listsum (map (\<lambda>(x',p). indicator {x'} x * p) xs)) \<partial>count_space UNIV)"
    by (intro nn_integral_cong, subst listsum_map_filter) (auto intro: listsum_cong)
  also have "\<dots> = (\<Sum>(x',p)\<leftarrow>xs. (\<integral>\<^sup>+ x. ereal (indicator {x'} x * p) \<partial>count_space UNIV))"
    using assms(1)
  proof (induction xs)
    case (Cons x xs)
    have "(\<integral>\<^sup>+ y. ereal (\<Sum>(x', p)\<leftarrow>x # xs. indicator {x'} y * p) \<partial>count_space UNIV) = 
            (\<integral>\<^sup>+ y. ereal (indicator {fst x} y * snd x) + 
            ereal (\<Sum>(x', p)\<leftarrow>xs. indicator {x'} y * p) \<partial>count_space UNIV)"
      by (simp add: plus_ereal.simps [symmetric] case_prod_unfold del: plus_ereal.simps)
    also have "\<dots> = (\<integral>\<^sup>+ y. ereal (indicator {fst x} y * snd x) \<partial>count_space UNIV) + 
                      (\<integral>\<^sup>+ y. ereal (\<Sum>(x', p)\<leftarrow>xs. indicator {x'} y * p) \<partial>count_space UNIV)"
      by (intro nn_integral_add)
         (force intro!: listsum_nonneg AE_I2 intro: Cons simp: indicator_def)+
    also have "(\<integral>\<^sup>+ y. ereal (\<Sum>(x', p)\<leftarrow>xs. indicator {x'} y * p) \<partial>count_space UNIV) =
               (\<Sum>(x', p)\<leftarrow>xs. (\<integral>\<^sup>+ y. ereal (indicator {x'} y * p) \<partial>count_space UNIV))"
      using Cons(1) by (intro Cons) simp_all
    finally show ?case by (simp add: case_prod_unfold)
  qed simp
  also have "\<dots> = (\<Sum>(x',p)\<leftarrow>xs. ereal p * (\<integral>\<^sup>+ x. indicator {x'} x \<partial>count_space UNIV))"
    using assms(1)
    by (intro listsum_cong, simp only: case_prod_unfold, subst nn_integral_cmult [symmetric])
       (auto intro!: assms(1) simp: max_def times_ereal.simps [symmetric] mult_ac ereal_indicator
             simp del: times_ereal.simps)+
  also have "\<dots> = listsum (map snd xs)" by (simp add: case_prod_unfold ereal_listsum)
  also have "\<dots> = 1" using assms(2) by simp
  finally show ?thesis .
qed

lemma pmf_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "pmf (pmf_of_list xs) x = listsum (map snd (filter (\<lambda>z. fst z = x) xs))"
  using assms pmf_of_list_aux[of xs] unfolding pmf_of_list_def pmf_of_list_wf_def
  by (subst pmf_embed_pmf) (auto intro!: listsum_nonneg)+

lemma set_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "set_pmf (pmf_of_list xs) \<subseteq> set (map fst xs)"
proof clarify
  fix x assume A: "x \<in> set_pmf (pmf_of_list xs)"
  show "x \<in> set (map fst xs)"
  proof (rule ccontr)
    assume "x \<notin> set (map fst xs)"
    hence "[z\<leftarrow>xs . fst z = x] = []" by (auto simp: filter_empty_conv)
    with A assms show False by (simp add: pmf_pmf_of_list set_pmf_eq)
  qed
qed

lemma finite_set_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "finite (set_pmf (pmf_of_list xs))"
  using assms by (rule finite_subset[OF set_pmf_of_list]) simp_all

lemma emeasure_Int_set_pmf:
  "emeasure (measure_pmf p) (A \<inter> set_pmf p) = emeasure (measure_pmf p) A"
  by (rule emeasure_eq_AE) (auto simp: AE_measure_pmf_iff)

lemma measure_Int_set_pmf:
  "measure (measure_pmf p) (A \<inter> set_pmf p) = measure (measure_pmf p) A"
  using emeasure_Int_set_pmf[of p A] by (simp add: Sigma_Algebra.measure_def)

lemma measure_pmf_of_list:
  assumes "pmf_of_list_wf xs"
  shows   "measure (pmf_of_list xs) A = listsum (map snd (filter (\<lambda>x. fst x \<in> A) xs))"
proof -
  have "emeasure (pmf_of_list xs) A = nn_integral (measure_pmf (pmf_of_list xs)) (indicator A)"
    by simp
  also have "\<dots> = ereal (\<Sum>x\<in>set_pmf (pmf_of_list xs). indicator A x * pmf (pmf_of_list xs) x)"
    (is "_ = ereal ?S") using assms
    by (subst nn_integral_measure_pmf_finite) 
       (simp_all add: finite_set_pmf_of_list ereal_indicator [symmetric] pmf_pmf_of_list)
  also have "?S = (\<Sum>x\<in>set (map fst xs). indicator A x * pmf (pmf_of_list xs) x)"
    using assms by (intro setsum.mono_neutral_left set_pmf_of_list) (auto simp: set_pmf_eq)
  also have "\<dots> = (\<Sum>x\<in>set (map fst xs). indicator A x * 
                      listsum (map snd (filter (\<lambda>z. fst z = x) xs)))"
    using assms by (simp add: pmf_pmf_of_list)
  also have "\<dots> = (\<Sum>x\<in>set (map fst xs). listsum (map snd (filter (\<lambda>z. fst z = x \<and> x \<in> A) xs)))"
    by (intro setsum.cong) (auto simp: indicator_def)
  also have "\<dots> = (\<Sum>x\<in>set (map fst xs). (\<Sum>xa = 0..<length xs.
                     if fst (xs ! xa) = x \<and> x \<in> A then snd (xs ! xa) else 0))"
    by (intro setsum.cong refl, subst listsum_map_filter, subst listsum_setsum_nth) simp
  also have "\<dots> = (\<Sum>xa = 0..<length xs. (\<Sum>x\<in>set (map fst xs). 
                     if fst (xs ! xa) = x \<and> x \<in> A then snd (xs ! xa) else 0))"
    by (rule setsum.commute)
  also have "\<dots> = (\<Sum>xa = 0..<length xs. if fst (xs ! xa) \<in> A then 
                     (\<Sum>x\<in>set (map fst xs). if x = fst (xs ! xa) then snd (xs ! xa) else 0) else 0)"
    by (auto intro!: setsum.cong setsum.neutral)
  also have "\<dots> = (\<Sum>xa = 0..<length xs. if fst (xs ! xa) \<in> A then snd (xs ! xa) else 0)"
    by (intro setsum.cong refl) (simp_all add: setsum.delta)
  also have "\<dots> = listsum (map snd (filter (\<lambda>x. fst x \<in> A) xs))"
    by (subst listsum_map_filter, subst listsum_setsum_nth) simp_all
  finally show ?thesis by (simp add: Sigma_Algebra.measure_def)
qed

end