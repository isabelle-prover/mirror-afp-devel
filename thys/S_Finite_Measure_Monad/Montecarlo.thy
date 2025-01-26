(*  Title:   Montecarlo.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section \<open> Examples\<close>
subsection \<open>Montecarlo Approximation\<close>

theory Montecarlo
  imports "Monad_QuasiBorel"
begin

declare [[coercion qbs_l]]

abbreviation real_quasi_borel :: "real quasi_borel" ("\<real>\<^sub>Q") where
"real_quasi_borel \<equiv> qbs_borel"
abbreviation nat_quasi_borel :: "nat quasi_borel" ("\<nat>\<^sub>Q") where
"nat_quasi_borel \<equiv> qbs_count_space UNIV"


primrec montecarlo :: "'a qbs_measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real qbs_measure" where
"montecarlo _ _ 0       = return_qbs \<real>\<^sub>Q 0" |
"montecarlo d h (Suc n) = do { m \<leftarrow> montecarlo d h n;
                               x \<leftarrow> d;
                               return_qbs \<real>\<^sub>Q ((h x + m * real n) / real (Suc n))}"

declare
  bind_qbs_morphismP[qbs]
  return_qbs_morphismP[qbs]
  qbs_pair_measure_morphismP[qbs]
  qbs_space_monadPM[qbs]

lemma montecarlo_qbs_morphism[qbs]: "montecarlo \<in> qbs_space (monadP_qbs X \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Rightarrow>\<^sub>Q \<nat>\<^sub>Q \<Rightarrow>\<^sub>Q monadP_qbs \<real>\<^sub>Q)"
  by(simp add: montecarlo_def)

lemma qbs_integrable_indep_mult2:
  fixes f :: "_ \<Rightarrow> real"
  assumes "p \<in> qbs_space (monadM_qbs X)" "q \<in> qbs_space (monadM_qbs Y)"
    and "qbs_integrable p f"
    and "qbs_integrable q g"
  shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>x. g (snd x) * f (fst x))"
  using qbs_integrable_indep_mult[OF assms] by (simp add: mult.commute)

lemma montecarlo_integrable:
  assumes [qbs]:"p \<in> qbs_space (monadP_qbs X)" "h \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q" "qbs_integrable p h" "qbs_integrable p (\<lambda>x. h x * h x)"
  shows "qbs_integrable (montecarlo p h n) (\<lambda>x. x)" "qbs_integrable (montecarlo p h n) (\<lambda>x. x * x)"
proof -
  note qbs_space_monadPM[qbs]
  have "qbs_integrable (montecarlo p h n) (\<lambda>x. x) \<and> qbs_integrable (montecarlo p h n) (\<lambda>x. x * x)"
  proof(induction n)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    hence ih[intro,simp]:"qbs_integrable (montecarlo p h n) (\<lambda>x. x)" "qbs_integrable (montecarlo p h n) (\<lambda>x. x * x)"
      by simp_all
    have "qbs_integrable (montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p) (\<lambda>x. (h (snd x) + fst x * real n) * (h (snd x) + fst x * real n))"
    proof(subst qbs_integrable_cong[OF qbs_space_monadPM[where X="\<real>\<^sub>Q \<Otimes>\<^sub>Q X"]])
      show "qbs_integrable (montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p) (\<lambda>x. h (snd x) * h (snd x) + fst x * h (snd x) * 2 * real n + fst x * fst x * real n * real n)"
        by(auto intro!: qbs_integrable_indep_mult[OF qbs_space_monadPM[of _ "\<real>\<^sub>Q"] qbs_space_monadPM[of _ X]] qbs_integrable_indep2[OF _ qbs_space_monadPM,of _ "\<real>\<^sub>Q" _ X] assms qbs_integrable_mult_left qbs_integrable_indep1[OF qbs_space_monadPM,of _ "\<real>\<^sub>Q" _ X])
    qed (auto simp: distrib_right distrib_left)
    thus ?case
      by(auto simp: qbs_bind_bind_return2P'[of _ "\<real>\<^sub>Q" X "\<real>\<^sub>Q"] qbs_pair_measure_def[OF qbs_space_monadPM qbs_space_monadPM,symmetric] split_beta' qbs_integrable_bind_return[OF qbs_space_monadPM,of _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q X" _ "\<real>\<^sub>Q"] comp_def
            intro!: qbs_integrable_indep2[OF _ qbs_space_monadPM,of _ "\<real>\<^sub>Q" _ X] assms qbs_integrable_mult_left qbs_integrable_indep1[OF qbs_space_monadPM,of _ "\<real>\<^sub>Q" _ X])
  qed
  thus "qbs_integrable (montecarlo p h n) (\<lambda>x. x)" "qbs_integrable (montecarlo p h n) (\<lambda>x. x * x)"
    by simp_all
qed

lemma
  fixes n :: nat
  assumes [qbs,simp]:"p \<in> qbs_space (monadP_qbs X)" "h \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q" "qbs_integrable p h" "qbs_integrable p (\<lambda>x. h x * h x)"
      and e:"e > 0"
      and "(\<integral>\<^sub>Q x. h x \<partial>p) = \<mu>" "(\<integral>\<^sub>Q x. (h x - \<mu>)\<^sup>2 \<partial>p) = \<sigma>\<^sup>2"
      and n:"n > 0" 
    shows "\<P>(y in montecarlo p h n. \<bar>y - \<mu>\<bar> \<ge> e) \<le> \<sigma>\<^sup>2 / (real n * e\<^sup>2)" (is "?P \<le> _")
proof -
  have monte_p: "\<And>n. montecarlo p h n \<in> monadP_qbs \<real>\<^sub>Q"
    by simp
  note [intro!, simp] =
       montecarlo_integrable[OF assms(1-4)] qbs_integrable_indep1[where X="\<real>\<^sub>Q" and Y=X]
       qbs_integrable_indep2[where X="\<real>\<^sub>Q" and Y=X] qbs_integrable_sq qbs_integrable_mult_left qbs_integrable_mult_right
       qbs_integrable_const[OF assms(1)] qbs_integrable_const[OF monte_p]
       qbs_integrable_indep_mult2[where X="\<real>\<^sub>Q" and Y=X,OF qbs_space_monadPM qbs_space_monadPM]
  have [intro!, simp]:"qbs_integrable p (\<lambda>x. (h x)\<^sup>2)" "\<And>n. qbs_integrable (montecarlo p h n) power2"
    by(simp_all add: power2_eq_square)
  have exp:"(\<integral>\<^sub>Q y. y \<partial>(montecarlo p h n)) = \<mu>" (is "?e n") and var:"(\<integral>\<^sub>Q y. (y - \<mu>)\<^sup>2 \<partial>(montecarlo p h n)) = \<sigma>\<^sup>2 / n" (is "?v n")
  proof -
    have "?e n \<and> ?v n"
    proof(rule nat_induct_non_zero[OF n])
      fix n :: nat
      assume n[arith]:"0 < n"
      assume "?e n \<and> ?v n"
      hence ih: "?e n" "?v n"
        by simp_all
      have "?e (Suc n)"
      proof -
        have "(\<integral>\<^sub>Q y. y \<partial>montecarlo p h (Suc n)) = (\<integral>\<^sub>Q x. h (snd x) + fst x * real n \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) / (1 + real n)"
          by(auto simp:  qbs_bind_bind_return2P'[of _ "\<real>\<^sub>Q" X "\<real>\<^sub>Q"] split_beta' qbs_pair_measure_def[OF qbs_space_monadPM qbs_space_monadPM,symmetric] qbs_integral_bind_return[OF qbs_space_monadPM,of _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q X" _ "\<real>\<^sub>Q"] comp_def)
        also have "... = ((\<integral>\<^sub>Q x. h (snd x) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) + (\<integral>\<^sub>Q x. fst x * real n \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))) / (1 + real n)"
          by(auto intro!: qbs_integral_add simp del: qbs_integral_mult_left_zero)
        also have "... = (\<mu> + (\<integral>\<^sub>Q x. fst x\<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) * real n) / (1 + real n)"
          by(subst qbs_integral_indep2[where X="\<real>\<^sub>Q" and Y=X,OF _ qbs_space_monadPM]) (auto simp: assms(6))
        also have "... = (\<mu> * (1 + real n)) / (1 + real n)"
          by(subst  qbs_integral_indep1[where X="\<real>\<^sub>Q" and Y=X,OF qbs_space_monadPM]) (auto simp: ih distrib_left)
        also have "... = \<mu>"
          by simp
        finally show "?e (Suc n)" .
      qed
      moreover have "?v (Suc n)"
      proof -
        have "(\<integral>\<^sub>Q y. (y - \<mu>)\<^sup>2 \<partial>montecarlo p h (Suc n)) =(\<integral>\<^sub>Q x. ((h (snd x) + fst x * real n) / real (Suc n) - \<mu>)\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by(auto simp: qbs_bind_bind_return2P'[of _ "\<real>\<^sub>Q" X "\<real>\<^sub>Q"] split_beta' qbs_pair_measure_def[OF qbs_space_monadPM qbs_space_monadPM,symmetric] qbs_integral_bind_return[OF qbs_space_monadPM,of _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q X" _ "\<real>\<^sub>Q"] comp_def)
        also have "... = (\<integral>\<^sub>Q x. ((h (snd x) + fst x * real n) / real (Suc n) - (Suc n) * \<mu> / Suc n)\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by simp
        also have "... = (\<integral>\<^sub>Q x. ((h (snd x) + fst x * real n - (Suc n) * \<mu>) / Suc n)\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by(simp only: diff_divide_distrib[symmetric])
        also have "... = (\<integral>\<^sub>Q x. ((h (snd x) - \<mu> + (fst x * real n - real n * \<mu>)) / Suc n)\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by (simp add: add_diff_add distrib_left mult.commute)
        also have "... = (\<integral>\<^sub>Q x. (1 / real (Suc n) * (h (snd x) - \<mu>) + n / real (Suc n) * (fst x  - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by(auto simp: add_divide_distrib[symmetric] pair_qbs_space mult.commute[of _ "real n"]) (simp add: right_diff_distrib)
        also have "... = (\<integral>\<^sub>Q x. (1 / real (Suc n) * (h (snd x) - \<mu>))\<^sup>2 + (n / real (Suc n) * (fst x  - \<mu>))\<^sup>2 + 2 * (1 / real (Suc n) * (h (snd x) - \<mu>)) * (n / real (Suc n) * (fst x  - \<mu>)) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by(simp add: power2_sum)
        also have "... = (\<integral>\<^sub>Q x. 1 / (real (Suc n))\<^sup>2 * ((h (snd x) - \<mu>))\<^sup>2 + (n / real (Suc n))\<^sup>2 * ((fst x  - \<mu>))\<^sup>2 + 2 * (1 / real (Suc n) * (h (snd x) - \<mu>)) * (n / real (Suc n) * (fst x  - \<mu>)) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by(simp only: power_mult_distrib) (simp add: power2_eq_square)
        also have "... = (\<integral>\<^sub>Q x. 1 / (real (Suc n))\<^sup>2 * ((h (snd x) - \<mu>))\<^sup>2 + (n / real (Suc n))\<^sup>2 * ((fst x  - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) + (\<integral>\<^sub>Q x. 2 * (1 / real (Suc n) * (h (snd x) - \<mu>)) * (n / real (Suc n) * (fst x  - \<mu>)) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by(rule qbs_integral_add) auto
        also have "... = (\<integral>\<^sub>Q x. 1 / (real (Suc n))\<^sup>2 * ((h (snd x) - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) + (\<integral>\<^sub>Q x. (n / real (Suc n))\<^sup>2 * ((fst x  - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) + (\<integral>\<^sub>Q x. 2 * (1 / real (Suc n) * (h (snd x) - \<mu>)) * (n / real (Suc n) * (fst x  - \<mu>)) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          by(subst qbs_integral_add) auto
        also have "... = 1 / (real (Suc n))\<^sup>2 * \<sigma>\<^sup>2 + (n / real (Suc n))\<^sup>2 * (\<sigma>\<^sup>2 / n)"
        proof -
          have 1: "(\<integral>\<^sub>Q x. ((h (snd x) - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = (\<integral>\<^sub>Q x. (h x - \<mu>)\<^sup>2 \<partial>p)"
            by(subst qbs_integral_indep2[of _ "\<real>\<^sub>Q" _ X]) auto
          have 2: "(\<integral>\<^sub>Q x. ((fst x  - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = (\<integral>\<^sub>Q y. (y - \<mu>)\<^sup>2 \<partial>montecarlo p h n)"
            by(subst qbs_integral_indep1[of _ "\<real>\<^sub>Q" _ X]) auto
          have 3: "(\<integral>\<^sub>Q x. 2 * (1 / real (Suc n) * (h (snd x) - \<mu>)) * (n / real (Suc n) * (fst x  - \<mu>)) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = 0" (is "?l = _")
            by(subst qbs_integral_indep_mult2[of _ "\<real>\<^sub>Q" _ X])
              (auto simp: qbs_integral_diff[OF montecarlo_integrable(1)[OF assms(1-4)] qbs_integrable_const[of _ "\<real>\<^sub>Q"]] qbs_integral_const_prob[of _ "\<real>\<^sub>Q"] ih)
          show ?thesis
            unfolding 3 by(simp add: 1 2 ih assms(7))
        qed
        also have "... = 1 / (real (Suc n))\<^sup>2 * \<sigma>\<^sup>2 + real n / (real (Suc n))\<^sup>2 * \<sigma>\<^sup>2"
          by(auto simp: power2_eq_square)
        also have "... = (1 + real n) * \<sigma>\<^sup>2 / (real (Suc n))\<^sup>2"
          by (simp add: add_divide_distrib ring_class.ring_distribs(2))
        also have "... = \<sigma>\<^sup>2 / real (Suc n)"
          by(auto simp: power2_eq_square)
        finally show ?thesis .
      qed
      ultimately show "?e (Suc n) \<and> ?v (Suc n)"
        by blast
    qed(simp add: assms(6,7) qbs_integral_bind_return[where Y=X,OF qbs_space_monadPM]  bind_qbs_return[where Y="\<real>\<^sub>Q"] comp_def)
    thus "?e n" "?v n" by simp_all
  qed
  have "?P \<le> (\<integral>\<^sub>Q x. (x - \<mu>)\<^sup>2 \<partial>montecarlo p h n) / e\<^sup>2"
    unfolding exp[symmetric] by(rule Chebyshev_inequality_qbs_prob[of "montecarlo p h n" qbs_borel "\<lambda>x. x"]) (auto simp: power2_eq_square e)
  also have "... = \<sigma>\<^sup>2 / (real n * e\<^sup>2)"
    by(simp add: var)
  finally show ?thesis .
qed

end