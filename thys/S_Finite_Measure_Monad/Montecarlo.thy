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
"montecarlo _ _ 0           = return_qbs \<real>\<^sub>Q 0" |
"montecarlo d h (Suc n) = do { m \<leftarrow> montecarlo d h n;
                               x \<leftarrow> d;
                               return_qbs \<real>\<^sub>Q ((h x + m * (real n)) / (real (Suc n)))}"

declare
  bind_qbs_morphismP[qbs]
  return_qbs_morphismP[qbs]
  qbs_pair_measure_morphismP[qbs]

lemma montecarlo_qbs_morphism[qbs]: "montecarlo \<in> qbs_space (monadP_qbs X \<Rightarrow>\<^sub>Q (X \<Rightarrow>\<^sub>Q \<real>\<^sub>Q) \<Rightarrow>\<^sub>Q \<nat>\<^sub>Q \<Rightarrow>\<^sub>Q monadP_qbs \<real>\<^sub>Q)"
  by(simp add: montecarlo_def)

(* integrability *)
lemma qbs_integrable_indep_mult2[simp, intro!]:
  fixes f :: "_ \<Rightarrow> real"
  assumes "qbs_integrable p f"
      and "qbs_integrable q g"
    shows "qbs_integrable (p \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s q) (\<lambda>x. g (snd x) * f (fst x))"
  using qbs_integrable_indep_mult[OF assms] by (simp add: mult.commute)


lemma montecarlo_integrable:
  assumes [qbs]:"p \<in> qbs_space (monadP_qbs X)" "h \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q" "qbs_integrable p h" "qbs_integrable p (\<lambda>x. h x * h x)"
  shows "qbs_integrable (montecarlo p h n) (\<lambda>x. x)" "qbs_integrable (montecarlo p h n) (\<lambda>x. x * x)"
proof -
  have "qbs_integrable (montecarlo p h n) (\<lambda>x. x) \<and> qbs_integrable (montecarlo p h n) (\<lambda>x. x * x)"
  proof(induction n)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    hence 1[intro,simp]:"qbs_integrable (montecarlo p h n) (\<lambda>x. x)" "qbs_integrable (montecarlo p h n) (\<lambda>x. x * x)"
      by simp_all
    have 2[intro,simp]: "\<And>q f. qbs_integrable q (\<lambda>x. f x * f x) \<Longrightarrow> qbs_integrable q (\<lambda>x. f x * a * (f x * b))" for a b :: real
      by(auto simp: mult.commute[of _ a] mult.assoc intro!: qbs_integrable_scaleR_left[where 'a=real,simplified] qbs_integrable_scaleR_right[where 'a=real,simplified]) (auto simp: mult.assoc[of _ _ b,symmetric] intro!: qbs_integrable_scaleR_left[where 'a=real,simplified])
    show ?case
      by(auto simp add: qbs_bind_bind_return2P'[of _ "\<real>\<^sub>Q" X "\<real>\<^sub>Q"] split_beta' qbs_pair_measure_def[OF qbs_space_monadPM qbs_space_monadPM,symmetric] qbs_integrable_bind_return[OF qbs_space_monadPM,of _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q X" _ "\<real>\<^sub>Q"] comp_def distrib_right distrib_left intro!: qbs_integrable_indep_mult  qbs_integrable_indep1[OF 1(1),of _ X] qbs_integrable_indep2[OF assms(3),of _ "\<real>\<^sub>Q"] qbs_integrable_indep1[OF 1(2),of _ X] qbs_integrable_indep2[OF assms(4),of _ "\<real>\<^sub>Q"] qbs_integrable_const[OF assms(1)] qbs_integrable_scaleR_left[where 'a=real,simplified] assms(3,4))
  qed
  thus "qbs_integrable (montecarlo p h n) (\<lambda>x. x)" "qbs_integrable (montecarlo p h n) (\<lambda>x. x * x)"
    by simp_all
qed

lemma
  fixes n :: nat
  assumes [qbs]:"p \<in> qbs_space (monadP_qbs X)" "h \<in> X \<rightarrow>\<^sub>Q \<real>\<^sub>Q" "qbs_integrable p h" "qbs_integrable p (\<lambda>x. h x * h x)"
      and e:"e > 0"
      and "(\<integral>\<^sub>Q x. h x \<partial>p) = \<mu>" "(\<integral>\<^sub>Q x. (h x - \<mu>)\<^sup>2 \<partial>p) = \<sigma>\<^sup>2"
      and n:"n > 0" 
    shows "\<P>(y in montecarlo p h n. \<bar>y - \<mu>\<bar> \<ge> e) \<le> \<sigma>\<^sup>2 / (real n * e\<^sup>2)" (is "?P \<le> _")
proof -
  note [intro!] = montecarlo_integrable[OF assms(1-4)] qbs_integrable_indep_mult qbs_integrable_indep1[OF montecarlo_integrable(1)[OF assms(1-4)],of _ X] qbs_integrable_indep2[OF assms(3),of _ "\<real>\<^sub>Q"] qbs_integrable_indep1[OF montecarlo_integrable(2)[OF assms(1-4)],of _ X] qbs_integrable_indep2[OF assms(4),of _ "\<real>\<^sub>Q"] qbs_integrable_const[OF assms(1)] qbs_integrable_scaleR_right[where 'a=real,simplified] qbs_integrable_scaleR_left[where 'a=real,simplified] assms(3,4) qbs_integrable_sq qbs_integrable_const[of "montecarlo p h _ \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p" "\<real>\<^sub>Q \<Otimes>\<^sub>Q X"] qbs_integrable_const[of "montecarlo p h _" "\<real>\<^sub>Q"]
  have integrable[intro,simp]: "\<And>q f. qbs_integrable q (\<lambda>x. f x * f x) \<Longrightarrow> qbs_integrable q (\<lambda>x. f x * a * (f x * b))" for a b :: real
    by(auto simp: mult.commute[of _ a] mult.assoc) (auto simp: mult.assoc[of _ _ b,symmetric])
  have exp:"(\<integral>\<^sub>Q y. y \<partial>(montecarlo p h n)) = \<mu>" (is "?e n") and var:"(\<integral>\<^sub>Q y. (y - \<mu>)\<^sup>2 \<partial>(montecarlo p h n)) = \<sigma>\<^sup>2 / n" (is "?v n")
  proof -
    have "?e n \<and> ?v n"
      using n
    proof(induction n)
      case 0
      then show ?case
        by simp
    next
      case ih:(Suc n)
      consider "n = 0" | "n > 0" by auto
      then show ?case
      proof cases
        case 1
        then show ?thesis
          by(auto simp: qbs_integral_indep2[OF qbs_integrable_sq[OF qbs_integrable_const[OF assms(1)] assms(3)],simplified power2_eq_square,OF assms(4),of _ qbs_borel] power2_eq_square qbs_bind_bind_return2P'[of _ "\<real>\<^sub>Q" X "\<real>\<^sub>Q"] split_beta' qbs_pair_measure_def[OF qbs_space_monadPM qbs_space_monadPM,symmetric] qbs_integral_bind_return[OF qbs_space_monadPM,of _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q X" _ "\<real>\<^sub>Q"] comp_def qbs_integral_indep2[OF assms(3),of _ "\<real>\<^sub>Q"] qbs_integral_indep2[OF assms(4),of _ "\<real>\<^sub>Q"] assms(6,7)[simplified power2_eq_square])
      next
        case n[arith]:2
        with ih have eq: "(\<integral>\<^sub>Q y. y \<partial>montecarlo p h n) = \<mu> " "(\<integral>\<^sub>Q y. (y - \<mu>)\<^sup>2 \<partial>montecarlo p h n) = \<sigma>\<^sup>2 / real n"
          by simp_all

        have 1:"?e (Suc n)"
        proof -
          have "(\<integral>\<^sub>Q x. h (snd x) + fst x * real n \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = ((\<integral>\<^sub>Q x. h (snd x) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) + (\<integral>\<^sub>Q x. fst x * real n \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)))"
            by(rule qbs_integral_add) auto
          also have "... = \<mu> +  \<mu> * n"
          proof -
            have "(\<integral>\<^sub>Q x. h (snd x) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = (\<integral>\<^sub>Q x. h x \<partial>p)"
              by(auto intro!: qbs_integral_indep2[of _ _ _ "\<real>\<^sub>Q"])
            moreover have "(\<integral>\<^sub>Q x. fst x \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = (\<integral>\<^sub>Q y. y \<partial>montecarlo p h n)"
              by(auto intro!: qbs_integral_indep1[of _ _ _ X])
            ultimately show ?thesis
              by(simp add: eq assms)
          qed
          finally have "( \<integral>\<^sub>Q y. y \<partial>montecarlo p h (Suc n)) = 1 / (Suc n) * (\<mu> +  \<mu> * n)"
            by(auto simp: qbs_bind_bind_return2P'[of _ "\<real>\<^sub>Q" X "\<real>\<^sub>Q"] split_beta' qbs_pair_measure_def[OF qbs_space_monadPM qbs_space_monadPM,symmetric] qbs_integral_bind_return[OF qbs_space_monadPM,of _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q X" _ "\<real>\<^sub>Q"] comp_def)
          also have "... = 1 / (Suc n) * (\<mu> * (1 + real n))"
            by(simp add: distrib_left)
          also have "... = \<mu>"
            by simp
          finally show ?thesis .
        qed
        have 2: "?v (Suc n)"
        proof -
          have "(\<integral>\<^sub>Q y. (y - \<mu>)\<^sup>2 \<partial>montecarlo p h (Suc n)) = (\<integral>\<^sub>Q x. ((h (snd x) + fst x * real n) / real (Suc n) - \<mu>)\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
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
            by(rule qbs_integral_add, auto) (auto simp: power2_eq_square)
          also have "... = (\<integral>\<^sub>Q x. 1 / (real (Suc n))\<^sup>2 * ((h (snd x) - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) + (\<integral>\<^sub>Q x. (n / real (Suc n))\<^sup>2 * ((fst x  - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) + (\<integral>\<^sub>Q x. 2 * (1 / real (Suc n) * (h (snd x) - \<mu>)) * (n / real (Suc n) * (fst x  - \<mu>)) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
          proof -
            have "(\<integral>\<^sub>Q x. 1 / (real (Suc n))\<^sup>2 * ((h (snd x) - \<mu>))\<^sup>2 + (n / real (Suc n))\<^sup>2 * ((fst x  - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = (\<integral>\<^sub>Q x. 1 / (real (Suc n))\<^sup>2 * ((h (snd x) - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) + (\<integral>\<^sub>Q x. (n / real (Suc n))\<^sup>2 * ((fst x  - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p))"
              by(rule qbs_integral_add, auto) (auto simp: power2_eq_square)
            thus ?thesis by simp
          qed
          also have "... = 1 / (real (Suc n))\<^sup>2 * \<sigma>\<^sup>2 + (n / real (Suc n))\<^sup>2 * (\<sigma>\<^sup>2 / n)"
          proof -
            have 1: "(\<integral>\<^sub>Q x. ((h (snd x) - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = (\<integral>\<^sub>Q x. (h x - \<mu>)\<^sup>2 \<partial>p)"
              by(auto intro!: qbs_integral_indep2[of _ _ _ "\<real>\<^sub>Q"]) (auto simp: power2_eq_square)
            have 2: "(\<integral>\<^sub>Q x. ((fst x  - \<mu>))\<^sup>2 \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = (\<integral>\<^sub>Q y. (y - \<mu>)\<^sup>2 \<partial>montecarlo p h n)"
              by(auto intro!: qbs_integral_indep1[of _ _ _ X]) (auto simp: power2_eq_square)
            have 3: "(\<integral>\<^sub>Q x. 2 * (1 / real (Suc n) * (h (snd x) - \<mu>)) * (n / real (Suc n) * (fst x  - \<mu>)) \<partial>(montecarlo p h n \<Otimes>\<^sub>Q\<^sub>m\<^sub>e\<^sub>s p)) = 0" (is "?l = _")
            proof -
              have "?l = (\<integral>\<^sub>Q x. 2 * (1 / real (Suc n) * (h x - \<mu>)) \<partial>p) * (\<integral>\<^sub>Q x. (n / real (Suc n) * (x  - \<mu>)) \<partial>montecarlo p h n)"
                by(rule qbs_integral_indep_mult2[of _ "\<real>\<^sub>Q" _ X]) auto
              also have "... = 0"
                by(simp add: qbs_integral_diff[OF montecarlo_integrable(1)[OF assms(1-4)] qbs_integrable_const[of _ "\<real>\<^sub>Q"]] eq qbs_integral_const_prob[of _ "\<real>\<^sub>Q"])
              finally show ?thesis .
            qed
            show ?thesis
              unfolding 3 by(simp add: 1 2 eq assms)
          qed
          also have "... = 1 / (real (Suc n))\<^sup>2 * \<sigma>\<^sup>2 + real n / (real (Suc n))\<^sup>2 * \<sigma>\<^sup>2"
            by(auto simp: power2_eq_square)
          also have "... = (1 + real n) * \<sigma>\<^sup>2 / (real (Suc n))\<^sup>2"
            by (simp add: add_divide_distrib ring_class.ring_distribs(2))
          also have "... = \<sigma>\<^sup>2 / real (Suc n)"
            by(auto simp: power2_eq_square)
          finally show ?thesis .
        qed
        show ?thesis
          by(simp only: 1 2)
      qed
    qed
    thus "?e n" "?v n" by simp_all
  qed


  have "?P \<le> (\<integral>\<^sub>Q x. (x - \<mu>)\<^sup>2 \<partial>montecarlo p h n) / e\<^sup>2"
    unfolding exp[symmetric] by(rule Chebyshev_inequality_qbs_prob[of "montecarlo p h n" qbs_borel "\<lambda>x. x"]) (auto simp: power2_eq_square e)
  also have "... = \<sigma>\<^sup>2 / (real n * e\<^sup>2)"
    by(simp add: var)
  finally show ?thesis .
qed

end