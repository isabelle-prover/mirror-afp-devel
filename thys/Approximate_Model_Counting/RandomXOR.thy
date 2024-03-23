section \<open>Random XORs\<close>

text \<open>The goal of this section is to prove that,
  for a randomly sampled XOR $X$ from a set of variables $V$:
  \begin{enumerate}
  \item the probability of an assignment $w$ satisfying $X$ is $\frac{1}{2}$;
  \item for any distinct assignments $w$, $w'$ the probability of both satisfying $X$ is equal to $\frac{1}{4}$ (2-wise independence); and
  \item for any distinct assignments $w$, $w'$, $w''$ the probability of all three
     satisfying $X$ is equal to $\frac{1}{8}$ (3-wise independence).
  \end{enumerate}
  \<close>

theory RandomXOR imports
  ApproxMCPreliminaries
  Frequency_Moments.Product_PMF_Ext
  Monad_Normalisation.Monad_Normalisation
begin


text \<open>A random XOR constraint is modeled
  as a random subset of variables and a randomly chosen RHS bit. \<close>
definition random_xor :: "'a set \<Rightarrow> ('a set \<times> bool) pmf"
  where "random_xor V =
    pair_pmf (pmf_of_set (Pow V)) (bernoulli_pmf (1/2))"

lemma pmf_of_set_Pow_fin_map:
  assumes V:"finite V"
  shows "pmf_of_set (Pow V) =
    map_pmf (\<lambda>b. {x \<in> V. b x = Some True})
     (Pi_pmf V def (\<lambda>_. map_pmf Some (bernoulli_pmf (1 / 2))))"
proof -
  have *: "Pi_pmf V def (\<lambda>_. map_pmf Some (bernoulli_pmf (1 / 2))) =
    map_pmf (\<lambda>f x. if x \<in> V then f x else def)
    (Pi_pmf V (Some False) (\<lambda>_. map_pmf Some (bernoulli_pmf (1 / 2))))"
    unfolding Pi_pmf_default_swap[OF V] by auto

  have **: "pmf_of_set (Pow V) =
    map_pmf
     (\<lambda>x. {xa. (xa \<in> V \<longrightarrow> x xa) \<and> xa \<in> V})
     (Pi_pmf V False  (\<lambda>_. bernoulli_pmf (1 / 2)))"
    by (smt (verit, ccfv_SIG) Collect_cong pmf_of_set_Pow_conv_bernoulli V pmf.map_cong)
  show ?thesis
    unfolding *
    apply (subst Pi_pmf_map[OF V, of _ "False"])
    using ** by (auto simp add: pmf.map_comp o_def)
qed

(* A random XOR can also be sampled as a
  map |V| \<Rightarrow> bool + a coin flip *)
lemma random_xor_from_bits:
  assumes V:"finite V"
  shows "random_xor V =
    pair_pmf
      (map_pmf (\<lambda>b. {x \<in> V. b x = Some True})
        (Pi_pmf V def (\<lambda>_. map_pmf Some (bernoulli_pmf (1/2)))))
      (bernoulli_pmf (1/2))"
  unfolding random_xor_def
  using V pmf_of_set_Pow_fin_map by fastforce

(* An assignment is a subset \<omega> of V
   i.e., those variables assigned to true *)
fun satisfies_xor :: "('a set \<times> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "satisfies_xor (x,b) \<omega> =
     even (card (\<omega> \<inter> x) + of_bool b) "

(*
(* x_0 \<oplus> x_1 \<oplus> x_2 = 0 *)
value "satisfies_xor ({0,1,2},False) {0::nat}"
(* x_0 \<oplus> x_1 \<oplus> x_2 = 1 *)
value "satisfies_xor ({0,1,2},True) {0::nat}"
*)

lemma satisfies_xor_inter:
  shows "satisfies_xor ( \<omega> \<inter> x ,b) \<omega> = satisfies_xor (x,b) \<omega>"
  by (auto simp add: Int_commute)

lemma prob_bernoulli_bind_pmf:
  assumes "0 \<le> p" "p \<le> 1"
  assumes "finite E"
  shows "measure_pmf.prob
   (bernoulli_pmf p \<bind> x) E =
  p * (measure_pmf.prob (x True) E) +
  (1 - p) * (measure_pmf.prob (x False) E) "
  using assms
  by (auto simp add: pmf_bind measure_measure_pmf_finite[OF assms(3)] vector_space_over_itself.scale_sum_right comm_monoid_add_class.sum.distrib mult.commute)

lemma set_pmf_random_xor:
  assumes V: "finite V"
  shows "set_pmf (random_xor V) = (Pow V) \<times> UNIV"
  unfolding random_xor_def
  using assms by (auto simp add: Pow_not_empty Set.basic_monos(7))

lemma pmf_of_set_prod:
  assumes "P \<noteq> {}" "Q \<noteq> {}"
  assumes "finite P" "finite Q"
  shows "pmf_of_set (P \<times> Q) = pair_pmf (pmf_of_set P) (pmf_of_set Q)"
  by (auto intro!: pmf_eqI simp add: indicator_def pmf_pair assms)

lemma random_xor_pmf_of_set:
  assumes V:"finite V"
  shows "random_xor V  = pmf_of_set ((Pow V) \<times> UNIV)"
  unfolding random_xor_def
  apply (subst pmf_of_set_prod)
  using V bernoulli_pmf_half_conv_pmf_of_set by auto

lemma prob_random_xor_with_set_pmf:
  assumes V: "finite V"
  shows "prob_space.prob (random_xor V) {c. P c} =
    prob_space.prob (random_xor V) {c. fst c \<subseteq> V \<and> P c}"
  by (smt (verit, best) PowD assms measure_pmf.measure_pmf_eq mem_Collect_eq mem_Sigma_iff prod.collapse set_pmf_random_xor)

lemma prob_set_parity:
  assumes "measure_pmf.prob M
    {c. P c} = q"
  shows "measure_pmf.prob M
    {c. P c = b} = (if b then q else 1 - q)"
proof -
  {
    assume b:"b"
    have ?thesis using assms
      using b by presburger
  }
  moreover {
    assume b:"\<not>b"
    have "{c. P c} \<in> measure_pmf.events M" by auto
    from measure_pmf.prob_compl[OF this]
    have "1 - q = measure_pmf.prob M (UNIV - {c. P c})"
      using assms by auto
    moreover have " ... =
      prob_space.prob M
      {c. P c = b}"
      by (simp add: b measure_pmf.measure_pmf_eq)
    ultimately have ?thesis
      using b by presburger
  }
  ultimately show ?thesis by auto
qed

lemma satisfies_random_xor:
  assumes V: "finite V"
  shows "prob_space.prob (random_xor V)
    {c. satisfies_xor c \<omega>} = 1 / 2"
proof -
  have eq: "{(c::'a set \<times> bool). fst c \<subseteq> V} = {c. c \<subseteq> V} \<times> UNIV"
    by auto
  then have "finite {(c::'a set \<times> bool). fst c \<subseteq> V}"
    using assms by auto

  then have *: "
    x \<subseteq> V \<Longrightarrow>
    measure_pmf.prob (bernoulli_pmf (1 / 2) \<bind> (\<lambda>y. return_pmf (x, y)))
        {c. fst c \<subseteq> V \<and> satisfies_xor c \<omega>} = 1 / 2" for x
    apply (subst prob_bernoulli_bind_pmf)
    by (auto simp add: indicator_def)

  have "prob_space.prob (random_xor V) {c. satisfies_xor c \<omega>} =
    prob_space.prob (random_xor V) {c. fst c \<subseteq> V \<and> satisfies_xor c \<omega>}"
    using prob_random_xor_with_set_pmf[OF V] by auto
  also have "... =
    prob_space.expectation (random_xor V)
    (indicat_real {c. fst c \<subseteq> V \<and> satisfies_xor c \<omega>})"
    by auto
  also have "... = (\<Sum>a\<in>Pow V.
       inverse (real (card (Pow V))) *
       measure_pmf.prob
        (bernoulli_pmf (1 / 2) \<bind>
         (\<lambda>y. return_pmf (a, y)))
        {c. fst c \<subseteq> V \<and> satisfies_xor c \<omega>})"
    unfolding random_xor_def pair_pmf_def
    apply (subst pmf_expectation_bind_pmf_of_set)
    using assms by auto
  also have "... = (\<Sum>a\<in>Pow V.
       inverse (real (card (Pow V))) * (1/2))"
    by (simp add: *)
  also have "... =
       inverse (real (card (Pow V))) * (1/2) * (\<Sum>a\<in>Pow V. 1)"
    using * by force
  also have "... = 1/2"
    by (metis One_nat_def Suc_leI assms card_Pow divide_real_def inverse_inverse_eq inverse_nonzero_iff_nonzero nat_one_le_power nonzero_mult_div_cancel_left not_one_le_zero of_nat_eq_0_iff pos2 real_of_card)
  finally show ?thesis
    by presburger
qed

lemma satisfies_random_xor_parity:
  assumes V: "finite V"
  shows "prob_space.prob (random_xor V)
    {c. satisfies_xor c \<omega> = b} = 1 / 2"
  using prob_set_parity[OF satisfies_random_xor[OF V]]
    by auto

subsection "Independence properties of random XORs"

lemma pmf_of_set_powerset_split:
  assumes "S \<subseteq> V" "finite V"
  shows "
    map_pmf (\<lambda>(x,y). x \<union> y)
    (pmf_of_set (Pow S \<times> Pow (V - S))) =
  pmf_of_set (Pow V)"
proof -
  have spmfS: "set_pmf (pmf_of_set (Pow S)) = Pow S"
    using assms
    by (auto intro!: set_pmf_of_set simp add: rev_finite_subset)
  have spmfVS: "set_pmf (pmf_of_set (Pow (V-S))) = Pow (V-S)"
    using assms by (auto intro!: set_pmf_of_set)

  have xsub: "x \<subseteq> V \<Longrightarrow>
         \<exists>xa\<in>Pow S.
            \<exists>y\<in>Pow (V - S). x = xa \<union> y" for x 
    by (metis Diff_subset_conv Pow_iff Un_Diff_Int basic_trans_rules(23) inf_le2 sup_commute)

  have inj: "inj_on (\<lambda>(x, y). x \<union> y)
     (Pow S \<times> Pow (V - S))"
    unfolding inj_on_def
    by auto
  then have bij: "bij_betw (\<lambda>(x, y). x \<union> y)
     ((Pow S) \<times> Pow (V - S))
     (Pow V)"
    unfolding bij_betw_def
    using assms(1) xsub by (auto simp add: image_def)

  have "map_pmf (\<lambda>(x, y). x \<union> y)
     (pmf_of_set (Pow S \<times> Pow (V - S))) =
    pmf_of_set (Pow V)"
    apply (subst map_pmf_of_set_inj[OF inj])
    subgoal by (auto simp add: image_def)
    subgoal using bij assms(2) bij_betw_finite by blast
    apply (intro arg_cong[where f = "pmf_of_set"])
    using assms(1) xsub by (auto  simp add: image_def)

  thus ?thesis
    unfolding spmfS spmfVS
    by auto
qed

lemma pmf_of_set_Pow_sing:
  shows"pmf_of_set (Pow {x}) =
     bernoulli_pmf (1 / 2) \<bind>
     (\<lambda>b. return_pmf (if b then {x} else {}))"
  apply (intro pmf_eqI)
  apply (subst pmf_of_set)
  by (auto simp add: pmf_bind card_Pow indicator_def subset_singleton_iff)

lemma pmf_of_set_sing_coin_flip:
  assumes "finite V"
  shows "pmf_of_set (Pow {x} \<times> Pow V) =
    map_pmf (\<lambda>(r,c). (if c then {x} else {}, r)) (random_xor V)"
proof -
  have *: "pmf_of_set (Pow {x} \<times> Pow V) =
    pair_pmf (pmf_of_set (Pow {x})) (pmf_of_set (Pow V))"
    apply(intro pmf_of_set_prod)
    using assms by auto
  show ?thesis
    unfolding *
    apply (intro pmf_eqI)
    including monad_normalisation
    by (auto simp add: map_pmf_def pair_pmf_def random_xor_def pmf_of_set_Pow_sing)
qed

(* TODO: there is a more general version below *)
lemma measure_pmf_prob_dependent_product_bound_eq:
  assumes "countable A" "\<And>i. countable (B i)"
  assumes "\<And>a. a \<in> A \<Longrightarrow> measure_pmf.prob N (B a) = r"
  shows "measure_pmf.prob (pair_pmf M N) (Sigma A B) =
    measure_pmf.prob M A * r"
proof -
  have "measure_pmf.prob (pair_pmf M N) (Sigma A B) =
    (\<Sum>\<^sub>a(a, b) \<in> Sigma A B. pmf M a * pmf N b)"
    by (auto intro!: infsetsum_cong simp add: measure_pmf_conv_infsetsum pmf_pair)
  also have "... = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B a. pmf M a * pmf N b)"
    apply (subst infsetsum_Sigma[OF assms(1-2)])
    subgoal by (metis (no_types, lifting) SigmaE abs_summable_on_cong case_prod_conv pmf_abs_summable pmf_pair)
    by (auto simp add: assms case_prod_unfold)

  also have "... = (\<Sum>\<^sub>aa\<in>A. pmf M a * (measure_pmf.prob N (B a)))"
    by (simp add: infsetsum_cmult_right measure_pmf_conv_infsetsum pmf_abs_summable)
  also have "... = (\<Sum>\<^sub>aa\<in>A. pmf M a * r)"
    using assms(3) by force
  also have"... = measure_pmf.prob M A * r"
    by (simp add: infsetsum_cmult_left pmf_abs_summable measure_pmf_conv_infsetsum)
  finally show ?thesis
    by linarith
qed

(* TODO: duplicated in Schwartz_Zippel, but
  we don't want to pull in the multivariate polynomials library *)
lemma measure_pmf_prob_dependent_product_bound_eq':
  assumes "countable (A \<inter> set_pmf M)" "\<And>i. countable (B i \<inter> set_pmf N)"
  assumes "\<And>a. a \<in> A \<inter> set_pmf M \<Longrightarrow> measure_pmf.prob N (B a \<inter> set_pmf N) = r"
  shows "measure_pmf.prob (pair_pmf M N) (Sigma A B) = measure_pmf.prob M A * r"
proof -
  have *: "Sigma A B \<inter> (set_pmf M \<times> set_pmf N) =
    Sigma (A \<inter> set_pmf M) (\<lambda>i. B i \<inter> set_pmf N)"
    by auto

  have "measure_pmf.prob (pair_pmf M N) (Sigma A B) =
    measure_pmf.prob (pair_pmf M N) (Sigma (A \<inter> set_pmf M) (\<lambda>i. B i \<inter> set_pmf N))"
    by (metis * measure_Int_set_pmf set_pair_pmf)
  moreover have "... =
    measure_pmf.prob M (A \<inter> set_pmf M) * r"
    using measure_pmf_prob_dependent_product_bound_eq[OF assms(1-3)]
    by auto
  moreover have "... = measure_pmf.prob M A * r"
    by (simp add: measure_Int_set_pmf)
  ultimately show ?thesis by linarith
qed

lemma single_var_parity_coin_flip:
  assumes "x \<in> \<omega>" "finite \<omega>"
  assumes "finite a" "x \<notin> a"
  shows "measure_pmf.prob (pmf_of_set (Pow {x}))
          {y. even (card ((a \<union> y) \<inter> \<omega>)) = b}  = 1/2"
proof -
  have "insert x a \<inter> \<omega> = insert x (a \<inter> \<omega>)"
    using assms by auto
  then have *: "card (insert x a \<inter> \<omega>) = 1 + card (a \<inter> \<omega>)"
    by (simp add: assms(2) assms(4))

  have "measure_pmf.prob (pmf_of_set (Pow {x}))
          {y. even (card ((a \<union> y) \<inter> \<omega>)) = b} =
    measure_pmf.prob (bernoulli_pmf (1/2))
          {odd (card (a \<inter> \<omega>)) = b}"
    unfolding pmf_of_set_Pow_sing map_pmf_def[symmetric]
    by (auto intro!: measure_prob_cong_0 simp add:image_def * )
  moreover have "... = 1/2"
    by (simp add: measure_pmf_single)
  ultimately show ?thesis by auto
qed

(*
  Fix any event E that does not touch x
  Then we can sample that event separately
*)
lemma prob_pmf_of_set_nonempty_parity:
  assumes V: "finite V"
  assumes "x \<in> \<omega>" "\<omega> \<subseteq> V"
  assumes "\<And>c. c \<in> E \<longleftrightarrow> c - {x} \<in> E"
  shows "prob_space.prob (pmf_of_set (Pow V))
    (E \<inter> {c. even (card (c \<inter> \<omega>)) = b}) =
    1 / 2 * prob_space.prob (pmf_of_set (Pow (V - {x}))) E"
proof -
  have 1: "set_pmf (pmf_of_set (Pow {x})) = Pow {x}"
    by (simp add: Pow_not_empty)
  have 2: "set_pmf (pmf_of_set (Pow (V-{x}))) = Pow (V-{x})"
    by (simp add: Pow_not_empty assms(1))
  have 3: "set_pmf (pmf_of_set (Pow {x} \<times> Pow (V - {x}))) = Pow {x} \<times> Pow (V - {x})"
    by (simp add: Pow_not_empty assms(1))

  have "{x} \<subseteq> V" using assms by auto
  from pmf_of_set_powerset_split[OF this assms(1)]
  have e: "map_pmf (\<lambda>(x, y). x \<union> y)
     (pmf_of_set (Pow {x} \<times> Pow (V - {x}))) =
    pmf_of_set (Pow V)" using 1 2 by auto
  have "map_pmf (\<lambda>(x, y). x \<union> y)
     (pair_pmf (pmf_of_set (Pow {x}))
       (pmf_of_set (Pow (V - {x})))) =
    map_pmf (\<lambda>(x, y). x \<union> y)
     (pair_pmf (pmf_of_set (Pow (V - {x})))
       (pmf_of_set (Pow {x})))"
    apply (subst pair_commute_pmf)
    by (auto simp add: pmf.map_comp o_def case_prod_unfold Un_commute)
  then have *: "pmf_of_set (Pow V) =
    map_pmf (\<lambda>(x, y). x \<union> y)
     (pair_pmf (pmf_of_set (Pow (V - {x}))) (pmf_of_set (Pow {x})))"
    unfolding e[symmetric]
    apply (subst pmf_of_set_prod)
    using V by auto

  have **: "((\<lambda>(x, y). x \<union> y) -` (E \<inter> S)) \<inter> (Pow (V - {x}) \<times> Pow{x}) =
    Sigma E (\<lambda>x. {y. (x \<union> y) \<in> S}) \<inter> (Pow (V - {x}) \<times> Pow{x})" for S
  proof -
    have 11: "\<And>a b. a \<union> b \<in> E \<Longrightarrow>
           a \<union> b \<in> S \<Longrightarrow>
           a \<subseteq> V - {x} \<Longrightarrow>
           b \<subseteq> {x} \<Longrightarrow> a \<in> E"
      by (metis Diff_insert_absorb Un_insert_right assms(4) boolean_algebra_cancel.sup0 subset_Diff_insert subset_singleton_iff)

    have 21: " \<And>a b. a \<in> E \<Longrightarrow>
           a \<union> b \<in> S \<Longrightarrow>
           a \<subseteq> V - {x} \<Longrightarrow>
           b \<subseteq> {x} \<Longrightarrow> a \<union> b \<in> E"
      by (metis Diff_cancel Un_Diff Un_empty_left assms(4) inf_sup_aci(5) subset_singletonD)

    have 1: "
      \<And>ab.  ab \<in> ((\<lambda>(x, y). x \<union> y) -` (E \<inter> S)) \<inter> (Pow (V - {x}) \<times> Pow{x}) \<Longrightarrow>
        ab \<in> Sigma E (\<lambda>x. {y. (x \<union> y) \<in> S}) \<inter> (Pow (V - {x}) \<times> Pow{x})"
        using 11 by clarsimp

    also have 2: "
      \<And>ab. ab \<in> Sigma E (\<lambda>x. {y. (x \<union> y) \<in> S}) \<inter> (Pow (V - {x}) \<times> Pow{x}) \<Longrightarrow>
         ab \<in> ((\<lambda>(x, y). x \<union> y) -` (E \<inter> S)) \<inter> (Pow (V - {x}) \<times> Pow{x})"
      using 21 by clarsimp
    ultimately show ?thesis
      apply (intro antisym)
      by (meson subsetI)+
  qed

  have eR: "\<And>a. a \<in> E \<inter> set_pmf (pmf_of_set (Pow (V - {x}))) \<Longrightarrow>
   measure_pmf.prob (pmf_of_set (Pow {x}))
    ({y. even (card ((a \<union> y) \<inter> \<omega>)) = b} \<inter>
     set_pmf (pmf_of_set (Pow {x}))) = 1/2 "
    apply (subst measure_Int_set_pmf)
    apply (intro single_var_parity_coin_flip)
    subgoal using assms by clarsimp
    subgoal using assms rev_finite_subset by blast
    subgoal by (metis 2 IntD2 PowD assms(1) finite_Diff rev_finite_subset)
    using 2 by blast

  have "
    prob_space.prob (pmf_of_set (Pow V))
      (E \<inter> {c. even (card (c \<inter> \<omega>)) = b}) =
    prob_space.prob (map_pmf (\<lambda>(x, y). x \<union> y)
       (pair_pmf (pmf_of_set (Pow (V - {x}))) (pmf_of_set (Pow {x}))))
      (E \<inter> {c. even (card (c \<inter> \<omega>)) = b})" unfolding * by auto
  moreover have "... =
    prob_space.prob (pair_pmf (pmf_of_set (Pow (V - {x}))) (pmf_of_set (Pow {x})))
      ((\<lambda>(x, y). x \<union> y) -` (E \<inter> {c. even (card (c \<inter> \<omega>)) = b}))"
    by auto
  moreover have "... =
   prob_space.prob (pair_pmf (pmf_of_set (Pow (V - {x}))) (pmf_of_set (Pow {x})))
    ((\<lambda>(x, y). x \<union> y) -` (E \<inter> {c. even (card (c \<inter> \<omega>)) = b}) \<inter> (Pow (V - {x}) \<times> Pow{x}))"
    by (smt (verit) "1" "2" Int_iff Sigma_cong measure_pmf.measure_pmf_eq set_pair_pmf)
  moreover have "... =
   prob_space.prob (pair_pmf (pmf_of_set (Pow (V - {x}))) (pmf_of_set (Pow {x})))
    (Sigma E (\<lambda>x. {y. even (card ((x \<union> y) \<inter> \<omega>)) = b}) \<inter> (Pow (V - {x}) \<times> Pow{x}))"
    unfolding ** by auto
  moreover have "... =
   prob_space.prob (pair_pmf (pmf_of_set (Pow (V - {x}))) (pmf_of_set (Pow {x})))
    (Sigma E (\<lambda>x. {y. even (card ((x \<union> y) \<inter> \<omega>)) = b}))"
    by (smt (verit, best) 1 2 Int_iff Sigma_cong measure_pmf.measure_pmf_eq set_pair_pmf)
  moreover have "... =
    measure_pmf.prob (pmf_of_set (Pow (V - {x}))) E *
    (1 / 2)"
    apply (subst measure_pmf_prob_dependent_product_bound_eq'[OF _ _ eR])
    by auto
  ultimately show ?thesis by auto
qed

lemma prob_random_xor_split:
  assumes V: "finite V"
  shows "prob_space.prob (random_xor V) E =
    1 / 2 * prob_space.prob (pmf_of_set (Pow V)) {e. (e,True) \<in> E} +
    1 / 2 * prob_space.prob (pmf_of_set (Pow V)) {e. (e,False) \<in> E}"
proof -
  have fin: "finite (set_pmf (random_xor V))"
    by (simp add: V set_pmf_random_xor)

  have fin2: "finite ((\<lambda>(x, y). (y, x)) -` set_pmf (random_xor V))"
    by(auto intro!: finite_vimageI[OF fin] simp add: inj_def)

  have rw: "{x. (x, b) \<in> E \<and> (x, b) \<in> set_pmf (random_xor V)} =
    {x. (x,b) \<in> E} \<inter> set_pmf (pmf_of_set (Pow V))" for b
    by (auto simp add: V set_pmf_random_xor Pow_not_empty)

  have "prob_space.prob (random_xor V) E =
    prob_space.prob (random_xor V) (E \<inter> set_pmf (random_xor V))"
    by (simp add: measure_Int_set_pmf)

  moreover have "... =
     measure_pmf.prob
     (pair_pmf (bernoulli_pmf (1 / 2))
       (pmf_of_set (Pow V)))
     ((\<lambda>(x, y). (y, x)) -` (E \<inter> set_pmf (random_xor V)))"
    unfolding random_xor_def
    apply (subst pair_commute_pmf)
    by simp
  moreover have "... =
    1 / 2 *
      measure_pmf.prob (pmf_of_set (Pow V)) {x. (x, True) \<in> E} +
    1 / 2 *
      measure_pmf.prob (pmf_of_set (Pow V)) {x. (x, False) \<in> E}"
    unfolding pair_pmf_def
    apply (subst prob_bernoulli_bind_pmf)
    using fin2
    unfolding map_pmf_def[symmetric] measure_map_pmf
    by (auto simp add: vimage_def rw simp add: measure_Int_set_pmf)
  ultimately show ?thesis by auto
qed

lemma prob_random_xor_nonempty_parity:
  assumes V: "finite V"
  assumes \<omega>: "x \<in> \<omega>" "\<omega> \<subseteq> V"
  assumes E: "\<And>c. c \<in> E \<longleftrightarrow> (fst c - {x},snd c) \<in> E"
  shows "prob_space.prob (random_xor V)
    (E \<inter> {c. satisfies_xor c \<omega> = b}) =
    1 / 2 * prob_space.prob (random_xor (V - {x})) E"
proof -
  have *: "{e. (e, b') \<in> E \<inter> {c. satisfies_xor c \<omega> = b}} =
    {e. (e, b') \<in> E} \<inter> {c. even (card (c \<inter> \<omega>)) = (b \<noteq> b')}" for b'
    by (auto simp add: Int_commute)

  have "prob_space.prob (random_xor V)
    (E \<inter> {c. satisfies_xor c \<omega> = b})  =
    1 / 2 *
    measure_pmf.prob (pmf_of_set (Pow V))
     {e. (e, True) \<in> E \<inter> {c. satisfies_xor c \<omega> = b}} +
    1 / 2 *
    measure_pmf.prob (pmf_of_set (Pow V))
     {e. (e, False) \<in> E \<inter> {c. satisfies_xor c \<omega> = b}}"
    unfolding prob_random_xor_split[OF V] by auto
  also have "... =
    1 / 2 *
    measure_pmf.prob (pmf_of_set (Pow V))
     ({e. (e, True) \<in> E} \<inter> {c. even (card (c \<inter> \<omega>)) = (b \<noteq> True)}) +
    1 / 2 *
    measure_pmf.prob (pmf_of_set (Pow V))
     ({e. (e, False) \<in> E} \<inter> {c. even (card (c \<inter> \<omega>)) = (b \<noteq> False)})"
    unfolding * by auto
  also have "... =
    1 / 2 *
    (1 / 2 *
     measure_pmf.prob (pmf_of_set (Pow (V - {x})))
      {e. (e, True) \<in> E} +
     1 / 2 *
     measure_pmf.prob (pmf_of_set (Pow (V - {x})))
      {e. (e, False) \<in> E})"
    apply (subst prob_pmf_of_set_nonempty_parity[OF V \<omega>])
    subgoal using E by clarsimp
    apply (subst prob_pmf_of_set_nonempty_parity[OF V \<omega>])
    using E by auto
  also have "... =
    1 / 2 * measure_pmf.prob (random_xor (V - {x})) E"
    apply (subst prob_random_xor_split[symmetric])
    using V by auto
  finally show ?thesis by auto
qed

lemma pair_satisfies_random_xor_parity_1:
  assumes V:"finite V"
  assumes x: "x \<notin> \<omega>" "x \<in> \<omega>'"
  assumes \<omega>: "\<omega> \<subseteq> V" "\<omega>' \<subseteq> V"
  shows "prob_space.prob (random_xor V)
    {c. satisfies_xor c \<omega> = b \<and> satisfies_xor c \<omega>' = b'} = 1 / 4"
proof -
  have wa: "\<omega> \<inter> (a - {x}) = \<omega> \<inter> a" for a
    using x
    by blast
  have "prob_space.prob (random_xor V)
    {c. satisfies_xor c \<omega> = b \<and> satisfies_xor c \<omega>' = b'} =
    prob_space.prob (random_xor V)
    ({c. satisfies_xor c \<omega> = b} \<inter> {c. satisfies_xor c \<omega>' = b'})"
    by (simp add: Collect_conj_eq)
  also have "... =
    1 / 2 *
    measure_pmf.prob (random_xor (V - {x})) {c. satisfies_xor c \<omega> = b}"
    apply (subst prob_random_xor_nonempty_parity[OF V x(2) \<omega>(2)])
    by (auto simp add: wa)
  also have "... = 1/4"
    apply (subst satisfies_random_xor_parity)
    using V by auto
  finally show ?thesis by auto
qed

lemma pair_satisfies_random_xor_parity:
  assumes V:"finite V"
  assumes \<omega>: "\<omega> \<noteq> \<omega>'" "\<omega> \<subseteq> V" "\<omega>' \<subseteq> V"
  shows "prob_space.prob (random_xor V)
    {c. satisfies_xor c \<omega> = b \<and> satisfies_xor c \<omega>' = b'} = 1 / 4"
proof -
  obtain x where "x \<notin> \<omega> \<and> x \<in> \<omega>' \<or> x \<notin> \<omega>' \<and> x \<in> \<omega>"
    using \<omega>
    by blast
  moreover {
    assume x: "x \<notin> \<omega>" "x \<in> \<omega>'"
    have ?thesis using pair_satisfies_random_xor_parity_1[OF V x \<omega>(2-3)]
      by blast
  }
  moreover {
    assume x: "x \<notin> \<omega>'" "x \<in> \<omega>"
    then have ?thesis using pair_satisfies_random_xor_parity_1[OF V x \<omega>(3) \<omega>(2)]
      by (simp add: Collect_conj_eq Int_commute)
  }
  ultimately show ?thesis by auto
qed

lemma prob_pmf_of_set_nonempty_parity_UNIV:
  assumes "finite V"
  assumes "x \<in> \<omega>" "\<omega> \<subseteq> V"
  shows "prob_space.prob (pmf_of_set (Pow V))
    {c. even (card (c \<inter> \<omega>)) = b} = 1 / 2"
  using prob_pmf_of_set_nonempty_parity[OF assms, of UNIV]
  by auto

lemma prob_Pow_split:
  assumes "\<omega> \<subseteq> V" "finite V"
  shows "prob_space.prob (pmf_of_set (Pow V))
    {x. P (\<omega> \<inter> x) \<and> Q ((V - \<omega>) \<inter> x)} =
  prob_space.prob (pmf_of_set (Pow \<omega>))
    {x. P x} *
  prob_space.prob (pmf_of_set (Pow (V - \<omega>)))
    {x. Q x}"
proof -
  have 1: "set_pmf (pmf_of_set (Pow \<omega>)) = Pow \<omega>"
    by (meson Pow_not_empty assms(1) assms(2) finite_Pow_iff finite_subset set_pmf_of_set)
  have 2: "set_pmf
         (pmf_of_set (Pow (V - \<omega>))) = Pow (V - \<omega> )"
    by (simp add: Pow_not_empty assms(2))

  have *: "(pmf_of_set (Pow \<omega> \<times> Pow (V - \<omega>))) =
     (pair_pmf (pmf_of_set (Pow \<omega>)) (pmf_of_set (Pow (V - \<omega>))))"
    unfolding 1 2
    apply (subst pmf_of_set_prod)
    using assms rev_finite_subset by auto
  have **: "(((\<lambda>(x, y). x \<union> y) -`
      {x. P (\<omega> \<inter> x) \<and> Q ((V - \<omega>) \<inter> x)}) \<inter> ((Pow \<omega>) \<times> (Pow (V - \<omega>)))) =
    ({x. P x} \<inter> Pow \<omega>) \<times> ({x. Q x} \<inter> Pow (V - \<omega>))"
    apply (rule antisym)
    subgoal
      apply clarsimp
      by (smt (verit) Diff_disjoint Int_Un_eq(4) inf.orderE inf_commute inf_sup_distrib1 sup_bot.right_neutral sup_commute)
    apply (intro subsetI)
    apply clarsimp
    by (smt (verit, ccfv_threshold) Diff_Int Diff_disjoint Diff_empty Diff_eq_empty_iff Un_Int_assoc_eq Un_commute sup_bot.left_neutral)

  have "prob_space.prob (pmf_of_set (Pow V))
    {x. P (\<omega> \<inter> x) \<and> Q ((V - \<omega>) \<inter> x)} =
    prob_space.prob (map_pmf (\<lambda>(x,y). x \<union> y)
      (pmf_of_set (Pow \<omega> \<times> Pow (V - \<omega>))))
    {x. P (\<omega> \<inter> x) \<and>  Q ((V - \<omega>) \<inter> x)}"
    apply (subst pmf_of_set_powerset_split[symmetric, OF assms(1-2)])
    by auto
  moreover have "... =
    measure_pmf.prob
     (pair_pmf (pmf_of_set (Pow \<omega>)) (pmf_of_set (Pow (V - \<omega>))))
     ((\<lambda>(x, y). x \<union> y) -`
      {x. P (\<omega> \<inter> x) \<and> Q ((V - \<omega>) \<inter> x)})"
    unfolding measure_map_pmf
    using *
    by presburger
  moreover have "... =
    measure_pmf.prob
     (pair_pmf (pmf_of_set (Pow \<omega>)) (pmf_of_set (Pow (V - \<omega>))))
     (((\<lambda>(x, y). x \<union> y) -`
      {x. P (\<omega> \<inter> x) \<and> Q ((V - \<omega>) \<inter> x)}) \<inter> ((Pow \<omega>) \<times> (Pow (V - \<omega>))))"
    using 1 2
    by (smt (verit) Int_Collect Int_def Sigma_cong inf_idem measure_pmf.measure_pmf_eq set_pair_pmf)
  moreover have "... =
     measure_pmf.prob
     (pair_pmf (pmf_of_set (Pow \<omega>)) (pmf_of_set (Pow (V - \<omega>))))
      (({x. P x} \<inter> Pow \<omega>) \<times> ({x. Q x} \<inter> Pow (V - \<omega>)))"
    unfolding **
    by auto
  moreover have "... =
     measure_pmf.prob
     (pmf_of_set (Pow \<omega>)) ({x. P x} \<inter> Pow \<omega>) *
     measure_pmf.prob
     (pmf_of_set (Pow (V - \<omega>))) ({x. Q x} \<inter> Pow (V - \<omega>))"
    apply (intro measure_pmf_prob_product)
    subgoal by (meson assms(1) assms(2) countable_finite finite_Int finite_Pow_iff rev_finite_subset)
    by (simp add: assms(2) countable_finite)
  moreover have "... =
     measure_pmf.prob
     (pmf_of_set (Pow \<omega>)) {x. P x} *
     measure_pmf.prob
     (pmf_of_set (Pow (V - \<omega>))) {x. Q x}"
    by (metis "1" "2" measure_Int_set_pmf)
  ultimately show ?thesis by auto
qed

(* Split probability for two disjoint non-empty sets *)
lemma disjoint_prob_pmf_of_set_nonempty:
  assumes \<omega>: "x \<in> \<omega>" "\<omega> \<subseteq> V"
  assumes \<omega>': "x' \<in> \<omega>'" "\<omega>' \<subseteq> V"
  assumes "\<omega> \<inter> \<omega>' = {}"
  assumes V: "finite V"
  shows "prob_space.prob (pmf_of_set (Pow V))
    {c. even (card (\<omega> \<inter> c)) = b \<and> even (card (\<omega>' \<inter> c)) = b'} = 1 / 4"
proof -
  have "prob_space.prob (pmf_of_set (Pow V))
    {c. even (card (\<omega> \<inter> c)) = b \<and> even (card (\<omega>' \<inter> c)) = b'} =
    prob_space.prob (pmf_of_set (Pow V))
    {c. even (card (\<omega> \<inter> c)) = b \<and> even (card (((V - \<omega>) \<inter> c) \<inter> \<omega>')) = b'}"
    by (smt (verit) Collect_cong Diff_Diff_Int Diff_eq_empty_iff Int_Diff Int_commute \<omega>'(2) assms(5) inf.orderE)

  moreover have "... =
    measure_pmf.prob (pmf_of_set (Pow \<omega>))
     {x. even (card x) = b} *
    measure_pmf.prob (pmf_of_set (Pow (V - \<omega>)))
     {x. even (card (x \<inter> \<omega>')) = b'}"
    apply (subst prob_Pow_split)
    using assms by auto
  moreover have "... =
    measure_pmf.prob (pmf_of_set (Pow \<omega>))
     {x. even (card (x \<inter> \<omega>)) = b} *
    measure_pmf.prob (pmf_of_set (Pow (V - \<omega>)))
     {x. even (card (x \<inter> \<omega>')) = b'} "
    by (smt (verit, best) PowD Pow_not_empty \<omega>(2) assms(6) finite_Pow_iff inf.orderE measure_pmf.measure_pmf_eq mem_Collect_eq rev_finite_subset set_pmf_of_set)

   moreover have "... = 1/4"
    apply (subst prob_pmf_of_set_nonempty_parity_UNIV[OF _ \<omega>(1)])
     subgoal using assms rev_finite_subset by blast
     subgoal by simp
    apply (subst prob_pmf_of_set_nonempty_parity_UNIV)
    using assms by auto
  ultimately show ?thesis by auto
qed

lemma measure_pmf_prob_product_finite_set_pmf:
  assumes "finite (set_pmf M)" "finite (set_pmf N)"
  shows "measure_pmf.prob (pair_pmf M N) (A \<times> B) =
  measure_pmf.prob M A * measure_pmf.prob N B"
proof -
  have A: "measure_pmf.prob M A = measure_pmf.prob M (A \<inter> set_pmf M)"
    by (simp add: measure_Int_set_pmf)
  have B: "measure_pmf.prob N B = measure_pmf.prob N (B \<inter> set_pmf N)"
    by (simp add: measure_Int_set_pmf)
  have "measure_pmf.prob M A * measure_pmf.prob N B =
    measure_pmf.prob M (A \<inter> set_pmf M) *  measure_pmf.prob N (B \<inter> set_pmf N)"
    using A B by auto
  moreover have "... = measure_pmf.prob (pair_pmf M N)
     ((A \<inter> set_pmf M) \<times> (B \<inter> set_pmf N))"
    apply (subst measure_pmf_prob_product[symmetric])
    by auto
  moreover have "... = measure_pmf.prob (pair_pmf M N)
     ((A \<times> B) \<inter> set_pmf (pair_pmf M N))"
    by (simp add: Times_Int_Times)
  moreover have "... = measure_pmf.prob (pair_pmf M N)
     ((A \<times> B) )"
    using measure_Int_set_pmf by blast
  ultimately show ?thesis by auto
qed

lemma prob_random_xor_split_space:
  assumes "\<omega> \<subseteq> V" "finite V"
  shows "prob_space.prob (random_xor V)
    {(x,b). P (\<omega> \<inter> x) b \<and> Q ((V - \<omega>) \<inter> x)} =
  prob_space.prob (random_xor \<omega>)
    {(x,b). P x b} *
  prob_space.prob (pmf_of_set (Pow (V - \<omega>)))
    {x. Q x}"
proof -
  have d1: "set_pmf (random_xor \<omega>) = Pow \<omega> \<times> UNIV"
    by (metis assms(1) assms(2) infinite_super set_pmf_random_xor)
  have d2: "set_pmf (pmf_of_set (Pow (V - \<omega>))) = Pow (V- \<omega>)"
    by (simp add: Pow_not_empty assms(2))
  have rhs: "prob_space.prob (random_xor \<omega>)
    {(x,b). P x b} *
  prob_space.prob (pmf_of_set (Pow (V - \<omega>)))
    {x. Q x} =
  prob_space.prob (pair_pmf (random_xor \<omega>) (pmf_of_set (Pow (V - \<omega>))))
    ({(x,b). P x b} \<times> {x. Q x})"
    apply (subst measure_pmf_prob_product_finite_set_pmf)
    subgoal by (metis Pow_def assms(1) assms(2) finite_Collect_subsets finite_SigmaI finite_code rev_finite_subset set_pmf_random_xor)
    using assms by (auto simp add: Pow_not_empty)

  from pmf_of_set_powerset_split[OF assms]
  have *: "pmf_of_set (Pow V) =
    map_pmf (\<lambda>(x, y). x \<union> y)
   (pair_pmf (pmf_of_set (Pow \<omega>)) (pmf_of_set (Pow (V - \<omega>))))"
    by (metis Pow_not_empty assms(1) assms(2) finite_Diff finite_Pow_iff pmf_of_set_prod rev_finite_subset)

  have **: "random_xor V =
    map_pmf (\<lambda>((x,b),y). (x \<union> y,b)) (pair_pmf (random_xor \<omega>) (pmf_of_set (Pow (V - \<omega>))))"
    unfolding random_xor_def *
    including monad_normalisation
    by (auto simp add: pair_pmf_def map_pmf_def case_prod_unfold)

  have "prob_space.prob (random_xor V) {(x,b). P (\<omega> \<inter> x) b \<and> Q ((V - \<omega>) \<inter> x)} =
    measure_pmf.prob
     (pair_pmf (random_xor \<omega>) (pmf_of_set (Pow (V - \<omega>))))
     {y. P (\<omega> \<inter> (fst (fst y) \<union> snd y)) (snd (fst y)) \<and>
         Q ((V - \<omega>) \<inter> (fst (fst y) \<union> snd y))}"
    unfolding **
    by (auto simp add:case_prod_unfold)

  moreover have "... =
  prob_space.prob (pair_pmf (random_xor \<omega>) (pmf_of_set (Pow (V - \<omega>))))
    ({(x,b). P x b} \<times> {x. Q x})"
    apply (intro measure_pmf.measure_pmf_eq[where p ="pair_pmf (random_xor \<omega>)
       (pmf_of_set (Pow (V - \<omega>)))"])
    subgoal by simp
    apply (clarsimp simp add: d1 d2)
    by (smt (verit, del_insts) Diff_disjoint Int_Diff boolean_algebra_cancel.sup0 inf.orderE inf_commute inf_sup_distrib1 sup_bot.left_neutral)
  ultimately show ?thesis using rhs
    by simp
qed

lemma three_disjoint_prob_random_xor_nonempty:
  assumes \<omega>: "\<omega> \<noteq> {}" "\<omega> \<subseteq> V"
  assumes \<omega>': "\<omega>' \<noteq> {}" "\<omega>' \<subseteq> V"
  assumes I: "I \<subseteq> V"
  assumes int: "I \<inter> \<omega> = {}" "I \<inter> \<omega>' = {}" "\<omega> \<inter> \<omega>' = {}"
  assumes V: "finite V"
  shows "prob_space.prob (random_xor V)
    {c. satisfies_xor c I = b \<and>
      even (card (\<omega> \<inter> fst c)) = b' \<and>
      even (card (\<omega>' \<inter> fst c)) = b''} = 1 / 8"
proof -
  have finI: "finite I"
    using V I
    using rev_finite_subset by blast
  have finVI: "finite (V - I)"
    using V I
    using rev_finite_subset by blast
  obtain x x' where x: "x \<in> \<omega>" "x' \<in> \<omega>'" using \<omega> \<omega>'
    by blast

  have rw1:"\<omega> \<inter> ((V - I) \<inter> xx) = \<omega> \<inter>  xx " for xx
    by (metis Diff_Int_distrib2 Diff_empty \<omega>(2) assms(6) inf.absorb_iff2 inf_assoc inf_left_commute)

  have rw2:"\<omega>' \<inter> ((V - I) \<inter> xx)= \<omega>' \<inter>  xx" for xx
    by (metis Diff_Int_distrib2 Diff_empty \<omega>'(2) assms(7) inf.absorb_iff2 inf_assoc inf_left_commute)

  have "prob_space.prob (random_xor V)
    {c. satisfies_xor c I = b \<and>
      even (card ( \<omega> \<inter> fst c )) = b' \<and>
      even (card (\<omega>' \<inter>  fst c )) = b''} =
    prob_space.prob (random_xor V)
    {(x,bb). satisfies_xor (I \<inter> x, bb) I = b \<and>
      even (card (\<omega> \<inter> ((V - I) \<inter> x))) = b' \<and>
      even (card ( \<omega>' \<inter> ((V - I) \<inter> x))) = b''}"
    apply (intro arg_cong[where f = "prob_space.prob (random_xor V)"])
    unfolding rw1 rw2 satisfies_xor_inter
    by (smt (verit) Collect_cong prod.collapse split_conv)

  moreover have "... =
    measure_pmf.prob (random_xor I)
     {c. satisfies_xor c I = b} *
    measure_pmf.prob (pmf_of_set (Pow (V - I)))
     {x. even (card (\<omega> \<inter> x)) = b' \<and>
         even (card (\<omega>' \<inter> x)) = b''}"
    apply (subst prob_random_xor_split_space[OF I V])
    by (metis (no_types, lifting) Collect_cong case_prodE case_prodI2)
  moreover have "... = 1 / 8"
    apply (subst satisfies_random_xor_parity[OF finI])
    apply (subst disjoint_prob_pmf_of_set_nonempty)
    using x \<omega> \<omega>' int finVI by auto
  ultimately show ?thesis by auto
qed

(* Split probability for three disjoint non-empty sets *)
lemma three_disjoint_prob_pmf_of_set_nonempty:
  assumes \<omega>: "x \<in> \<omega>" "\<omega> \<subseteq> V"
  assumes \<omega>': "x' \<in> \<omega>'" "\<omega>' \<subseteq> V"
  assumes \<omega>'': "x'' \<in> \<omega>''" "\<omega>'' \<subseteq> V"
  assumes int: "\<omega> \<inter> \<omega>' = {}" "\<omega>' \<inter> \<omega>'' = {}" "\<omega>'' \<inter> \<omega> = {}"
  assumes V: "finite V"
  shows "prob_space.prob (pmf_of_set (Pow V))
    {c. even (card (\<omega> \<inter> c)) = b \<and> even (card (\<omega>' \<inter> c)) = b' \<and> even (card (\<omega>'' \<inter> c)) = b''} = 1 / 8"
proof -
  have "prob_space.prob (pmf_of_set (Pow V))
    {c. even (card (\<omega> \<inter> c)) = b \<and> even (card (\<omega>' \<inter> c)) = b' \<and> even (card (\<omega>'' \<inter> c)) = b''} =
    prob_space.prob (pmf_of_set (Pow V))
    {c. even (card (\<omega> \<inter> c)) = b \<and>
        even (card (((V - \<omega>) \<inter> c) \<inter> \<omega>')) = b' \<and>
        even (card (((V - \<omega>) \<inter> c) \<inter> \<omega>'')) = b''}"
    by (smt (verit,best) Collect_cong Diff_Diff_Int Diff_eq_empty_iff Int_Diff Int_commute \<omega>' \<omega>'' int inf.orderE)

  moreover have "... =
    measure_pmf.prob (pmf_of_set (Pow \<omega>))
     {x. even (card x) = b} *
    measure_pmf.prob (pmf_of_set (Pow (V - \<omega>)))
     {x. even (card (\<omega>' \<inter> x)) = b' \<and> even (card (\<omega>'' \<inter> x)) = b''}"
    apply (subst prob_Pow_split)
    using assms by (auto simp add: inf.commute)
  moreover have "... =
    measure_pmf.prob (pmf_of_set (Pow \<omega>))
     {x. even (card (x \<inter> \<omega>)) = b} *
    measure_pmf.prob (pmf_of_set (Pow (V - \<omega>)))
     {x. even (card (\<omega>' \<inter> x)) = b'\<and> even (card (\<omega>'' \<inter> x)) = b''} "
    by (smt (verit, best) PowD Pow_not_empty \<omega> V finite_Pow_iff inf.orderE measure_pmf.measure_pmf_eq mem_Collect_eq rev_finite_subset set_pmf_of_set)

   moreover have "... = 1/8"
    apply (subst prob_pmf_of_set_nonempty_parity_UNIV[OF _ \<omega>(1)])
     subgoal using \<omega>(2) V rev_finite_subset by blast
     subgoal by simp
     apply (subst disjoint_prob_pmf_of_set_nonempty)
     using assms by auto
  ultimately show ?thesis by auto
qed

lemma four_disjoint_prob_random_xor_nonempty:
  assumes \<omega>: "\<omega> \<noteq> {}" "\<omega> \<subseteq> V"
  assumes \<omega>': "\<omega>' \<noteq> {}" "\<omega>' \<subseteq> V"
  assumes \<omega>'': "\<omega>'' \<noteq> {}" "\<omega>'' \<subseteq> V"
  assumes I: "I \<subseteq> V"
  assumes int: "I \<inter> \<omega> = {}" "I \<inter> \<omega>' = {}" "I \<inter> \<omega>'' = {}"
    "\<omega> \<inter> \<omega>' = {}" "\<omega>' \<inter> \<omega>'' = {}" "\<omega>'' \<inter> \<omega> = {}"
  assumes V: "finite V"
  shows "prob_space.prob (random_xor V)
    {c. satisfies_xor c I = b0 \<and>
      even (card (\<omega> \<inter> fst c)) = b \<and>
      even (card (\<omega>' \<inter> fst c)) = b' \<and>
      even (card (\<omega>'' \<inter> fst c)) = b''} = 1 / 16"
proof -
  have finI: "finite I"
    using V I
    using rev_finite_subset by blast
  have finVI: "finite (V - I)"
    using V I
    using rev_finite_subset by blast
  obtain x x' x'' where x: "x \<in> \<omega>" "x' \<in> \<omega>'" "x'' \<in> \<omega>''"
    using \<omega> \<omega>' \<omega>''
    by blast

  have rw1:"\<omega> \<inter> ((V - I) \<inter> xx) = \<omega> \<inter>  xx " for xx
    by (metis Diff_Int_distrib2 Diff_empty \<omega>(2) int(1) inf.absorb_iff2 inf_assoc inf_left_commute)

  have rw2:"\<omega>' \<inter> ((V - I) \<inter> xx)= \<omega>' \<inter>  xx" for xx
    by (metis Diff_Int_distrib2 Diff_empty \<omega>'(2) int(2) inf.absorb_iff2 inf_assoc inf_left_commute)

  have rw3:"\<omega>'' \<inter> ((V - I) \<inter> xx)= \<omega>'' \<inter>  xx" for xx
    by (metis Diff_Int_distrib2 Diff_empty \<omega>''(2) int(3) inf.absorb_iff2 inf_assoc inf_left_commute)

  have "prob_space.prob (random_xor V)
    {c. satisfies_xor c I = b0 \<and>
      even (card (\<omega> \<inter> fst c)) = b \<and>
      even (card (\<omega>' \<inter>  fst c)) = b' \<and>
      even (card (\<omega>'' \<inter>  fst c)) = b''} =
    prob_space.prob (random_xor V)
    {(x,bb). satisfies_xor (I \<inter> x, bb) I = b0 \<and>
      even (card (\<omega> \<inter> ((V - I) \<inter> x))) = b \<and>
      even (card (\<omega>' \<inter> ((V - I) \<inter> x))) = b' \<and>
      even (card (\<omega>'' \<inter> ((V - I) \<inter> x))) = b''}"
    apply (intro arg_cong[where f = "prob_space.prob (random_xor V)"])
    unfolding rw1 rw2 rw3 satisfies_xor_inter
    by (smt (verit) Collect_cong prod.collapse split_conv)

  moreover have "... =
    measure_pmf.prob (random_xor I)
     {c. satisfies_xor c I = b0} *
    measure_pmf.prob (pmf_of_set (Pow (V - I)))
     {x. even (card (\<omega> \<inter> x)) = b \<and>
         even (card (\<omega>' \<inter> x)) = b' \<and>
         even (card (\<omega>'' \<inter> x)) = b''}"
    apply (subst prob_random_xor_split_space[OF I V])
    by (metis (no_types, lifting) Collect_cong case_prodE case_prodI2)
  moreover have "... = 1 / 16"
    apply(subst satisfies_random_xor_parity[OF finI])
    apply (subst three_disjoint_prob_pmf_of_set_nonempty)
    using x \<omega> \<omega>' \<omega>'' int finVI by auto
  ultimately show ?thesis by auto
qed

lemma three_satisfies_random_xor_parity_1:
  assumes V:"finite V"
  assumes \<omega>: "\<omega> \<subseteq> V" "\<omega>' \<subseteq> V" "\<omega>'' \<subseteq> V"
  assumes x: "x \<notin> \<omega>" "x \<notin> \<omega>'" "x \<in> \<omega>''"
  assumes d: "\<omega> \<noteq> \<omega>'"
  shows "prob_space.prob (random_xor V)
    {c.
    satisfies_xor c \<omega> = b \<and>
    satisfies_xor c \<omega>' = b' \<and>
    satisfies_xor c \<omega>'' = b''} = 1 / 8"
proof -
  have wa: "\<omega> \<inter> (a - {x}) = \<omega> \<inter> a" for a
    using x
    by blast
  have wa': "\<omega>' \<inter> (a - {x}) = \<omega>' \<inter> a" for a
    using x
    by blast
  have "prob_space.prob (random_xor V)
    {c.
      satisfies_xor c \<omega> = b \<and> satisfies_xor c \<omega>' = b' \<and>
      satisfies_xor c \<omega>'' = b''} =
    prob_space.prob (random_xor V)
    ({c. satisfies_xor c \<omega> = b \<and> satisfies_xor c \<omega>' = b'} \<inter>
      {c. satisfies_xor c \<omega>'' = b''})"
    by (simp add: Collect_conj_eq inf_assoc)
  moreover have "... =
    1 / 2 *
    measure_pmf.prob (random_xor (V - {x}))
      {c. satisfies_xor c \<omega> = b \<and> satisfies_xor c \<omega>' = b'}"
    apply (subst prob_random_xor_nonempty_parity[OF V x(3) \<omega>(3)])
    by (auto simp add: wa wa')
  moreover have "... = 1/8"
    apply (subst pair_satisfies_random_xor_parity)
    using V \<omega> x d by auto
  ultimately show ?thesis by auto
qed

lemma split_boolean_eq:
  shows"(A \<longleftrightarrow> B) = (b \<longleftrightarrow> I) \<and>
    (B \<longleftrightarrow> C) = (b' \<longleftrightarrow>  I) \<and>
    (C \<longleftrightarrow> A) = (b'' \<longleftrightarrow> I)
  \<longleftrightarrow>
    I = odd(of_bool b + of_bool b' + of_bool b'') \<and>
     (A = True \<and>
      B = (b'=b'') \<and>
      C = (b = b') \<or>
      A = False \<and>
      B = (b' \<noteq> b'') \<and>
      C = (b \<noteq> b'))"
  by auto

lemma three_satisfies_random_xor_parity:
  assumes V:"finite V"
  assumes \<omega>:
      "\<omega> \<noteq> \<omega>'" "\<omega> \<noteq> \<omega>''" "\<omega>' \<noteq> \<omega>''"
      "\<omega> \<subseteq> V" "\<omega>' \<subseteq> V" "\<omega>'' \<subseteq> V"
  shows "prob_space.prob (random_xor V)
    {c. satisfies_xor c \<omega> = b \<and>
        satisfies_xor c \<omega>' = b' \<and>
        satisfies_xor c \<omega>'' = b''} = 1 / 8"
proof -
  have "(\<exists>x.
    x \<in> \<omega> \<and> x \<notin> \<omega>' \<and> x \<notin> \<omega>'' \<or>
    x \<in> \<omega>' \<and> x \<notin> \<omega> \<and> x \<notin> \<omega>'' \<or>
    x \<in> \<omega>'' \<and> x \<notin> \<omega> \<and> x \<notin> \<omega>') \<or>
    \<omega> - (\<omega>' \<union> \<omega>'') = {} \<and>
    \<omega>' - (\<omega> \<union> \<omega>'') = {} \<and>
    \<omega>'' - (\<omega> \<union> \<omega>') = {}"
    by blast
  moreover {
    assume "(\<exists>x.
    x \<in> \<omega> \<and> x \<notin> \<omega>' \<and> x \<notin> \<omega>'' \<or>
    x \<in> \<omega>' \<and> x \<notin> \<omega> \<and> x \<notin> \<omega>'' \<or>
    x \<in> \<omega>'' \<and> x \<notin> \<omega> \<and> x \<notin> \<omega>')"
    then obtain x where "
      x \<in> \<omega> \<and> x \<notin> \<omega>' \<and> x \<notin> \<omega>'' \<or>
      x \<in> \<omega>' \<and> x \<notin> \<omega> \<and> x \<notin> \<omega>'' \<or>
      x \<in> \<omega>'' \<and> x \<notin> \<omega> \<and> x \<notin> \<omega>'" by auto
    moreover {
      assume x: "x \<notin> \<omega>'" "x \<notin> \<omega>''" "x \<in> \<omega>"
      have "measure_pmf.prob (random_xor V)
       {c. satisfies_xor c \<omega>' = b' \<and>
           satisfies_xor c \<omega>'' = b'' \<and>
           satisfies_xor c \<omega> = b} = 1 / 8"
        apply (intro three_satisfies_random_xor_parity_1[OF V _ _ _ x])
        using \<omega> by auto
      then have ?thesis
        by (smt (verit, ccfv_SIG) Collect_cong)
    }
    moreover {
      assume x: "x \<notin> \<omega>" "x \<notin> \<omega>''" "x \<in> \<omega>'"
      have "measure_pmf.prob (random_xor V)
       {c. satisfies_xor c \<omega> = b \<and>
           satisfies_xor c \<omega>'' = b'' \<and>
           satisfies_xor c \<omega>' = b'} = 1 / 8"
        apply (intro three_satisfies_random_xor_parity_1[OF V _ _ _ x])
        using \<omega> by auto
      then have ?thesis
        by (smt (verit, ccfv_SIG) Collect_cong)
    }
    moreover {
      assume x: "x \<notin> \<omega>" "x \<notin> \<omega>'" "x \<in> \<omega>''"
      have "measure_pmf.prob (random_xor V)
       {c. satisfies_xor c \<omega> = b \<and>
           satisfies_xor c \<omega>' = b' \<and>
           satisfies_xor c \<omega>'' = b''} = 1 / 8"
        apply (intro three_satisfies_random_xor_parity_1[OF V _ _ _ x])
        using \<omega> by auto
      then have ?thesis
        by (smt (verit, ccfv_SIG) Collect_cong)
    }
    ultimately have ?thesis by auto
  }
  moreover {
    assume dis: "\<omega> - (\<omega>' \<union> \<omega>'') = {} \<and>
      \<omega>' - (\<omega> \<union> \<omega>'') = {} \<and>
      \<omega>'' - (\<omega> \<union> \<omega>') = {}"

    define A where "A = (\<omega> \<inter> \<omega>'') - \<omega>'"
    define B where "B = (\<omega> \<inter> \<omega>') - \<omega>''"
    define C where "C = (\<omega>' \<inter> \<omega>'') - \<omega>"
    define I where "I = \<omega> \<inter> \<omega>' \<inter> \<omega>''"

    have f: "finite A" "finite B" "finite C" "finite I"
      unfolding A_def B_def C_def I_def
      by (meson V \<omega> finite_Diff finite_Int rev_finite_subset)+

    have s: "A \<subseteq> V" "B \<subseteq> V" "C \<subseteq> V" "I \<subseteq> V"
      unfolding A_def B_def C_def I_def
      using \<omega> by auto

    have i: "I \<inter> A = {}" "I \<inter> B = {}" "I \<inter> C = {}"
        "B \<inter> C = {}" "C \<inter> A = {}" "A \<inter> B = {}"
      unfolding A_def B_def C_def I_def
      by blast +

    have s1: "\<omega> = A \<union> B \<union> I"
      unfolding A_def B_def I_def
      using dis by auto
    have sx1: "satisfies_xor (xx,bb) \<omega> = b \<longleftrightarrow>
      even (card (A \<inter> xx)) = even (card (B \<inter> xx)) = (b \<longleftrightarrow> satisfies_xor(xx,bb) I)" for xx bb
      unfolding s1 satisfies_xor.simps Int_Un_distrib2
      apply (subst card_Un_disjoint)
      subgoal using f by auto
      subgoal using f by auto
      subgoal using A_def B_def I_def by blast
      apply (subst card_Un_disjoint)
      subgoal using f by auto
      subgoal using f by auto
      subgoal using A_def B_def I_def by blast
      by auto

    have s2: "\<omega>' = B \<union> C \<union> I"
      unfolding B_def C_def I_def
      using dis by auto
    have sx2: "satisfies_xor (xx,bb) \<omega>' = b' \<longleftrightarrow>
      even (card (B \<inter> xx)) = even (card (C \<inter> xx)) = (b' \<longleftrightarrow> satisfies_xor(xx,bb) I)" for xx bb
      unfolding s2 satisfies_xor.simps Int_Un_distrib2
      apply (subst card_Un_disjoint)
      subgoal using f by auto
      subgoal using f by auto
      subgoal using B_def C_def I_def by blast
      apply (subst card_Un_disjoint)
      subgoal using f by auto
      subgoal using f by auto
      subgoal using B_def C_def I_def by blast
      by auto

    have s3: "\<omega>'' = A \<union> C \<union> I"
      unfolding A_def C_def I_def
      using dis by auto
    have sx3: "satisfies_xor (xx,bb) \<omega>'' = b'' \<longleftrightarrow>
      even (card (C \<inter> xx)) = even (card (A \<inter> xx)) = (b'' \<longleftrightarrow> satisfies_xor(xx,bb) I)" for xx bb
      unfolding s3 satisfies_xor.simps Int_Un_distrib2
      apply (subst card_Un_disjoint)
      subgoal using f by auto
      subgoal using f by auto
      subgoal using A_def B_def C_def I_def by blast
      apply (subst card_Un_disjoint)
      subgoal using f by auto
      subgoal using f by auto
      subgoal using A_def B_def C_def I_def by blast
      by auto

    have "A = {} \<and> B \<noteq> {} \<and> C \<noteq> {} \<or>
      A \<noteq> {} \<and> B = {} \<and> C \<noteq> {} \<or>
      A \<noteq> {} \<and> B \<noteq> {} \<and> C = {} \<or>
      A \<noteq> {} \<and> B \<noteq> {} \<and> C \<noteq> {}"
      by (metis Un_commute \<omega>(1) \<omega>(2) \<omega>(3) s1 s2 s3)

    moreover {
      assume as: "A = {}" "B \<noteq> {}" "C \<noteq> {}"
      have "satisfies_xor (xx,bb) \<omega> = b
        \<and> satisfies_xor (xx,bb) \<omega>' = b'
        \<and> satisfies_xor (xx,bb) \<omega>'' = b'' \<longleftrightarrow>
      (satisfies_xor (xx, bb) I =
       odd (of_bool b + of_bool b' + of_bool b'') \<and>
       (even (card (B \<inter> xx)) = (b' = b'') \<and>
        even (card (C \<inter> xx)) = (b = b')))" for xx bb
        unfolding sx1 sx2 sx3
        apply(subst split_boolean_eq)
        using as by simp
      then have *: "{c. satisfies_xor c \<omega> = b
        \<and> satisfies_xor c \<omega>' = b'
        \<and> satisfies_xor c \<omega>'' = b''} =
      {c. satisfies_xor c I =
       odd (of_bool b + of_bool b' + of_bool b'') \<and>
       even (card (B \<inter> fst c)) = (b' = b'') \<and>
       even (card (C \<inter> fst c)) = (b = b')}"
        by (smt (verit,best) Collect_cong prod.collapse)
      have ?thesis
        apply (subst *)
        apply (intro three_disjoint_prob_random_xor_nonempty)
        using as s i V by auto
    }

    moreover {
      assume as: "A \<noteq> {}" "B \<noteq> {}" "C = {}"
      have "satisfies_xor (xx,bb) \<omega>'' = b''
        \<and> satisfies_xor (xx,bb) \<omega> = b
        \<and> satisfies_xor (xx,bb) \<omega>' = b' \<longleftrightarrow>
      (satisfies_xor (xx, bb) I =
       odd (of_bool b'' + of_bool b + of_bool b') \<and>
       (even (card (A \<inter> xx)) = (b = b') \<and>
        even (card (B \<inter> xx)) = (b'' = b)))" for xx bb
        unfolding sx1 sx2 sx3
        apply(subst split_boolean_eq)
        using as by simp
      then have *: "{c. satisfies_xor c \<omega> = b
        \<and> satisfies_xor c \<omega>' = b'
        \<and> satisfies_xor c \<omega>'' = b''} =
      {c. satisfies_xor c I =
       odd (of_bool b'' + of_bool b + of_bool b') \<and>
       (even (card (A \<inter> fst c)) = (b = b') \<and>
        even (card (B \<inter> fst c)) = (b'' = b))}"
        by (smt (verit,best) Collect_cong prod.collapse)
      have ?thesis
        apply (subst *)
        apply (intro three_disjoint_prob_random_xor_nonempty)
        using as s i V by auto
    }

    moreover {
      assume as: "A \<noteq> {}" "B = {}" "C \<noteq> {}"
      have "satisfies_xor (xx,bb) \<omega>' = b'
        \<and> satisfies_xor (xx,bb) \<omega>'' = b''
        \<and> satisfies_xor (xx,bb) \<omega> = b \<longleftrightarrow>
      (satisfies_xor (xx, bb) I =
       odd (of_bool b' + of_bool b'' + of_bool b) \<and>
       (even (card (C \<inter> xx)) = (b'' = b) \<and>
        even (card (A \<inter> xx)) = (b' = b'')))" for xx bb
        unfolding sx1 sx2 sx3
        apply(subst split_boolean_eq)
        using as by simp
      then have *: "{c. satisfies_xor c \<omega> = b
        \<and> satisfies_xor c \<omega>' = b'
        \<and> satisfies_xor c \<omega>'' = b''} =
      {c. satisfies_xor c I =
       odd (of_bool b' + of_bool b'' + of_bool b) \<and>
       (even (card (C \<inter> fst c)) = (b'' = b) \<and>
        even (card (A \<inter> fst c)) = (b' = b''))}"
        by (smt (verit,best) Collect_cong prod.collapse)
      have ?thesis
        apply (subst *)
        apply (intro three_disjoint_prob_random_xor_nonempty)
        using as s i V by auto
    }

    moreover {
      assume as: "A \<noteq> {}" "B \<noteq> {}" "C \<noteq> {}"
      have 1: "satisfies_xor (xx,bb) \<omega> = b
        \<and> satisfies_xor (xx,bb) \<omega>' = b'
        \<and> satisfies_xor (xx,bb) \<omega>'' = b'' \<longleftrightarrow>
      (satisfies_xor (xx, bb) I =
        odd (of_bool b + of_bool b' + of_bool b'') \<and>
        even (card (A \<inter> xx)) = True \<and>
        even (card (B \<inter> xx)) = (b' = b'') \<and>
        even (card (C \<inter> xx)) = (b = b') \<or>
       satisfies_xor (xx, bb) I =
        odd (of_bool b + of_bool b' + of_bool b'') \<and>
        even (card (A \<inter> xx)) = False \<and>
        even (card (B \<inter> xx)) = (b' \<noteq> b'') \<and>
        even (card (C \<inter> xx)) = (b \<noteq> b'))" for xx bb
        unfolding sx1 sx2 sx3
        apply(subst split_boolean_eq)
        by auto
      have 2: "satisfies_xor c \<omega> = b
        \<and> satisfies_xor c \<omega>' = b'
        \<and> satisfies_xor c \<omega>'' = b'' \<longleftrightarrow>
      (satisfies_xor c I =
        odd (of_bool b + of_bool b' + of_bool b'') \<and>
        even (card (A \<inter> fst c)) = True \<and>
        even (card (B \<inter> fst c)) = (b' = b'') \<and>
        even (card (C \<inter> fst c)) = (b = b') \<or>
       satisfies_xor c I =
        odd (of_bool b + of_bool b' + of_bool b'') \<and>
        even (card (A \<inter> fst c)) = False \<and>
        even (card (B \<inter> fst c)) = (b' \<noteq> b'') \<and>
        even (card (C \<inter> fst c)) = (b \<noteq> b'))" for c
      proof -
        obtain xx bb where c:"c = (xx,bb)" by fastforce
        show ?thesis unfolding c
          apply (subst 1)
          by auto
      qed
      have *: "{c. satisfies_xor c \<omega> = b
        \<and> satisfies_xor c \<omega>' = b'
        \<and> satisfies_xor c \<omega>'' = b''} =
      {c. satisfies_xor c I =
        odd (of_bool b + of_bool b' + of_bool b'') \<and>
        even (card (A \<inter> fst c)) = True \<and>
        even (card (B \<inter> fst c)) = (b' = b'') \<and>
        even (card (C \<inter> fst c)) = (b = b')} \<union>
      {c. satisfies_xor c I =
        odd (of_bool b + of_bool b' + of_bool b'') \<and>
        even (card (A \<inter> fst c)) = False \<and>
        even (card (B \<inter> fst c)) = (b' \<noteq> b'') \<and>
        even (card (C \<inter> fst c)) = (b \<noteq> b')}"
        apply (subst Un_def)
        apply (intro Collect_cong)
        apply (subst 2)
        by simp

      have **: "1 / 16 +
        measure_pmf.prob (random_xor V)
         {c. satisfies_xor c I =
             odd (of_bool b + of_bool b' +
                  of_bool b'') \<and>
             even (card (A \<inter> fst c)) =
             False \<and>
             even (card (B \<inter> fst c)) =
             (b' \<noteq> b'') \<and>
             even (card (C \<inter> fst c)) =
             (b \<noteq> b')} =
        1 / 8" 
        apply (subst four_disjoint_prob_random_xor_nonempty)
        using as s i V by auto
      have ?thesis
        apply (subst *)
        apply (subst measure_pmf.finite_measure_Union)
        subgoal by simp
        subgoal by simp
        subgoal by auto
        apply (subst four_disjoint_prob_random_xor_nonempty)
        using as s i V ** by auto
    }

    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by auto
qed

subsection "Independence for repeated XORs"

text \<open> We can lift the previous result to a list of independent sampled XORs. \<close>

definition random_xors :: "'a set \<Rightarrow> nat \<Rightarrow>
    (nat \<rightharpoonup> 'a set \<times> bool) pmf"
  where "random_xors V n =
    Pi_pmf {..<(n::nat)} None
      (\<lambda>_. map_pmf Some (random_xor V))"

(* The set of random XORs expressed in various ways*)
lemma random_xors_set:
  assumes V:"finite V"
  shows
    "PiE_dflt {..<n} None
      (set_pmf \<circ> (\<lambda>_. map_pmf Some (random_xor V))) =
     {xors. dom xors = {..<n} \<and>
        ran xors \<subseteq> (Pow V) \<times> UNIV}" (is "?lhs = ?rhs")
proof -
  have "?lhs =
    {f. dom f = {..<n} \<and>
        (\<forall>x \<in> {..<n}. f x \<in> Some ` (Pow V \<times> UNIV))}"
    unfolding PiE_dflt_def o_def set_map_pmf set_pmf_random_xor[OF V]
    by force

  also have "... = ?rhs"
    apply (rule antisym)
    subgoal
      apply clarsimp
      by (smt (z3) PowD domI image_iff mem_Collect_eq mem_Sigma_iff option.simps(1) ran_def subsetD)
    apply clarsimp
    by (smt (verit, ccfv_threshold) domD image_iff lessThan_iff ranI subsetD)
  finally show ?thesis .
qed

lemma random_xors_eq:
  assumes V:"finite V"
  shows"random_xors V n =
    pmf_of_set
    {xors. dom xors = {..<n} \<and> ran xors \<subseteq> (Pow V) \<times> UNIV}"
proof -
  have "pmf_of_set
    {xors. dom xors = {..<n} \<and>
        ran xors \<subseteq> (Pow V) \<times> UNIV} =
    pmf_of_set
      (PiE_dflt {..<n} None
      (set_pmf \<circ> (\<lambda>_. map_pmf Some (random_xor V))))"
    unfolding random_xors_set[OF V] by auto
  also have "... =
    Pi_pmf {..<n} None
     (\<lambda>x. pmf_of_set
            ((set_pmf \<circ>
              (\<lambda>_. map_pmf Some (random_xor V))) x))"
    apply (subst Pi_pmf_of_set[symmetric])
    by (auto simp add:set_pmf_random_xor[OF V] V)
  also have "... = random_xors V n"
    unfolding random_xors_def o_def set_map_pmf
    apply (subst map_pmf_of_set_inj[symmetric])
    subgoal by (auto simp add:set_pmf_random_xor[OF V] V)
    subgoal by (auto simp add:set_pmf_random_xor[OF V] V)
    subgoal by (auto simp add:set_pmf_random_xor[OF V] V)
    by (metis V random_xor_pmf_of_set set_pmf_random_xor)
  ultimately show ?thesis by auto
qed

(* The XOR hash function from a mapping nat \<rightharpoonup> XOR *)
definition xor_hash ::
  "('a \<rightharpoonup> bool) \<Rightarrow>
   (nat \<rightharpoonup> ('a set \<times> bool)) \<Rightarrow>
   (nat \<rightharpoonup> bool)"
  where "xor_hash \<omega> xors =
      (map_option
        (\<lambda>xor. satisfies_xor xor {x. \<omega> x = Some True}) \<circ> xors)"

lemma finite_map_set_nonempty:
  assumes "R \<noteq> {}"
  shows "
    {xors.
      dom xors = D \<and> ran xors \<subseteq> R} \<noteq> {}"
proof -
  obtain r where "r \<in> R"
    using assms by blast
  then have "(\<lambda>x. if x \<in> D then Some r else None) \<in>
    {xors. dom xors = D \<and> ran xors \<subseteq> R}"
    by (auto split:if_splits simp:ran_def)
  thus ?thesis by auto
qed

lemma random_xors_set_pmf:
  assumes V: "finite V"
  shows "
    set_pmf (random_xors V n) =
      {xors. dom xors = {..<n} \<and>
        ran xors \<subseteq> (Pow V) \<times> UNIV}"
  unfolding random_xors_eq[OF V]
  apply (intro set_pmf_of_set)
  subgoal
    apply (intro finite_map_set_nonempty)
    by blast
  apply (intro finite_set_of_finite_maps)
  by (auto simp add: V)

lemma finite_random_xors_set_pmf:
  assumes V: "finite V"
  shows "
    finite (set_pmf (random_xors V n))"
  unfolding random_xors_set_pmf[OF V]
  by (auto intro!: finite_set_of_finite_maps simp add: V)

lemma map_eq_1:
  assumes "dom f = dom g"
  assumes "\<And>x. x \<in> dom f \<Longrightarrow> the (f x) = the (g x)"
  shows "f = g"
  by (metis assms(1) assms(2) domIff map_le_antisym map_le_def option.expand)

lemma xor_hash_eq_iff:
  assumes "dom \<alpha> = {..<n}"
  shows"xor_hash \<omega> x = \<alpha> \<longleftrightarrow>
  (dom x = {..<n} \<and>
  (\<forall>i. i < n \<longrightarrow>
    (\<exists>xor. x i = Some xor \<and>
    satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> i))
  ))"
proof -
  have 1: "xor_hash \<omega> x = \<alpha> \<longleftrightarrow>
    (dom (xor_hash \<omega> x) = dom \<alpha>) \<and>
    (\<forall>i \<in> dom \<alpha>. the (xor_hash \<omega> x i) = the (\<alpha> i))"
    using map_eq_1 by fastforce
  have 2: "dom (xor_hash \<omega> x) = dom x"
    unfolding xor_hash_def
    by auto
  have 3: "\<And>i. i \<in> dom x \<Longrightarrow>
    xor_hash \<omega> x i = Some (satisfies_xor (the (x i)) {x. \<omega> x = Some True})"
    unfolding xor_hash_def
    by fastforce
  show ?thesis 
    unfolding 1 assms 2
    using 3
    by (smt (verit, best) domD lessThan_iff option.sel)
qed

lemma xor_hash_eq_PiE_dflt:
  assumes "dom \<alpha> = {..<n}"
  shows
    "{xors. xor_hash \<omega> xors = \<alpha>} =
    PiE_dflt {..<n} None
      (\<lambda>i. Some `
        {xor. satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> i)})"
proof -
  have *: "\<And>x xa a b.
       (\<not> xa < n \<longrightarrow> x xa = None) \<Longrightarrow>
       x xa = Some (a, b) \<Longrightarrow> xa < n"
  by (metis option.distinct(2))
  show ?thesis
  unfolding PiE_dflt_def
  unfolding xor_hash_eq_iff[OF assms]
  by (auto intro: * simp del: satisfies_xor.simps)
qed

lemma prob_random_xors_xor_hash:
  assumes V: "finite V"
  assumes \<alpha>: "dom \<alpha> = {..<n}"
  shows "
  measure_pmf.prob (random_xors V n)
    {xors. xor_hash \<omega> xors = \<alpha>} = 1 / 2  ^ n"
proof -
  have "measure_pmf.prob (random_xors V n)
    {xors. xor_hash \<omega> xors = \<alpha>} =
    measure_pmf.prob
    (Pi_pmf {..<(n::nat)} None
      (\<lambda>_. map_pmf Some (random_xor V)))
    (PiE_dflt {..<n} None
      (\<lambda>i. Some ` {xor. satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> i)}))"
    unfolding random_xors_def xor_hash_eq_PiE_dflt[OF \<alpha>]
    by auto
  also have "... =
    (\<Prod>x<n. measure_pmf.prob (random_xor V)
             ({xor.
               satisfies_xor xor {x. \<omega> x = Some True} =
               the (\<alpha> x)}))"
    by (subst measure_Pi_pmf_PiE_dflt)
     (auto simp add: inj_vimage_image_eq)
  also have "... = (\<Prod>x<n. 1/2)"
    by (simp add: assms(1) satisfies_random_xor_parity)
  also have "... = 1/ 2 ^ n"
    by (simp add: power_one_over)
  finally show ?thesis by auto
qed

lemma PiE_dflt_inter:
  shows"PiE_dflt A dflt B \<inter> PiE_dflt A dflt B' =
    PiE_dflt A dflt (\<lambda>b. B b \<inter> B' b)"
  unfolding PiE_dflt_def
  by auto

lemma random_xors_xor_hash_pair:
  assumes V: "finite V"
  assumes \<alpha>: "dom \<alpha> = {..<n}"
  assumes \<alpha>': "dom \<alpha>' = {..<n}"
  assumes \<omega>: "dom \<omega> = V"
  assumes \<omega>': "dom \<omega>' = V"
  assumes neq: "\<omega> \<noteq> \<omega>'"
  shows "
  measure_pmf.prob (random_xors V n)
    {xors. xor_hash \<omega> xors = \<alpha> \<and> xor_hash \<omega>' xors = \<alpha>'} =
    1 / 4  ^ n"
proof -
  obtain y where "\<omega> y \<noteq> \<omega>' y"
    using neq
    by blast
  then have neq:"{x. \<omega> x = Some True} \<noteq> {x. \<omega>' x = Some True}"
    by (smt (verit, ccfv_threshold) assms(4) assms(5) domD domIff mem_Collect_eq)
  have "measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha> \<and> xor_hash \<omega>' xors = \<alpha>'} =
    measure_pmf.prob (random_xors V n)
      ({xors. xor_hash \<omega> xors = \<alpha>} \<inter>
        {xors. xor_hash \<omega>' xors = \<alpha>'})"
    by (simp add: Collect_conj_eq)
  also have "... =
    measure_pmf.prob
    (Pi_pmf {..<(n::nat)} None
      (\<lambda>_. map_pmf Some (random_xor V)))
    (PiE_dflt {..<n} None
      (\<lambda>i. Some ` {xor. satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> i)})
    \<inter>
    PiE_dflt {..<n} None
      (\<lambda>i. Some ` {xor. satisfies_xor xor {x. \<omega>' x = Some True} = the (\<alpha>' i)}))"
    unfolding random_xors_def xor_hash_eq_PiE_dflt[OF \<alpha>] xor_hash_eq_PiE_dflt[OF \<alpha>']
    by auto
  also have "... =
    measure_pmf.prob
    (Pi_pmf {..<(n::nat)} None
      (\<lambda>_. map_pmf Some (random_xor V)))
    (PiE_dflt {..<n} None
      (\<lambda>i.
      Some ` {xor.
        satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> i) \<and>
        satisfies_xor xor {x. \<omega>' x = Some True} = the (\<alpha>' i)}))"
    unfolding PiE_dflt_inter
    apply (subst image_Int[symmetric])
    by (auto simp add: Collect_conj_eq)

  also have "... =
    (\<Prod>x<n. measure_pmf.prob (random_xor V)
       ({xor.
         satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> x) \<and>
         satisfies_xor xor {x. \<omega>' x = Some True} = the (\<alpha>' x)}))"
    by (subst measure_Pi_pmf_PiE_dflt)
     (auto simp add: inj_vimage_image_eq)
  also have "... = (\<Prod>x<n. 1/4)"
    apply (subst pair_satisfies_random_xor_parity)
    using assms neq by auto
  also have "... = 1/ 4 ^ n"
    by (simp add: power_one_over)
  finally show ?thesis by auto
qed

lemma random_xors_xor_hash_three:
  assumes V: "finite V"
  assumes \<alpha>: "dom \<alpha> = {..<n}"
  assumes \<alpha>': "dom \<alpha>' = {..<n}"
  assumes \<alpha>'': "dom \<alpha>'' = {..<n}"
  assumes \<omega>: "dom \<omega> = V"
  assumes \<omega>': "dom \<omega>' = V"
  assumes \<omega>': "dom \<omega>'' = V"
  assumes neq: "\<omega> \<noteq> \<omega>'" "\<omega>' \<noteq> \<omega>''" "\<omega>'' \<noteq> \<omega>"
  shows "
  measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha>
      \<and> xor_hash \<omega>' xors = \<alpha>'
      \<and> xor_hash \<omega>'' xors = \<alpha>''} =
    1 / 8  ^ n"
proof -
  obtain x y z where "\<omega> x \<noteq> \<omega>' x" "\<omega>' y \<noteq> \<omega>'' y" "\<omega>'' z \<noteq> \<omega> z"
    using neq
    by blast
  then have neq:
    "{x. \<omega> x = Some True} \<noteq> {x. \<omega>' x = Some True}"
    "{x. \<omega>' x = Some True} \<noteq> {x. \<omega>'' x = Some True}"
    "{x. \<omega>'' x = Some True} \<noteq> {x. \<omega> x = Some True}"
    by (smt (verit, ccfv_threshold) assms domD domIff mem_Collect_eq)+
  have "measure_pmf.prob (random_xors V n)
    {xors.
      xor_hash \<omega> xors = \<alpha> \<and> xor_hash \<omega>' xors = \<alpha>' \<and> xor_hash \<omega>'' xors = \<alpha>''} =
    measure_pmf.prob (random_xors V n)
      ({xors. xor_hash \<omega> xors = \<alpha>} \<inter>
      {xors. xor_hash \<omega>' xors = \<alpha>'} \<inter>
      {xors. xor_hash \<omega>'' xors = \<alpha>''})"
    by (simp add: measure_pmf.measure_pmf_eq)
  moreover have "... =
    measure_pmf.prob
    (Pi_pmf {..<(n::nat)} None
      (\<lambda>_. map_pmf Some (random_xor V)))
    (PiE_dflt {..<n} None
      (\<lambda>i. Some ` {xor. satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> i)})
    \<inter>
    PiE_dflt {..<n} None
      (\<lambda>i. Some ` {xor. satisfies_xor xor {x. \<omega>' x = Some True} = the (\<alpha>' i)})
    \<inter>
    PiE_dflt {..<n} None
      (\<lambda>i. Some ` {xor. satisfies_xor xor {x. \<omega>'' x = Some True} = the (\<alpha>'' i)}))"
    unfolding random_xors_def xor_hash_eq_PiE_dflt[OF \<alpha>] xor_hash_eq_PiE_dflt[OF \<alpha>'] xor_hash_eq_PiE_dflt[OF \<alpha>'']
    by auto
  moreover have "... =
    measure_pmf.prob
    (Pi_pmf {..<(n::nat)} None
      (\<lambda>_. map_pmf Some (random_xor V)))
    (PiE_dflt {..<n} None
      (\<lambda>i.
      Some ` {xor.
        satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> i) \<and>
        satisfies_xor xor {x. \<omega>' x = Some True} = the (\<alpha>' i) \<and>
        satisfies_xor xor {x. \<omega>'' x = Some True} = the (\<alpha>'' i)}))
    "
    unfolding PiE_dflt_inter
    apply (subst image_Int[symmetric])
    subgoal by simp
    apply (intro arg_cong[where f="measure_pmf.prob
     (Pi_pmf {..<n} None
       (\<lambda>_. map_pmf Some (random_xor V)))"])
    apply (intro arg_cong[where f="PiE_dflt {..<n} None"])
    by auto

  moreover have "... =
    (\<Prod>x<n. measure_pmf.prob (random_xor V)
       ({xor.
         satisfies_xor xor {x. \<omega> x = Some True} = the (\<alpha> x) \<and>
         satisfies_xor xor {x. \<omega>' x = Some True} = the (\<alpha>' x)\<and>
         satisfies_xor xor {x. \<omega>'' x = Some True} = the (\<alpha>'' x)}))"
     apply (subst measure_Pi_pmf_PiE_dflt)
     by (auto simp add: inj_vimage_image_eq)
  moreover have "... = (\<Prod>x<n. 1/8)"
    apply (subst three_satisfies_random_xor_parity)
    subgoal using assms neq by clarsimp
    subgoal using assms neq by clarsimp
    subgoal using assms neq by clarsimp
    subgoal using assms neq by clarsimp
    subgoal using assms(5) by blast
    subgoal using assms(6) by blast
    subgoal using assms(7) by blast
    by auto
  moreover have "... = 1/ 8 ^ n"
    by (simp add: power_one_over)
  ultimately show ?thesis by auto
qed

end
