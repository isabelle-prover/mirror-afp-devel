section \<open>Algorithms for finding irreducible polynomials\<close>

theory Find_Irreducible_Poly
  imports
    Finite_Fields_More_PMF
    Finite_Fields_Poly_Factor_Ring_Code
    Rabin_Irreducibility_Test_Code
    Probabilistic_While.While_SPMF
    Card_Irreducible_Polynomials
    Executable_Randomized_Algorithms.Randomized_Algorithm
    "HOL-Library.Log_Nat"
begin

hide_const (open) Divisibility.prime
hide_const (open) Finite_Fields_Factorization_Ext.multiplicity
hide_const (open) Numeral_Type.mod_ring
hide_const (open) Polynomial.degree
hide_const (open) Polynomial.order

text \<open>Enumeration of the monic polynomials in lexicographic order.\<close>

definition enum_monic_poly :: "('a,'b) idx_ring_enum_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  where "enum_monic_poly A d i = 1\<^sub>C\<^bsub>A\<^esub>#[ idx_enum A (nth_digit i j (idx_size A)). j \<leftarrow> rev [0..<d]]"

lemma enum_monic_poly:
  assumes "field\<^sub>C R" "enum\<^sub>C R"
  shows "bij_betw (enum_monic_poly R d) {..<order (ring_of R)^d}
    {f. monic_poly (ring_of R) f \<and> degree f = d}"
proof -
  let ?f = " (\<lambda>x. 1\<^sub>C\<^bsub>R\<^esub> # map (\<lambda>j. idx_enum R (x j)) (rev [ 0..<d ] ))"
  let ?R = "ring_of R"

  note select_bij = enum_cD(3)[OF assms(2)]
  note fin_carr = enum_cD(1)[OF assms(2)]
  note fo = field_cD[OF assms(1)]

  interpret finite_field "ring_of R"
    using fin_carr assms(1) unfolding finite_field_def finite_field_axioms_def field\<^sub>C_def by auto

  have 1:"enum_monic_poly R d = ?f \<circ> (\<lambda>v. \<lambda>x\<in>{..<d}. nth_digit v x (order (ring_of R)))"
    unfolding enum_monic_poly_def comp_def enum_cD[OF assms(2)]
    by (intro ext arg_cong2[where f="(#)"] refl map_cong) auto

  have 2:"?f = (\<lambda>x. 1\<^sub>C\<^bsub>R\<^esub> # map x (rev [ 0..<d ] )) \<circ> (\<lambda>x. \<lambda>i\<in>{..<d}. idx_enum R ( x i))"
    unfolding comp_def by auto

  have 3: "(\<lambda>x. \<one>\<^bsub>ring_of R\<^esub>#map x (rev [0..<d])) = (\<lambda>x. \<one>\<^bsub>ring_of R\<^esub>#x) \<circ>rev\<circ> (\<lambda>x. map x [0..<d])"
    unfolding comp_def by (intro ext) (simp add:rev_map)

  have ap_bij: "bij_betw ((#) \<one>\<^bsub>?R\<^esub>) {x. set x\<subseteq>carrier ?R\<and>length x=d} {f. monic_poly ?R f \<and> degree f=d}"
    using list.collapse unfolding monic_poly_def univ_poly_carrier[symmetric] polynomial_def
    by (intro bij_betwI[where g="tl"]) (fastforce intro:in_set_tlD)+

  have rev_bij:
    "bij_betw rev {x. set x \<subseteq> carrier ?R \<and> length x = d} {x. set x \<subseteq> carrier ?R \<and> length x = d}"
    by (intro bij_betwI[where g="rev"]) auto

  have "bij_betw (\<lambda>x. \<one>\<^bsub>?R\<^esub>#map x (rev [ 0..<d] )) ({..<d} \<rightarrow>\<^sub>E carrier ?R) {f. monic_poly ?R f\<and>degree f=d}"
    unfolding 3 by (intro bij_betw_trans[OF lists_bij] bij_betw_trans[OF rev_bij] ap_bij)
  hence "bij_betw ?f ({..<d} \<rightarrow>\<^sub>E {..<order ?R}) {f. monic_poly ?R f \<and> degree f = d}"
    unfolding 2 by (intro bij_betw_trans[OF lift_bij_betw[OF select_bij]]) (simp add:fo)
  thus ?thesis
    unfolding 1 by (intro bij_betw_trans[OF nth_digit_bij])
qed

abbreviation tick_spmf :: "('a \<times> nat) spmf \<Rightarrow> ('a \<times> nat) spmf"
  where "tick_spmf \<equiv> map_spmf (\<lambda>(x,c). (x,c+1))"

text \<open>Finds an irreducible polynomial in the finite field @{term "mod_ring p"} with given degree n:\<close>

partial_function (spmf) sample_irreducible_poly :: "nat \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat) spmf"
  where
    "sample_irreducible_poly p n =
      do {
        k \<leftarrow> spmf_of_set {..<p^n};
        let poly = enum_monic_poly (mod_ring p) n k;
        if rabin_test (mod_ring p) poly
          then return_spmf (poly,1)
          else tick_spmf (sample_irreducible_poly p n)
      }"

text \<open>The following is a deterministic version. It returns the lexicographically minimal monic
irreducible polynomial. Note that contrary to the randomized algorithm, the run time of the
deterministic algorithm may be exponential (w.r.t. to the size of the field and degree of the
polynomial).\<close>

fun find_irreducible_poly :: "nat \<Rightarrow> nat \<Rightarrow> nat list"
  where "find_irreducible_poly p n = (let f = enum_monic_poly (mod_ring p) n in
    f (while ((\<lambda>k. \<not>rabin_test (mod_ring p) (f k))) (\<lambda>x. x + 1) 0))"

definition cost :: "('a \<times> nat) option \<Rightarrow> enat"
  where "cost x = (case x of None \<Rightarrow> \<infinity> | Some (_,r) \<Rightarrow> enat r)"

lemma cost_tick: "cost (map_option (\<lambda>(x, c). (x, Suc c)) c) = eSuc (cost c)"
  by (cases c) (auto simp:cost_def eSuc_enat)

context
  fixes n p :: nat
  assumes p_prime: "Factorial_Ring.prime p"
  assumes n_gt_0: "n > 0"
begin

private definition S where "S = {f. monic_poly (ring_of (mod_ring p)) f \<and> degree f = n }"
private definition T where "T = {f. monic_irreducible_poly (ring_of (mod_ring p)) f \<and> degree f = n}"

lemmas field_c = mod_ring_is_field_c[OF p_prime]
lemmas enum_c = mod_ring_is_enum_c[where n="p"]

interpretation finite_field "ring_of (mod_ring p)"
  unfolding finite_field_def finite_field_axioms_def
  by (intro mod_ring_is_field conjI mod_ring_finite p_prime)

private lemmas field_ops = field_cD[OF field_c]

private lemma S_fin: "finite S"
  unfolding S_def
  using enum_monic_poly[OF field_c enum_c, where d="n"]
    bij_betw_finite by auto

private lemma T_sub_S: "T \<subseteq> S"
  unfolding S_def T_def monic_irreducible_poly_def by auto

private lemma T_card_gt_0: "real (card T) > 0"
proof -
  have "0 < real (order (ring_of (mod_ring p))) ^ n / (2 * real n)"
    using n_gt_0 finite_field_min_order by (intro divide_pos_pos) (simp_all)
  also have "... \<le> real (card T)" unfolding T_def by (intro card_irred_gt_0 n_gt_0)
  finally show  "real (card T) > 0" by auto
qed

private lemma S_card_gt_0: "real (card S) > 0"
proof -
  have "0 < card T" using T_card_gt_0 by simp
  also have "... \<le> card S" by (intro card_mono T_sub_S S_fin)
  finally have "0 < card S" by simp
  thus ?thesis by simp
qed

private lemma S_ne: "S \<noteq> {}" using S_card_gt_0 by auto

private lemma sample_irreducible_poly_step_aux:
   "do {
      k \<leftarrow> spmf_of_set {..<p^n};
      let poly = enum_monic_poly (mod_ring p) n k;
      if rabin_test (mod_ring p) poly then return_spmf (poly,c) else x
    } =
    do {
      poly \<leftarrow> spmf_of_set S;
      if monic_irreducible_poly (ring_of (mod_ring p)) poly
          then return_spmf (poly,c)
          else x
    }"
  (is "?L = ?R")
proof -
  have "order (ring_of (mod_ring p)) = p"
    unfolding Finite_Fields_Mod_Ring_Code.mod_ring_def Coset.order_def ring_of_def by simp
  hence 0:"spmf_of_set S = map_spmf (enum_monic_poly (mod_ring p) n) (spmf_of_set {..<p^n})"
    using enum_monic_poly[OF field_c enum_c, where d="n"] unfolding bij_betw_def S_def
    by (subst map_spmf_of_set_inj_on) auto

  have "?L =do {f \<leftarrow> spmf_of_set S; if rabin_test (mod_ring p) f then return_spmf (f,c) else x}"
    unfolding 0 bind_map_spmf by (simp add:Let_def comp_def)
  also have "... = ?R"
    using set_spmf_of_set_finite[OF S_fin]
    by (intro bind_spmf_cong refl if_cong rabin_test field_c enum_c) (simp add:S_def)
  finally show ?thesis by simp
qed

private lemma sample_irreducible_poly_step:
  "sample_irreducible_poly p n =
      do {
        poly \<leftarrow> spmf_of_set S;
        if monic_irreducible_poly (ring_of (mod_ring p)) poly
          then return_spmf (poly,1)
          else tick_spmf (sample_irreducible_poly p n)
      }"
  by (subst sample_irreducible_poly.simps) (simp add:sample_irreducible_poly_step_aux)

private lemma sample_irreducible_poly_aux_1:
  "ord_spmf (=) (map_spmf fst (sample_irreducible_poly p n)) (spmf_of_set T)"
proof (induction rule:sample_irreducible_poly.fixp_induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 rec)
  let ?f = "monic_irreducible_poly (ring_of (mod_ring p))"

  have "real (card (S\<inter>-{x. ?f x})) = real (card (S - T))"
    unfolding S_def T_def by (intro arg_cong[where f="card"] arg_cong[where f="of_nat"]) (auto)
  also have "... = real (card S - card T)"
    by (intro arg_cong[where f="of_nat"] card_Diff_subset T_sub_S finite_subset[OF T_sub_S S_fin])
  also have "... = real (card S) - card T"
    by (intro of_nat_diff card_mono S_fin T_sub_S)
  finally have 0:"real (card (S\<inter>-{x. ?f x})) = real (card S) - card T" by simp

  have S_card_gt_0: "real (card S) > 0" using S_ne S_fin by auto

  have "do {f \<leftarrow> spmf_of_set S;if ?f f then return_spmf f else spmf_of_set T} = spmf_of_set T"
    (is "?L = ?R")
  proof (rule spmf_eqI)
    fix i
    have "spmf ?L i = spmf (pmf_of_set S \<bind>(\<lambda>x. if ?f x then return_spmf x else spmf_of_set T)) i"
      unfolding spmf_of_pmf_pmf_of_set[OF S_fin S_ne, symmetric] spmf_of_pmf_def
      by (simp add:bind_spmf_def bind_map_pmf)
    also have "... = (\<integral>x. (if ?f x then of_bool (x=i) else spmf (spmf_of_set T) i) \<partial>pmf_of_set S)"
      unfolding pmf_bind if_distrib if_distribR pmf_return_spmf indicator_def by (simp cong:if_cong)
    also have "... = (\<Sum>x \<in> S. (if ?f x then of_bool (x = i) else spmf (spmf_of_set T) i))/card S"
      by (subst integral_pmf_of_set[OF S_ne S_fin]) simp
    also have "... = (of_bool (i \<in> T) + spmf (spmf_of_set T) i*real (card (S\<inter>-{x. ?f x})))/card S"
      using S_fin S_ne
      by (subst sum.If_cases[OF S_fin]) (simp add:of_bool_def T_def monic_irreducible_poly_def S_def)
    also have "... = (of_bool (i \<in> T)*(1 + real (card (S\<inter>-{x. ?f x}))/real (card T)))/card S"
      unfolding spmf_of_set indicator_def by (simp add:algebra_simps)
    also have "... = (of_bool (i \<in> T)*(real (card S)/real (card T)))/card S"
      using T_card_gt_0 unfolding 0 by (simp add:field_simps)
    also have "... = of_bool (i \<in> T)/real (card T)"
      using S_card_gt_0 by (simp add:field_simps)
    also have "... = spmf ?R i"
      unfolding spmf_of_set by simp
    finally show "spmf ?L i = spmf ?R i"
      by simp
  qed
  hence "ord_spmf (=)
    (spmf_of_set S \<bind> (\<lambda>x. if ?f x then return_spmf x else spmf_of_set T)) (spmf_of_set T)"
    by simp
  moreover have "ord_spmf (=)
    (do { poly \<leftarrow> spmf_of_set S; if ?f poly then return_spmf poly else map_spmf fst (rec p n)})
    (do { poly \<leftarrow> spmf_of_set S; if ?f poly then return_spmf poly else spmf_of_set T})"
    using 3 by (intro bind_spmf_mono') simp_all
  ultimately have "ord_spmf (=) (spmf_of_set S \<bind>
    (\<lambda>x. if ?f x then return_spmf x else map_spmf fst (rec p n))) (spmf_of_set T)"
    using spmf.leq_trans by force
  thus ?case unfolding sample_irreducible_poly_step_aux map_spmf_bind_spmf
    by (simp add:comp_def if_distribR if_distrib spmf.map_comp case_prod_beta cong:if_cong)
qed

lemma cost_sample_irreducible_poly:
  "(\<integral>\<^sup>+x. cost x \<partial>sample_irreducible_poly p n) \<le> 2*real n" (is "?L \<le> ?R")
proof -
  let ?f = "monic_irreducible_poly (ring_of (mod_ring p))"
  let ?a = "(\<lambda>t. measure (sample_irreducible_poly p n) {\<omega>. enat t < cost \<omega>})"
  let ?b = "(\<lambda>t. measure (sample_irreducible_poly p n) {\<omega>. enat t \<ge> cost \<omega>})"

  define \<alpha> where "\<alpha> = measure (pmf_of_set S) {x. ?f x}"
  have \<alpha>_le_1: "\<alpha> \<le> 1" unfolding \<alpha>_def by simp

  have "1 / (2* real n) = (card S / (2 * real n)) / card S"
    using S_card_gt_0 by (simp add:algebra_simps)
  also have "... = (real (order (ring_of (mod_ring p)))^n / (2 * real n)) / card S"
    unfolding S_def bij_betw_same_card[OF enum_monic_poly[OF field_c enum_c, where d="n"],symmetric]
    by simp
  also have "... \<le> card T / card S"
    unfolding T_def  by (intro divide_right_mono card_irred_gt_0 n_gt_0) auto
  also have "... = \<alpha>"
    unfolding \<alpha>_def measure_pmf_of_set[OF S_ne S_fin]
    by (intro arg_cong2[where f="(/)"] refl arg_cong[where f="of_nat"]  arg_cong[where f="card"])
     (auto simp: S_def T_def monic_irreducible_poly_def)
  finally have \<alpha>_lb: "1/ (2*real n) \<le> \<alpha>"
    by simp
  have "0 < 1/ (2*real n)" using n_gt_0 by simp
  also have "... \<le> \<alpha>" using \<alpha>_lb by simp
  finally have \<alpha>_gt_0: "\<alpha> > 0" by simp

  have a_step_aux: "norm (a * b) \<le> 1" if "norm a \<le> 1" "norm b \<le> 1" for a b :: real
    using that by (simp add:abs_mult mult_le_one)

  have b_eval: "?b t = (\<integral>x. (if ?f x then of_bool(t \<ge> 1) else
    measure (sample_irreducible_poly p n) {\<omega>. enat t \<ge> eSuc (cost \<omega>)}) \<partial>pmf_of_set S)"
    (is "?L1 = ?R1") for t
  proof -
    have "?b t = measure (bind_spmf (spmf_of_set S) (\<lambda>x. if ?f x then return_spmf (x,1) else
        tick_spmf (sample_irreducible_poly p n))) {\<omega>. enat t \<ge> cost \<omega>}"
      by (subst sample_irreducible_poly_step) simp
    also have "... = measure (bind_pmf (pmf_of_set S) (\<lambda>x. if ?f x then return_spmf (x,1) else
        tick_spmf (sample_irreducible_poly p n))) {\<omega>. enat t \<ge> cost \<omega>}"
      unfolding spmf_of_pmf_pmf_of_set[OF S_fin S_ne, symmetric]
      by (simp add:spmf_of_pmf_def bind_map_pmf bind_spmf_def)
    also have "... = (\<integral>x. (if ?f x then of_bool(t \<ge> 1) else
      measure (tick_spmf (sample_irreducible_poly p n)) {\<omega>. enat t \<ge> cost \<omega>})  \<partial>pmf_of_set S)"
      unfolding measure_bind_pmf if_distrib if_distribR emeasure_return_pmf
      by (simp add:indicator_def cost_def comp_def cong:if_cong)
    also have "... = ?R1"
      unfolding measure_map_pmf vimage_def
      by (intro arg_cong2[where f="integral\<^sup>L"] refl ext if_cong arg_cong2[where f="measure"])
       (auto simp add:vimage_def cost_tick eSuc_enat[symmetric])
    finally show ?thesis by simp
  qed

  have b_eval_2: "?b t = 1 - (1-\<alpha>)^t" for t
  proof (induction t)
    case 0
    have "?b 0 = 0" unfolding b_eval by (simp add:enat_0 cong:if_cong )
    thus ?case by simp
  next
    case (Suc t)
    have "?b (Suc t) = (\<integral>x. (if ?f x then 1 else  ?b t) \<partial>pmf_of_set S)"
      unfolding b_eval[of "Suc t"]
      by (intro arg_cong2[where f="integral\<^sup>L"] if_cong arg_cong2[where f="measure"])
       (auto simp add: eSuc_enat[symmetric])
    also have "... = (\<integral>x. indicator {x. ?f x} x + ?b t * indicator {x. \<not>?f x} x \<partial>pmf_of_set S)"
      by (intro Bochner_Integration.integral_cong) (auto simp:algebra_simps)
    also have "... = (\<integral>x. indicator {x. ?f x} x \<partial>pmf_of_set S) +
      (\<integral>x. ?b t * indicator {x. \<not>?f x} x \<partial>pmf_of_set S)"
      by (intro Bochner_Integration.integral_add measure_pmf.integrable_const_bound[where B="1"]
          AE_pmfI a_step_aux) auto
    also have "... = \<alpha> + ?b t * measure (pmf_of_set S) {x. \<not>?f x}" unfolding \<alpha>_def by simp
    also have "... = \<alpha> + (1-\<alpha>) * ?b t"
      unfolding \<alpha>_def
      by (subst measure_pmf.prob_compl[symmetric]) (auto simp:Compl_eq_Diff_UNIV Collect_neg_eq)
    also have "... = 1 - (1-\<alpha>)^Suc t"
      unfolding Suc by (simp add:algebra_simps)
    finally show ?case by simp
  qed

  hence a_eval: "?a t = (1-\<alpha>)^t" for t
  proof -
    have "?a t = 1 - ?b t"
      by (simp add: measure_pmf.prob_compl[symmetric] Compl_eq_Diff_UNIV[symmetric]
          Collect_neg_eq[symmetric] not_le)
    also have "... =  (1-\<alpha>)^t"
      unfolding b_eval_2 by simp
    finally show ?thesis by simp
  qed

  have "?L = (\<Sum>t. emeasure (sample_irreducible_poly p n) {\<omega>. enat t < cost \<omega>})"
    by (subst nn_integral_enat_function) simp_all
  also have "... = (\<Sum>t. ennreal (?a t))"
    unfolding measure_pmf.emeasure_eq_measure by simp
  also have "... = (\<Sum>t. ennreal ((1-\<alpha>)^t))"
    unfolding a_eval by (intro arg_cong[where f="suminf"] ext) (simp add: \<alpha>_def ennreal_mult')
  also have "... = ennreal (1 / (1-(1-\<alpha>)))"
    using \<alpha>_le_1 \<alpha>_gt_0
    by (intro arg_cong2[where f="(*)"] refl suminf_ennreal_eq geometric_sums) auto
  also have "... = ennreal (1 / \<alpha>)" using \<alpha>_le_1 \<alpha>_gt_0 by auto
  also have "... \<le> ?R"
    using \<alpha>_lb n_gt_0 \<alpha>_gt_0 by (intro ennreal_leI) (simp add:field_simps)
  finally show ?thesis by simp
qed

private lemma weight_sample_irreducible_poly:
  "weight_spmf (sample_irreducible_poly p n) = 1" (is "?L = ?R")
proof (rule ccontr)
  assume "?L \<noteq> 1"
  hence "?L < 1" using less_eq_real_def weight_spmf_le_1 by blast
  hence "(\<infinity>::ennreal) = \<infinity> * ennreal (1-?L)" by simp
  also have "... = \<infinity> * ennreal (pmf (sample_irreducible_poly p n) None)"
    unfolding pmf_None_eq_weight_spmf[symmetric] by simp
  also have "... = (\<integral>\<^sup>+x. \<infinity> * indicator {None} x  \<partial>sample_irreducible_poly p n)"
    by (simp add:emeasure_pmf_single)
  also have "... \<le> (\<integral>\<^sup>+x. cost x \<partial>sample_irreducible_poly p n)"
    unfolding cost_def by (intro nn_integral_mono) (auto simp:indicator_def)
  also have "... \<le> 2*real n" by (intro cost_sample_irreducible_poly)
  finally have "(\<infinity>::ennreal) \<le> 2 * real n" by simp
  thus "False" using linorder_not_le by fastforce
qed

lemma sample_irreducible_poly_result:
  "map_spmf fst (sample_irreducible_poly p n) =
    spmf_of_set {f. monic_irreducible_poly (ring_of (mod_ring p)) f \<and> degree f = n}" (is "?L = ?R")
proof -
  have "?L = spmf_of_set T" using weight_sample_irreducible_poly
    by (intro eq_iff_ord_spmf sample_irreducible_poly_aux_1) (auto intro:weight_spmf_le_1)
  thus ?thesis  unfolding T_def by simp
qed

lemma find_irreducible_poly_result:
  defines "res \<equiv> find_irreducible_poly p n"
  shows "monic_irreducible_poly (ring_of (mod_ring p)) res" "degree res = n"
proof -
  let ?f = "enum_monic_poly (mod_ring p) n"

  have ex:"\<exists>k. ?f k \<in> T \<and> k < order (ring_of (mod_ring p))^n"
  proof (rule ccontr)
    assume "\<nexists>k. ?f k \<in> T \<and> k < order (ring_of (mod_ring p)) ^ n"
    hence "?f ` {..<order (ring_of (mod_ring p)) ^ n} \<inter> T = {}" by auto
    hence "S \<inter> T = {}"
      unfolding S_def using bij_betw_imp_surj_on[OF enum_monic_poly[OF field_c enum_c]] by auto
    hence "T = {}" using T_sub_S by auto
    thus "False" using T_card_gt_0 by simp
  qed

  then obtain k :: nat where k_def: "?f k \<in> T" "\<forall>j<k. ?f j \<notin> T"
    using exists_least_iff[where P="\<lambda>x. ?f x \<in> T"] by auto

  have k_ub: "k < order (ring_of (mod_ring p))^n"
    using ex k_def(2) by (meson dual_order.strict_trans1 not_less)

  have a: "monic_irreducible_poly (ring_of (mod_ring p)) (?f k)"
    using k_def(1) unfolding T_def by simp
  have b: "monic_poly (ring_of (mod_ring p)) (?f j)" "degree (?f j) = n" if "j \<le> k" for j
  proof -
    have "j < order (ring_of (mod_ring p)) ^n" using k_ub that by simp
    hence "?f j \<in> S" unfolding S_def using bij_betw_apply[OF enum_monic_poly[OF field_c enum_c]] by auto
    thus "monic_poly (ring_of (mod_ring p)) (?f j)" "degree (?f j) = n" unfolding S_def by auto
  qed

  have c: "\<not>monic_irreducible_poly (ring_of (mod_ring p)) (?f j)"  if " j < k" for j
    using b[of "j"] that k_def(2) unfolding T_def by auto

  have 2: "while ((\<lambda>k. \<not>rabin_test (mod_ring p) (?f k))) (\<lambda>x. x + 1) (k-j) = k" if "j \<le> k" for j
  using that proof (induction j)
    case 0
    have "rabin_test (mod_ring p) (?f k)" by (intro iffD2[OF rabin_test] a b field_c enum_c) auto
    thus ?case by (subst while_unfold) simp
  next
    case (Suc j)
    hence "\<not>rabin_test (mod_ring p) (?f (k-Suc j))"
      using b c by (subst rabin_test[OF field_c enum_c]) auto
    moreover have "Suc (Suc (k - Suc j)) = Suc (k-j)" using Suc by simp
    ultimately show ?case using Suc(1) by (subst while_unfold) simp
  qed

  have 3:"while ((\<lambda>k. \<not>rabin_test (mod_ring p) (?f k))) (\<lambda>x. x + 1) 0 = k"
    using 2[of "k"] by simp

  have "?f k \<in> T" using a b unfolding T_def by auto
  hence "res \<in> T" unfolding res_def find_irreducible_poly.simps Let_def 3 by simp
  thus "monic_irreducible_poly (ring_of (mod_ring p)) res" "degree res = n" unfolding T_def by auto
qed

lemma monic_irred_poly_set_nonempty_finite:
  "{f. monic_irreducible_poly (ring_of (mod_ring p)) f \<and> degree f = n} \<noteq> {}" (is "?R1")
  "finite {f. monic_irreducible_poly (ring_of (mod_ring p)) f \<and> degree f = n}" (is "?R2")
proof -
  have "card T > 0" using T_card_gt_0 by auto
  hence "T \<noteq> {}" "finite T" using card_ge_0_finite by auto
  thus ?R1 ?R2 unfolding T_def by auto
qed

end

text \<open>Returns @{term "m"} @{term "e"} such that @{term "n = m^e"}, where @{term "e"} is maximal.\<close>

definition split_power :: "nat \<Rightarrow> nat \<times> nat"
  where "split_power n = (
    let e = last (filter (\<lambda>x. is_nth_power_nat x n) (1#[2..<floorlog 2 n]))
    in (nth_root_nat e n, e))"

lemma split_power_result:
  assumes "(x,e) = split_power n"
  shows "n = x^e" "\<And>k. n > 1 \<Longrightarrow> k>e \<Longrightarrow> \<not>is_nth_power k n"
proof -
  define es where "es = filter (\<lambda>x. is_nth_power_nat x n) (1#[2..<floorlog 2 n])"
  define m where "m = max 2 (floorlog 2 n)"

  have 0: "x < m" if that0: "is_nth_power_nat x n" "n > 1" for x
  proof (rule ccontr)
    assume a:"\<not>(x < m)"
    obtain y where n_def:"n = y^x" using that0 is_nth_power_def is_nth_power_nat_def by auto
    have "y \<noteq> 0" using that(2) unfolding n_def
      by (metis (mono_tags) nat_power_eq_Suc_0_iff not_less0 power_0_left power_inject_exp)
    moreover have "y \<noteq> 1" using that(2) unfolding n_def by auto
    ultimately have y_ge_2: "y \<ge> 2" by simp
    have "n < 2^floorlog 2 n" using that floorlog_bounds by simp
    also have "... \<le> 2^x" using a unfolding m_def by (intro power_increasing) auto
    also have "... \<le> y^x" using y_ge_2 by (intro power_mono) auto
    also have "... = n" using n_def by auto
    finally show "False" by simp
  qed

  have 1: "m = 2" if "\<not>(n > 1)"
  proof -
    have "floorlog 2 n \<le> 2" using that by (intro floorlog_leI) auto
    thus ?thesis unfolding m_def by auto
  qed

  have 2: "n = 1" if "is_nth_power_nat 0 n" using that by (simp add: is_nth_power_nat_code)

  have "set es = {x \<in> insert 1 {2..<floorlog 2 n}. is_nth_power_nat x n}" unfolding es_def by auto
  also have "... = {x. x \<noteq> 0 \<and> x < m \<and> is_nth_power_nat x n}" unfolding m_def by auto
  also have "... = {x. is_nth_power_nat x n \<and> (n > 1 \<or> x = 1)}"
    using 0 1 2 zero_neq_one by (intro Collect_cong iffI conjI) fastforce+
  finally have set_es: "set es = {x. is_nth_power_nat x n \<and> (n > 1 \<or> x = 1)}" by simp

  have "is_nth_power_nat 1 n" unfolding is_nth_power_nat_def by simp
  hence es_ne: "es \<noteq> []" unfolding es_def by auto

  have sorted: "sorted es" unfolding es_def by (intro sorted_wrt_filter) simp

  have e_def: "e = last es" and x_def: "x = nth_root_nat e n"
    using assms unfolding es_def split_power_def by (simp_all add:Let_def)

  hence e_in_set_es: "e \<in> set es" unfolding e_def using es_ne by (intro last_in_set) auto

  have e_max: "x \<le> e" if that1:"x \<in> set es" for x
  proof -
    obtain k where "k < length es" "x = es ! k" using that1 by (metis in_set_conv_nth)
    moreover have "e = es ! (length es -1)" unfolding e_def using es_ne last_conv_nth by auto
    ultimately show ?thesis using sorted_nth_mono[OF sorted] es_ne by simp
  qed
  have 3:"is_nth_power_nat e n \<and> (1 < n \<or> e = 1)" using e_in_set_es unfolding set_es by simp
  hence "e > 0" using 2 zero_neq_one by fast
  thus "n = x^e" using 3 unfolding x_def using nth_root_nat_nth_power
    by (metis is_nth_power_nat_code nth_root_nat_naive_code power_eq_0_iff)
  show "\<not>is_nth_power k n" if "n > 1" "k > e" for k
  proof (rule ccontr)
    assume "\<not>(\<not>is_nth_power k n)"
    hence "k \<in> set es" using that unfolding set_es is_nth_power_nat_def by auto
    hence "k \<le> e" using e_max by auto
    thus "False" using that(2) by auto
  qed
qed

definition not_perfect_power :: "nat \<Rightarrow> bool"
  where "not_perfect_power n = (n > 1 \<and> (\<forall>x k. n = x ^ k \<longrightarrow> k = 1))"

lemma is_nth_power_from_multiplicities:
  assumes "n > (0::nat)"
  assumes "\<And>p. Factorial_Ring.prime p \<Longrightarrow> k dvd (multiplicity p n)"
  shows "is_nth_power k n"
proof -
  have "n = (\<Prod>p \<in> prime_factors n. p^multiplicity p n)" using assms(1)
    by (simp add: prod_prime_factors)
  also have "... = (\<Prod>p \<in> prime_factors n. p^((multiplicity p n div k)*k))"
    by (intro prod.cong arg_cong2[where f="power"] dvd_div_mult_self[symmetric] refl assms(2)) auto
  also have "... = (\<Prod>p \<in> prime_factors n. p^(multiplicity p n div k))^k"
    unfolding power_mult prod_power_distrib[symmetric] by simp
  finally have "n = (\<Prod>p \<in> prime_factors n. p^(multiplicity p n div k))^k" by simp
  thus ?thesis by (intro is_nth_powerI) simp
qed

lemma power_inj_aux:
  assumes "not_perfect_power a" "not_perfect_power b"
  assumes "n > 0" "m > n"
  assumes "a ^ n = b ^ m"
  shows "False"
proof -
  define s where "s = gcd n m"
  define u where "u = n div gcd n m"
  define t where "t = m div gcd n m"

  have a_nz: "a \<noteq> 0" and b_nz: "b \<noteq> 0" using assms(1,2) unfolding not_perfect_power_def by auto

  have "gcd n m \<noteq> 0" using assms (3,4) by simp

  then obtain t u where n_def: "n = t * s" and m_def: "m = u * s" and cp: "coprime t u"
    using gcd_coprime_exists unfolding s_def t_def u_def by blast

  have s_gt_0: "s > 0" and t_gt_0: "t > 0" and u_gt_t: "u > t"
    using assms(3,4) unfolding n_def m_def by auto

  have "(a ^ t) ^ s = (b ^ u) ^ s" using assms(5) unfolding n_def m_def power_mult by simp
  hence 0: "a^t = b^u" using s_gt_0 by (metis nth_root_nat_nth_power)

  have "u dvd multiplicity p a" if "Factorial_Ring.prime p" for p
  proof -
    have "prime_elem p" using that by simp
    hence "t * multiplicity p a = u * multiplicity p b"
      using 0 a_nz b_nz by (subst (1 2) prime_elem_multiplicity_power_distrib[symmetric]) auto
    hence "u dvd t * multiplicity p a" by simp
    thus ?thesis using cp coprime_commute coprime_dvd_mult_right_iff by blast
  qed

  hence "is_nth_power u a" using a_nz by (intro is_nth_power_from_multiplicities) auto
  moreover have "u > 1" using u_gt_t t_gt_0 by auto
  ultimately show "False" using assms(1) unfolding not_perfect_power_def is_nth_power_def by auto
qed

text \<open>Generalization of @{thm [source] prime_power_inj'}\<close>

lemma power_inj:
  assumes "not_perfect_power a" "not_perfect_power b"
  assumes "n > 0" "m > 0"
  assumes "a ^ n = b ^ m"
  shows "a = b \<and> n = m"
proof -
  consider (a) "n < m" | (b) "m < n" | (c) "n = m" by linarith
  thus ?thesis
  proof (cases)
    case a thus ?thesis using assms power_inj_aux by auto
  next
    case b thus ?thesis using assms power_inj_aux[OF assms(2,1,4) b] by auto
  next
    case c thus ?thesis using assms by (simp add: power_eq_iff_eq_base)
  qed
qed

lemma split_power_base_not_perfect:
  assumes "n > 1"
  shows "not_perfect_power (fst (split_power n))"
proof (rule ccontr)
  obtain b e where be_def: "(b,e) = split_power n" by (metis surj_pair)
  have n_def:"n = b ^ e" and e_max: "\<And>k. e < k \<Longrightarrow> \<not> is_nth_power k n"
    using assms split_power_result[OF be_def] by auto

  have e_gt_0: "e > 0" using assms unfolding n_def by (cases e) auto

  assume "\<not>not_perfect_power (fst (split_power n))"
  hence "\<not>not_perfect_power b" unfolding be_def[symmetric] by simp
  moreover have b_gt_1: "b > 1" using assms unfolding n_def
    by (metis less_one nat_neq_iff nat_power_eq_Suc_0_iff power_0_left)
  ultimately obtain k b' where "k \<noteq> 1" and b_def: "b = b'^k"
    unfolding not_perfect_power_def by auto
  hence k_gt_1: "k > 1" using b_gt_1 nat_neq_iff by force
  have "n = b'^(k*e)" unfolding power_mult n_def b_def by auto
  moreover have "k*e > e" using k_gt_1 e_gt_0 by simp
  hence "\<not>is_nth_power (k*e) n" using e_max by auto
  ultimately show "False" unfolding is_nth_power_def by auto
qed

lemma prime_not_perfect:
  assumes "Factorial_Ring.prime p"
  shows "not_perfect_power p"
proof -
  have "k=1" if "p = x^k" for x k using assms unfolding that by (simp add:prime_power_iff)
  thus ?thesis using prime_gt_1_nat[OF assms] unfolding not_perfect_power_def by auto
qed

lemma split_power_prime:
  assumes "Factorial_Ring.prime p" "n > 0"
  shows "split_power (p^n) = (p,n)"
proof -
  obtain x e where xe:"(x,e) = split_power (p^n)" by (metis surj_pair)

  have "1 < p^1" using prime_gt_1_nat[OF assms(1)] by simp
  also have "... \<le> p^n" using assms(2) prime_gt_0_nat[OF assms(1)] by (intro power_increasing) auto
  finally have 0:"p^n > 1" by simp

  have "not_perfect_power x"
    using split_power_base_not_perfect[OF 0] unfolding xe[symmetric] by simp
  moreover have "not_perfect_power p" by (rule prime_not_perfect[OF assms(1)])
  moreover have 1:"p^n = x^e" using split_power_result[OF xe] by simp
  moreover have "e > 0" using 0 1 by (cases e) auto
  ultimately have "p=x \<and> n = e" by (intro power_inj assms(2))
  thus ?thesis using xe by simp
qed

definition "is_prime_power n = (\<exists>p k. Factorial_Ring.prime p \<and> k > 0 \<and> n = p^k)"

lemma is_prime_powerI:
  assumes "prime p" "k > 0"
  shows "is_prime_power (p ^ k)"
  unfolding is_prime_power_def using assms by auto

definition GF where
  "GF n = (
    let (p,k) = split_power n;
        f = find_irreducible_poly p k
     in poly_mod_ring (mod_ring p) f)"


definition GF\<^sub>R where
  "GF\<^sub>R n =
    do {
      let (p,k) = split_power n;
      f \<leftarrow> sample_irreducible_poly p k;
      return_spmf (poly_mod_ring (mod_ring p) (fst f))
    }"

lemma GF_in_GF_R:
  assumes "is_prime_power n"
  shows "GF n \<in> set_spmf (GF\<^sub>R n)"
proof-
  obtain p k where n_def: "n = p^k" and p_prime: "prime p" and k_gt_0: "k > 0"
    using assms unfolding is_prime_power_def by blast
  have pk_def: "(p,k) = split_power n"
    unfolding n_def using split_power_prime[OF p_prime k_gt_0] by auto
  let ?S = "{f. monic_irreducible_poly (ring_of (mod_ring p)) f \<and> degree f = k}"

  have S_fin: "finite ?S" by (intro monic_irred_poly_set_nonempty_finite p_prime k_gt_0)

  have "find_irreducible_poly p k \<in> ?S"
    using find_irreducible_poly_result[OF p_prime k_gt_0] by auto
  also have "... = set_spmf (map_spmf fst (sample_irreducible_poly p k))"
    unfolding sample_irreducible_poly_result[OF p_prime k_gt_0] set_spmf_of_set_finite[OF S_fin]
    by simp
  finally have 0: "find_irreducible_poly p k \<in> set_spmf(map_spmf fst (sample_irreducible_poly p k))"
    by simp

  have "GF n = poly_mod_ring (mod_ring p) (find_irreducible_poly p k)"
    unfolding GF_def pk_def[symmetric] by (simp del:find_irreducible_poly.simps)
  also have "... \<in> set_spmf (map_spmf fst (sample_irreducible_poly p k)) \<bind> (\<lambda>x. {poly_mod_ring (mod_ring p) x})"
    using 0 by force
  also have "... = set_spmf (GF\<^sub>R n)"
    unfolding GF\<^sub>R_def pk_def[symmetric] by (simp add:set_bind_spmf comp_def bind_image)
  finally show ?thesis by simp
qed

lemma galois_field_random_1:
  assumes "is_prime_power n"
  shows "\<And>\<omega>. \<omega> \<in> set_spmf (GF\<^sub>R n) \<Longrightarrow> enum\<^sub>C \<omega> \<and> field\<^sub>C \<omega> \<and> order (ring_of \<omega>) = n"
    and "lossless_spmf (GF\<^sub>R n)"
proof -
  let ?pred = "\<lambda>\<omega>. enum\<^sub>C \<omega> \<and> field\<^sub>C \<omega> \<and> order (ring_of \<omega>) = n"

  obtain p k where n_def: "n = p^k" and p_prime: "prime p" and k_gt_0: "k > 0"
    using assms unfolding is_prime_power_def by blast
  let ?r = "(\<lambda>f. poly_mod_ring (mod_ring p) f)"
  let ?S = "{f. monic_irreducible_poly (ring_of (mod_ring p)) f \<and> degree f = k}"

  have fc: "field\<^sub>C (mod_ring p)" by (intro mod_ring_is_field_c p_prime)
  have ec: "enum\<^sub>C (mod_ring p)" by (intro mod_ring_is_enum_c)

  have S_fin: "finite ?S" by (intro monic_irred_poly_set_nonempty_finite p_prime k_gt_0)
  have S_ne: "?S \<noteq> {}" by (intro monic_irred_poly_set_nonempty_finite p_prime k_gt_0)

  have pk_def: "(p,k) = split_power n"
    unfolding n_def using split_power_prime[OF p_prime k_gt_0] by auto

  have cond: "?pred (?r x)" if "x \<in> ?S" for x
  proof -
    have "order (ring_of (poly_mod_ring (mod_ring p) x)) = idx_size (poly_mod_ring (mod_ring p) x)"
      using enum_cD[OF enum_c_poly_mod_ring[OF ec field_c_imp_ring[OF fc]]] by simp
    also have "... = p^(degree x)"
      by (simp add:poly_mod_ring_def Finite_Fields_Mod_Ring_Code.mod_ring_def)
    also have "... = n" unfolding n_def using that by simp
    finally have "order (ring_of (poly_mod_ring (mod_ring p) x)) = n" by simp

    thus ?thesis using that
      by (intro conjI enum_c_poly_mod_ring field_c_poly_mod_ring ec field_c_imp_ring fc) auto
  qed

  have "GF\<^sub>R n = bind_spmf (map_spmf fst (sample_irreducible_poly p k)) (\<lambda>x. return_spmf (?r x))"
    unfolding GF\<^sub>R_def pk_def[symmetric] map_spmf_conv_bind_spmf by simp
  also have "... = spmf_of_set ?S \<bind> (\<lambda>f. return_spmf ((?r f)))"
    unfolding sample_irreducible_poly_result[OF p_prime k_gt_0] by (simp)
  also have "... = pmf_of_set ?S \<bind> (\<lambda>f. return_spmf (?r f))"
    unfolding spmf_of_pmf_pmf_of_set[OF S_fin S_ne, symmetric] spmf_of_pmf_def
    by (simp add:bind_spmf_def bind_map_pmf)
  finally have 0:"GF\<^sub>R n = map_pmf (Some \<circ> ?r) (pmf_of_set ?S) " by (simp add:comp_def map_pmf_def)

  show "enum\<^sub>C \<omega> \<and> field\<^sub>C \<omega> \<and> order (ring_of \<omega>) = n" if "\<omega> \<in> set_spmf (GF\<^sub>R n)" for \<omega>
  proof -
    have "Some \<omega> \<in> set_pmf (GF\<^sub>R n)" unfolding in_set_spmf[symmetric] by (rule that)
    also have "... = (Some \<circ> ?r) ` ?S" unfolding 0 set_map_pmf set_pmf_of_set[OF S_ne S_fin] by simp
    finally have "Some \<omega> \<in> (Some \<circ> ?r) ` ?S" by simp
    hence "\<omega> \<in> ?r ` ?S" by auto
    then obtain x where x:"x \<in> ?S" and \<omega>_def:"\<omega> = ?r x" by auto
    show ?thesis unfolding \<omega>_def by (intro cond x)
  qed

  have "None \<notin> set_pmf(GF\<^sub>R n)" unfolding 0 set_map_pmf set_pmf_of_set[OF S_ne S_fin] by auto
  thus "lossless_spmf (GF\<^sub>R n)" using lossless_iff_set_pmf_None by blast
qed

lemma galois_field:
  assumes "is_prime_power n"
  shows "enum\<^sub>C (GF n)" "field\<^sub>C (GF n)" "order (ring_of (GF n)) = n"
  using galois_field_random_1(1)[OF assms(1) GF_in_GF_R[OF assms(1)]] by auto

lemma lossless_imp_spmf_of_pmf:
  assumes "lossless_spmf M"
  shows "spmf_of_pmf (map_pmf the M) = M"
proof -
  have "spmf_of_pmf (map_pmf the M) = map_pmf (Some \<circ> the) M"
    unfolding spmf_of_pmf_def by (simp add: pmf.map_comp)
  also have "... = map_pmf id M"
    using assms unfolding lossless_iff_set_pmf_None
    by (intro map_pmf_cong refl) (metis id_apply o_apply option.collapse)
  also have "... = M" by simp
  finally show ?thesis by simp
qed

lemma galois_field_random_2:
  assumes "is_prime_power n"
  shows "map_spmf (\<lambda>\<omega>. enum\<^sub>C \<omega> \<and> field\<^sub>C \<omega> \<and> order (ring_of \<omega>) = n) (GF\<^sub>R n) = return_spmf True"
    (is "?L = _")
proof -
  have "?L = map_spmf (\<lambda>\<omega>. True) (GF\<^sub>R n)"
    using galois_field_random_1[OF assms] by (intro map_spmf_cong refl) auto
  also have "... = map_pmf (\<lambda>\<omega>. Some True) (GF\<^sub>R n)"
    by (subst lossless_imp_spmf_of_pmf[OF galois_field_random_1(2)[OF assms],symmetric]) simp
  also have "... = return_spmf True" unfolding map_pmf_def by simp
  finally show ?thesis by simp
qed

lemma bind_galois_field_cong:
  assumes "is_prime_power n"
  assumes "\<And>\<omega>. enum\<^sub>C \<omega> \<Longrightarrow> field\<^sub>C \<omega> \<Longrightarrow> order (ring_of \<omega>) = n \<Longrightarrow> f \<omega> = g \<omega>"
  shows "bind_spmf (GF\<^sub>R n) f = bind_spmf (GF\<^sub>R n) g"
  using galois_field_random_1(1)[OF assms(1)]
  by (intro bind_spmf_cong refl assms(2)) auto

end