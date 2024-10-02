section \<open>K-Independent Hash Families as Pseudorandom Objects\<close>

theory Pseudorandom_Objects_Hash_Families
  imports
    Pseudorandom_Objects
    Finite_Fields.Find_Irreducible_Poly
    Carter_Wegman_Hash_Family
    Universal_Hash_Families_More_Product_PMF
begin

hide_const (open) Numeral_Type.mod_ring
hide_const (open) Divisibility.prime
hide_const (open) Isolated.discrete

definition hash_space' ::
  "('a,'b) idx_ring_enum_scheme \<Rightarrow> nat \<Rightarrow> ('c,'d) pseudorandom_object_scheme
  \<Rightarrow> (nat \<Rightarrow> 'c) pseudorandom_object"
  where "hash_space' R k S = (
    \<lparr>
      pro_last = idx_size R ^k-1,
      pro_select = (\<lambda>x i.
        pro_select S
        (idx_enum_inv R (poly_eval R (poly_enum R k x) (idx_enum R i)) mod pro_size S))
    \<rparr>)"

lemma hash_prob_single':
  assumes "field F" "finite (carrier F)"
  assumes "x \<in> carrier F"
  assumes "1 \<le> n"
  shows "measure (pmf_of_set (bounded_degree_polynomials F n)) {\<omega>. ring.hash F x \<omega> = y} =
    of_bool (y\<in> carrier F)/(real (card (carrier F)))" (is "?L = ?R")
proof (cases "y \<in> carrier F")
  case True
  have "?L = \<P>(\<omega> in pmf_of_set (bounded_degree_polynomials F n). ring.hash F x \<omega> = y)" by simp
  also have "... = 1 / (real (card (carrier F)))" by (intro hash_prob_single assms conjI True)
  also have "... = ?R" using True by simp
  finally show ?thesis by simp
next
  case False
  interpret field "F" using assms by simp
  have fin_carr: "finite (carrier F)" using assms by simp
  note S = non_empty_bounded_degree_polynomials fin_degree_bounded[OF fin_carr]
  let ?S = "bounded_degree_polynomials F n"

  have "hash x f \<noteq> y" if "f \<in> ?S" for f
  proof -
    have "hash x f \<in> carrier F"
      using that unfolding hash_def bounded_degree_polynomials_def
      by (intro eval_in_carrier assms) (simp add: polynomial_incl univ_poly_carrier)
    thus ?thesis using False by auto
  qed
  hence "?L = measure (pmf_of_set (bounded_degree_polynomials F n)) {}"
    using S by (intro measure_eq_AE AE_pmfI) simp_all
  also have "... = ?R" using False by simp
  finally show ?thesis by simp
qed

lemma hash_k_wise_indep':
  assumes "field F \<and> finite (carrier F)"
  assumes "1 \<le> n"
  shows "prob_space.k_wise_indep_vars (pmf_of_set (bounded_degree_polynomials F n)) n
    (\<lambda>_. discrete) (ring.hash F) (carrier F)"
  by (intro prob_space.k_wise_indep_vars_compose[OF _ hash_k_wise_indep[OF assms]]
      prob_space_measure_pmf) auto

lemma hash_space':
  fixes R :: "('a,'b) idx_ring_enum_scheme"
  assumes "enum\<^sub>C R" "field\<^sub>C R"
  assumes "pro_size S dvd order (ring_of R)"
  assumes "I \<subseteq> {..<order (ring_of R)}" "card I \<le> k"
  shows "map_pmf (\<lambda>f. (\<lambda>i\<in>I. f i)) (sample_pro (hash_space' R k S)) = prod_pmf I (\<lambda>_. sample_pro S)"
    (is "?L = ?R")
proof (cases "I = {}")
  case False
  let ?b = "idx_size R"
  let ?s = "pro_size S"
  let ?t = "?b div ?s"
  let ?g = "\<lambda>x i. poly_eval R (poly_enum R k x) (idx_enum R i)"
  let ?f = "\<lambda>x. pro_select S (idx_enum_inv R x mod ?s)"
  let ?R_pmf = "pmf_of_set (carrier (ring_of R))"
  let ?S = "{xs \<in> carrier (poly_ring (ring_of R)). length xs \<le> k}"
  let ?T = "pmf_of_set (bounded_degree_polynomials (ring_of R) k)"

  interpret field "ring_of R" using assms(2) unfolding field\<^sub>C_def by auto

  have ring_c: "ring\<^sub>C R" using field_c_imp_ring assms(2) by auto
  note enum_c = enum_cD[OF assms(1)]

  have fin_carr: "finite (carrier (ring_of R))" using enum_c by simp

  have "0 < card I" using False assms(4) card_gt_0_iff finite_nat_iff_bounded by blast
  also have "... \<le> k" using assms(5) by simp
  finally have k_gt_0: "k > 0" by simp
  have b_gt_0: "?b > 0" unfolding enum_c(2) using fin_carr order_gt_0_iff_finite by blast
  hence t_gt_0: "?t > 0" using enum_c(2) assms(3) dvd_div_gt0 by simp
  have b_k_gt_0: "?b ^ k > 0" using b_gt_0 by simp

  have fin_I: "finite I" using assms(4) finite_subset by auto

  have inj:  "inj_on (idx_enum R) I"
    using assms(4) unfolding enum_c(2)
    by (intro inj_on_subset[OF bij_betw_imp_inj_on[OF enum_c(3)]])
  have "card (idx_enum R ` I) \<le> k"
    using assms(5) unfolding card_image[OF inj] by auto

  hence "prob_space.indep_vars ?T (\<lambda>_. discrete) hash (idx_enum R ` I)"
    using assms(4) k_gt_0 fin_I bij_betw_apply[OF enum_c(3)] enum_c(2)
    by (intro prob_space.k_wise_indep_vars_subset[OF _ hash_k_wise_indep']
        prob_space_measure_pmf conjI fin_carr field_axioms) auto
  hence "prob_space.indep_vars ?T ((\<lambda>_. discrete) \<circ> idx_enum R) (\<lambda>x \<omega>. eval \<omega> (idx_enum R x)) I"
    using inj unfolding hash_def
    by (intro prob_space.indep_vars_reindex prob_space_measure_pmf) auto
  hence indep: "prob_space.indep_vars ?T (\<lambda>_. discrete) (\<lambda>x \<omega>. eval \<omega> (idx_enum R x)) I"
    by (simp add:comp_def)

  have 0: "pmf (map_pmf (\<lambda>x. \<lambda>i\<in>I. eval x (idx_enum R i)) ?T) \<omega> = pmf (prod_pmf I (\<lambda>_. ?R_pmf)) \<omega>"
    (is "?L1 = ?R1") for \<omega>
  proof (cases "\<omega> \<in> extensional I")
    case True
    have "?L1 = measure ?T {x. (\<lambda>i\<in>I. eval x (idx_enum R i)) = \<omega>}"
      by (simp add:pmf_map vimage_def)
    also have "... = measure ?T {x. (\<forall>i\<in>I. eval x (idx_enum R i) = \<omega> i)}"
      using True unfolding restrict_def extensional_def
      by (intro arg_cong2[where f="measure"] refl Collect_cong) auto
    also have "... = (\<Prod>i\<in>I. measure ?T {x. eval x (idx_enum R i) = \<omega> i})"
      by (intro prob_space.split_indep_events[where I="I" and p="?T"] prob_space_measure_pmf
          fin_I refl prob_space.indep_vars_compose2[OF _ indep]) auto
    also have "... = (\<Prod>i\<in>I. measure ?T {x. hash (idx_enum R i) x = \<omega> i})"
      unfolding hash_def by simp
    also have "... = (\<Prod>i\<in>I. of_bool( \<omega> i \<in> carrier (ring_of R))/real (card (carrier (ring_of R))))"
      using k_gt_0 assms(4) by (intro prod.cong refl hash_prob_single'
          bij_betw_apply[OF enum_c(3)] fin_carr field_axioms) (auto simp:enum_c)
    also have "... = (\<Prod>i\<in>I. pmf (pmf_of_set (carrier (ring_of R))) (\<omega> i))"
      using fin_carr carrier_not_empty by (simp add:indicator_def)
    also have "... = ?R1"
      using True unfolding pmf_prod_pmf[OF fin_I] by simp
    finally show ?thesis by simp
  next
    case False
    have "?L1 = 0" using False unfolding pmf_eq_0_set_pmf set_map_pmf by auto
    moreover have "?R1 = 0"
      using False unfolding pmf_eq_0_set_pmf set_prod_pmf[OF fin_I] PiE_def by simp
    ultimately show ?thesis by simp
  qed

  have "map_pmf (\<lambda>x. \<lambda>i\<in>I. ?g x i) (pmf_of_set {..<?b^k}) =
    map_pmf (\<lambda>x. \<lambda>i\<in>I. poly_eval R x (idx_enum R i)) (map_pmf (poly_enum R k) (pmf_of_set {..<?b^k}))"
    by (simp add:map_pmf_comp)
  also have "... = map_pmf (\<lambda>x. \<lambda>i\<in>I. poly_eval R x (idx_enum R i)) (pmf_of_set ?S)"
    using b_k_gt_0 by (intro arg_cong2[where f="map_pmf"] refl map_pmf_of_set_bij_betw
        bij_betw_poly_enum assms(1,2) field_c_imp_ring) blast+
  also have "... = map_pmf (\<lambda>x. \<lambda>i\<in>I. poly_eval R x (idx_enum R i)) ?T"
    using k_gt_0 unfolding bounded_degree_polynomials_def
    by (intro map_pmf_cong refl arg_cong[where f="pmf_of_set"] restrict_ext ring_c) auto
  also have "... = map_pmf (\<lambda>x. \<lambda>i\<in>I. eval x (idx_enum R i)) ?T"
    using non_empty_bounded_degree_polynomials fin_degree_bounded[OF fin_carr] assms(4)
    by (intro map_pmf_cong poly_eval refl restrict_ext ring_c bij_betw_apply[OF enum_c(3)])
     (auto simp add:bounded_degree_polynomials_def ring_of_poly[OF ring_c] enum_c(2))
  also have "... = prod_pmf I (\<lambda>_. ?R_pmf)" (is "?L1 = ?R1")
    by (intro pmf_eqI 0)
  finally have 0: "map_pmf (\<lambda>x. \<lambda>i\<in>I. ?g x i) (pmf_of_set {..<?b^k}) = prod_pmf I (\<lambda>_. ?R_pmf)"
    by simp

  have 1: "map_pmf (\<lambda>x. x mod ?s) (pmf_of_set {..<?b}) = pmf_of_set {..<?s}" (is "?L1=?R1")
  proof -
    have "?L1 = map_pmf fst (map_pmf (\<lambda>x. (x mod ?s, x div ?s)) (pmf_of_set {..<?s*?t}))"
      using assms(3) by (simp add:map_pmf_comp enum_c(2))
    also have "... = map_pmf fst (pmf_of_set ({..<?s} \<times> {..<?t}))"
      using pro_size_gt_0 t_gt_0 lessThan_empty_iff finite_lessThan
      by (intro arg_cong2[where f="map_pmf"] refl map_pmf_of_set_bij_betw bij_betw_prod) force+
    also have "... = map_pmf fst (pair_pmf (pmf_of_set {..<?s}) (pmf_of_set {..<?t}))"
      using pro_size_gt_0 t_gt_0 by(intro arg_cong2[where f="map_pmf"] pmf_of_set_prod_eq refl) auto
    also have "... = pmf_of_set {..<?s}" using map_fst_pair_pmf by blast
    finally show ?thesis by simp
  qed

  have "map_pmf ?f ?R_pmf = map_pmf (\<lambda>x. pro_select S (x mod ?s)) (map_pmf (idx_enum_inv R) ?R_pmf)"
    by (simp add:map_pmf_comp)
  also have "... = map_pmf (\<lambda>x. pro_select S (x mod ?s)) (pmf_of_set {..<?b})"
    using enum_cD(1,2,4)[OF assms(1)] carrier_not_empty
    by (intro arg_cong2[where f="map_pmf"] refl map_pmf_of_set_bij_betw) auto
  also have "... = map_pmf (pro_select S) (map_pmf (\<lambda>x. x mod ?s) (pmf_of_set {..<?b}))"
    by (simp add:map_pmf_comp)
  also have "... = sample_pro S" unfolding sample_pro_alt 1 by simp
  finally have 2:"map_pmf ?f ?R_pmf = sample_pro S" by simp

  have "?L = map_pmf (\<lambda>x. \<lambda>i\<in>I. ?f (?g x i)) (pmf_of_set {..<?b^k})"
    using b_k_gt_0 unfolding sample_pro_alt hash_space'_def pro_size_def
    by (simp add: map_pmf_comp del:poly_eval.simps)
  also have "... =  map_pmf (\<lambda>f. \<lambda>i\<in>I. ?f (f i)) (map_pmf (\<lambda>x. \<lambda>i\<in>I. ?g x i) (pmf_of_set {..<?b^k}))"
    unfolding map_pmf_comp by (intro arg_cong2[where f="map_pmf"] refl restrict_ext ext) simp
  also have "... = prod_pmf I (\<lambda>_. map_pmf ?f (pmf_of_set (carrier (ring_of R))))" unfolding 0
    by (simp add:map_pmf_def Pi_pmf_bind_return[OF fin_I, where d'="undefined"] restrict_def)
  also have "... = ?R" unfolding 2 by simp
  finally show ?thesis by simp
next
  case True
  have "?L = map_pmf (\<lambda>f i. undefined) (sample_pro (hash_space' R k S))"
    using True by (intro map_pmf_cong refl) auto
  also have "... = return_pmf (\<lambda>f. undefined)" unfolding map_pmf_const by simp
  also have "... = ?R" using True by simp
  finally show "?L = ?R" by simp
qed

lemma hash_space'_range:
  "pro_select (hash_space' R k S) i j \<in> pro_set S"
  unfolding hash_space'_def by (simp add: pro_select_in_set)

definition hash_pro ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a,'b) pseudorandom_object_scheme \<Rightarrow> (nat \<Rightarrow> 'a) pseudorandom_object"
  where "hash_pro k d S = (
    let (p,j) = split_power (pro_size S);
        l = max j (floorlog p (d-1))
    in hash_space' (GF (p^l)) k S)"

definition hash_pro_spmf ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a,'b) pseudorandom_object_scheme \<Rightarrow> (nat \<Rightarrow> 'a) pseudorandom_object spmf"
  where "hash_pro_spmf k d S =
    do {
      let (p,j) = split_power (pro_size S);
      let l = max j (floorlog p (d-1));
      R \<leftarrow> GF\<^sub>R (p^l);
      return_spmf (hash_space' R k S)
    }"

definition hash_pro_pmf ::
  "nat \<Rightarrow> nat \<Rightarrow> ('a,'b) pseudorandom_object_scheme \<Rightarrow> (nat \<Rightarrow> 'a) pseudorandom_object pmf"
  where "hash_pro_pmf k d S = map_pmf the (hash_pro_spmf k d S)"

syntax
  "_FLIPBIND"     :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'b"  (infixr \<open>=<<\<close> 54)

syntax_consts
  "_FLIPBIND"       == Monad_Syntax.bind

translations
  "_FLIPBIND f g"   => "g \<bind> f"

context
  fixes S
  fixes d :: nat
  fixes k :: nat
  assumes size_prime_power: "is_prime_power (pro_size S)"
begin

private definition p where "p = fst (split_power (pro_size S))"
private definition j where "j = snd (split_power (pro_size S))"
private definition l where "l = max j (floorlog p (d-1))"

private lemma split_power: "(p,j) = split_power (pro_size S)"
  using p_def j_def by auto

private lemma hash_sample_space_alt: "hash_pro k d S = hash_space' (GF (p^l)) k S"
  unfolding hash_pro_def split_power[symmetric] by (simp add:j_def l_def Let_def)

private lemma p_prime : "prime p" and j_gt_0: "j > 0"
proof -
  obtain q r where 0:"pro_size S = q^r" and q_prime: "prime q" and r_gt_0: "r > 0"
    using size_prime_power is_prime_power_def by blast

  have "(p,j) = split_power (q^r)" unfolding split_power 0 by simp
  also have "... = (q,r)" by (intro split_power_prime q_prime r_gt_0)
  finally have "(p,j) = (q,r)" by simp
  thus "prime p" "j > 0" using q_prime r_gt_0 by auto
qed

private lemma l_gt_0: "l > 0"
  unfolding l_def using j_gt_0 by simp

private lemma prime_power: "is_prime_power (p^l)"
  using p_prime l_gt_0 unfolding is_prime_power_def by auto

lemma hash_in_hash_pro_spmf: "hash_pro k d S \<in> set_spmf (hash_pro_spmf k d S)"
  using GF_in_GF_R[OF prime_power]
  unfolding hash_pro_def hash_pro_spmf_def split_power[symmetric] l_def by (auto simp add:set_bind_spmf)

lemma lossless_hash_pro_spmf: "lossless_spmf (hash_pro_spmf k d S)"
proof -
  have "lossless_spmf (GF\<^sub>R (p^l))" by (intro galois_field_random_1 prime_power)
  thus ?thesis unfolding hash_pro_spmf_def split_power[symmetric] l_def by simp
qed

lemma hashp_eq_hash_pro_spmf: "set_pmf (hash_pro_pmf k d S) = set_spmf (hash_pro_spmf k d S)"
  unfolding hash_pro_pmf_def using lossless_imp_spmf_of_pmf[OF lossless_hash_pro_spmf]
  by (metis set_spmf_spmf_of_pmf)

lemma hashp_in_hash_pro_spmf:
  assumes "x \<in> set_pmf (hash_pro_pmf k d S)"
  shows "x \<in> set_spmf (hash_pro_spmf k d S)"
  using hashp_eq_hash_pro_spmf assms by auto

lemma hash_pro_in_hash_pro_pmf: "hash_pro k d S \<in> set_pmf (hash_pro_pmf k d S)"
  unfolding hashp_eq_hash_pro_spmf by (intro hash_in_hash_pro_spmf)

lemma hash_pro_spmf_distr:
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)"
  assumes "I \<subseteq> {..<d}" "card I \<le> k"
  shows "map_pmf (\<lambda>f. (\<lambda>i\<in>I. f i)) (sample_pro s) = prod_pmf I (\<lambda>_. sample_pro S)"
proof -
  have "(d-1) < p^floorlog p (d-1)"
    using floorlog_leD prime_gt_1_nat[OF p_prime] by simp
  hence "d \<le> p^floorlog p (d-1)" by (cases d) auto
  also have "... \<le> p^l"
    using prime_gt_0_nat[OF p_prime] unfolding l_def by (intro power_increasing) auto
  finally have 0: "d \<le> p^l" by simp

  obtain R where R_in: "R \<in> set_spmf (GF\<^sub>R (p^l))" and s_def: "s = hash_space' R k S"
    using assms(1) unfolding hash_pro_spmf_def split_power[symmetric] l_def
    by (auto simp add:set_bind_spmf)
  have 1: "order (ring_of R) = p ^ l"
    using galois_field_random_1(1)[OF prime_power R_in]  by auto
  have "I \<subseteq> {..<d}" using assms by auto
  also have "... \<subseteq> {..<order (ring_of R)}" using 0 unfolding 1 by auto
  finally have "I \<subseteq> {..<order (ring_of R)}" by simp
  moreover have "j \<le> l" unfolding l_def by auto
  hence "pro_size S dvd order (ring_of R)"
    unfolding 1 split_power_result[OF split_power] by (intro le_imp_power_dvd)
  ultimately show ?thesis
    using galois_field_random_1(1)[OF prime_power R_in] assms(3)
    unfolding s_def by (intro hash_space') simp_all
qed

lemma hash_pro_spmf_component:
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)"
  assumes "i < d" "k > 0"
  shows "map_pmf (\<lambda>f. f i) (sample_pro s) = sample_pro S" (is "?L = ?R")
proof -
  have "?L = map_pmf (\<lambda>f. f i) (map_pmf (\<lambda>f. (\<lambda>i\<in>{i}. f i)) (sample_pro s))"
    using assms(1) unfolding map_pmf_comp by (intro map_pmf_cong refl) auto
  also have "... =  map_pmf (\<lambda>f. f i) (prod_pmf {i} (\<lambda>_. sample_pro S))"
    using assms by (subst hash_pro_spmf_distr[OF assms(1)]) auto
  also have "... = ?R" by (subst Pi_pmf_component) auto
  finally show ?thesis  by simp
qed

lemma hash_pro_spmf_indep:
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)"
  assumes "I \<subseteq> {..<d}" "card I \<le> k"
  shows "prob_space.indep_vars (sample_pro s) (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) I"
proof (rule measure_pmf.indep_vars_pmf[OF refl])
  fix x J
  assume a:"J \<subseteq> I"
  have 0:"J \<subseteq> {..<d}" using a assms(2) by auto
  have "card J \<le> card I" using finite_subset[OF assms(2)] by (intro card_mono a)  auto
  also have "... \<le> k" using assms(3) by simp
  finally have 1: " card J \<le> k" by simp
  let ?s = "sample_pro s"

  have 2: "0 < k" if "x \<in> J" for x
  proof -
    have "0 < card J" using 0 that card_gt_0_iff finite_nat_iff_bounded by auto
    also have "... \<le> k" using 1 by simp
    finally show ?thesis by simp
  qed

  have "measure ?s {\<omega>. \<forall>j\<in>J. \<omega> j = x j} = measure (map_pmf (\<lambda>\<omega>. \<lambda>j\<in>J. \<omega> j)?s) {\<omega>. \<forall>j\<in>J. \<omega> j = x j}"
    by auto
  also have "... = measure (prod_pmf J (\<lambda>_. sample_pro S)) (Pi J (\<lambda>j. {x j}))"
    unfolding hash_pro_spmf_distr[OF assms(1) 0 1] by (intro arg_cong2[where f="measure"]) (auto simp:Pi_def)
  also have "... = (\<Prod>j\<in>J. measure (sample_pro S) {x j})"
    using finite_subset[OF a] finite_subset[OF assms(2)] by (intro measure_Pi_pmf_Pi) auto
  also have "... = (\<Prod>j\<in>J. measure (map_pmf (\<lambda>\<omega>. \<omega> j) ?s) {x j})"
    using 0 1 2 by (intro prod.cong arg_cong2[where f="measure"] refl
        arg_cong[where f="measure_pmf"] hash_pro_spmf_component[OF assms(1), symmetric]) auto
  also have "... = (\<Prod>j\<in>J. measure ?s {\<omega>. \<omega> j = x j})" by (simp add:vimage_def)
  finally show "measure ?s {\<omega>. \<forall>j\<in>J. \<omega> j = x j} = (\<Prod>j\<in>J. measure_pmf.prob ?s {\<omega>. \<omega> j = x j})"
    by simp
qed

lemma hash_pro_spmf_k_indep:
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)"
  shows "prob_space.k_wise_indep_vars (sample_pro s) k (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<d}"
  using hash_pro_spmf_indep[OF assms]
  unfolding prob_space.k_wise_indep_vars_def[OF prob_space_measure_pmf] by auto


private lemma hash_pro_spmf_size_aux:
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)"
  shows "pro_size s = (p^l)^k" (is "?L = ?R")
proof -
  obtain R where R_in: "R \<in> set_spmf (GF\<^sub>R (p^l))" and s_def: "s = hash_space' R k S"
    using assms(1) unfolding hash_pro_spmf_def split_power[symmetric] l_def
    by (auto simp add:set_bind_spmf)
  have 1: "order (ring_of R) = p ^ l" and ec: "enum\<^sub>C R"
    using galois_field_random_1(1)[OF prime_power R_in]  by auto

  have "?L = idx_size R ^ k - 1 + 1"
    unfolding s_def pro_size_def hash_space'_def by simp
  also have "... = ((p^l)^k - 1) + 1"
    using 1 enum_cD(2)[OF ec] by simp
  also have "... = (p^l)^k" using prime_gt_0_nat[OF p_prime] by simp
  finally show ?thesis  by simp
qed

lemma floorlog_alt_def:
  "floorlog b a = (if 1 < b then nat \<lceil>log (real b) (real a+1)\<rceil> else 0)"
proof (cases "a > 0 \<and> 1 < b")
  case True
  have 1:"log (real b) (real a + 1) > 0" using True by (subst zero_less_log_cancel_iff) auto

  have "a < real a + 1" by simp
  also have "... = b powr (log b (real a + 1))" using True by simp
  also have "... \<le> b powr (\<lceil>log b (real a + 1)\<rceil>)"
    using True by (intro iffD2[OF powr_le_cancel_iff]) auto
  also have "... = b powr (real (nat \<lceil>log b (real a + 1)\<rceil>))"
    using 1 by (intro arg_cong2[where f="(powr)"] refl) linarith
  also have "... = b ^ nat \<lceil>log (real b) (real a + 1)\<rceil>" using True by (subst powr_realpow) auto
  finally have "a < b ^ nat \<lceil>log (real b) (real a + 1)\<rceil>" by simp
  hence 0:"floorlog b a \<le> nat \<lceil>log (real b) (real a+1)\<rceil>" using True by (intro floorlog_leI) auto

  have "b ^ (nat \<lceil>log b (real a + 1)\<rceil> - 1) = b powr (real (nat \<lceil>log b (real a + 1)\<rceil> - 1))"
    using True by (subst powr_realpow) auto
  also have "... = b powr (\<lceil>log b (real a + 1)\<rceil> - 1)"
    using 1 by (intro arg_cong2[where f="(powr)"] refl) linarith
  also have "... < b powr (log b (real a + 1))" using True by (intro powr_less_mono) linarith+
  also have "... = real (a + 1)" using True by simp
  finally have "b ^ (nat \<lceil>log (real b) (real a + 1)\<rceil> - 1) < a + 1" by linarith
  hence "b ^ (nat \<lceil>log (real b) (real a + 1)\<rceil> - 1) \<le> a" by simp
  hence "floorlog b a \<ge> nat \<lceil>log (real b) (real a+1)\<rceil>" using True by (intro floorlog_geI) auto
  hence "floorlog b a = nat \<lceil>log (real b) (real a+1)\<rceil>" using 0 by linarith
  also have "... = (if 1 < b then nat \<lceil>log (real b) (real a+1)\<rceil> else 0)" using True by simp
  finally show ?thesis by simp
next
  case False
  hence a_eq_0: "a = 0 \<or> \<not>(1 < b)" by simp
  thus ?thesis unfolding floorlog_def by auto
qed

lemma hash_pro_spmf_size:
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)"
  assumes "(p',j') = split_power (pro_size S)"
  shows "pro_size s = (p'^(max j' (floorlog p' (d-1))))^k"
  unfolding hash_pro_spmf_size_aux[OF assms(1)] l_def p_def j_def using assms(2)
  by (metis fst_conv snd_conv)

lemma hash_pro_spmf_size':
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)" "d > 0"
  assumes "(p',j') = split_power (pro_size S)"
  shows "pro_size s = (p'^(k*max j' (nat \<lceil>log p' d\<rceil>)))"
proof -
  have "pro_size s = (p^(max j (floorlog p (d-1))))^k"
    unfolding hash_pro_spmf_size_aux[OF assms(1)] l_def by simp
  also have "... = (p^(max j (nat \<lceil>log p (real (d-1)+1)\<rceil>)))^k"
    using prime_gt_1_nat[OF p_prime] by (simp add:floorlog_alt_def)
  also have "... = (p^(max j (nat \<lceil>log p d\<rceil>)))^k" using assms(2) by (subst of_nat_diff) auto
  also have "... = p^(k*max j (nat \<lceil>log p d\<rceil>))" by (simp add:ac_simps power_mult[symmetric])
  also have "... = p'^(k*max j' (nat \<lceil>log p' d\<rceil>))"
    using assms(3) p_def j_def by (metis fst_conv snd_conv)
  finally show ?thesis by simp
qed

lemma hash_pro_spmf_size_prime_power:
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)"
  assumes "k > 0"
  shows "is_prime_power (pro_size s)"
  unfolding hash_pro_spmf_size_aux[OF assms(1)] power_mult[symmetric] is_prime_power_def
  using p_prime  mult_pos_pos[OF l_gt_0 assms(2)] by blast

lemma hash_pro_smpf_range:
  assumes "s \<in> set_spmf (hash_pro_spmf k d S)"
  shows "pro_select s i q \<in> pro_set S"
proof -
  obtain R where R_in: "R \<in> set_spmf (GF\<^sub>R (p^l))" and s_def: "s = hash_space' R k S"
    using assms(1) unfolding hash_pro_spmf_def split_power[symmetric] l_def
    by (auto simp add:set_bind_spmf)
  thus ?thesis
    unfolding s_def using hash_space'_range by auto
qed

lemmas hash_pro_size' = hash_pro_spmf_size'[OF hash_in_hash_pro_spmf]
lemmas hash_pro_size = hash_pro_spmf_size[OF hash_in_hash_pro_spmf]
lemmas hash_pro_size_prime_power = hash_pro_spmf_size_prime_power[OF hash_in_hash_pro_spmf]
lemmas hash_pro_distr = hash_pro_spmf_distr[OF hash_in_hash_pro_spmf]
lemmas hash_pro_component = hash_pro_spmf_component[OF hash_in_hash_pro_spmf]
lemmas hash_pro_indep = hash_pro_spmf_indep[OF hash_in_hash_pro_spmf]
lemmas hash_pro_k_indep = hash_pro_spmf_k_indep[OF hash_in_hash_pro_spmf]
lemmas hash_pro_range = hash_pro_smpf_range[OF hash_in_hash_pro_spmf]

lemmas hash_pro_pmf_size' = hash_pro_spmf_size'[OF hashp_in_hash_pro_spmf]
lemmas hash_pro_pmf_size = hash_pro_spmf_size[OF hashp_in_hash_pro_spmf]
lemmas hash_pro_pmf_size_prime_power = hash_pro_spmf_size_prime_power[OF hashp_in_hash_pro_spmf]
lemmas hash_pro_pmf_distr = hash_pro_spmf_distr[OF hashp_in_hash_pro_spmf]
lemmas hash_pro_pmf_component = hash_pro_spmf_component[OF hashp_in_hash_pro_spmf]
lemmas hash_pro_pmf_indep = hash_pro_spmf_indep[OF hashp_in_hash_pro_spmf]
lemmas hash_pro_pmf_k_indep = hash_pro_spmf_k_indep[OF hashp_in_hash_pro_spmf]
lemmas hash_pro_pmf_range = hash_pro_smpf_range[OF hashp_in_hash_pro_spmf]

end

open_bundle pseudorandom_object_notation
begin
notation hash_pro (\<open>\<H>\<close>)
notation hash_pro_spmf (\<open>\<H>\<^sub>S\<close>)
notation hash_pro_pmf (\<open>\<H>\<^sub>P\<close>)
notation list_pro (\<open>\<L>\<close>)
notation nat_pro (\<open>\<N>\<close>)
notation geom_pro (\<open>\<G>\<close>)
notation prod_pro (infixr \<open>\<times>\<^sub>P\<close> 65)
end

bundle no_pseudorandom_object_notation
begin
no_notation hash_pro (\<open>\<H>\<close>)
no_notation hash_pro_spmf (\<open>\<H>\<^sub>S\<close>)
no_notation hash_pro_pmf (\<open>\<H>\<^sub>P\<close>)
no_notation list_pro (\<open>\<L>\<close>)
no_notation nat_pro (\<open>\<N>\<close>)
no_notation geom_pro (\<open>\<G>\<close>)
no_notation prod_pro (infixr \<open>\<times>\<^sub>P\<close> 65)
end

end