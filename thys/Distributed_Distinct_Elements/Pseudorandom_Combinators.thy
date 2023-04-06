section \<open>Combinators for Pseudo-random Objects\<close>

text \<open>This section introduces a combinator library for pseudo-random objects. Each object can be
described as a sample space, a function from an initial segment of the natural numbers that selects
a value (or data structure.) Semantically they are multisets with the natural interpretation as a
probability space (each element is selected with a probability proportional to its occurence count
in the multiset). Operationally the selection procedure describes an algorithm to sample from the
space.

After general definitions and lemmas basic sample spaces, such as chosing a natural uniformly in
an initial segment, a product construction the main pseudo-random objects: hash families and
expander graphs are introduced. In both cases the range is itself an arbitrary sample space, such
that it is for example possible to construct a pseudo-random object that samples seeds for hash
families using an expander walk.

The definitions @{term "\<Psi>"} in Section~\ref{sec:inner_algorithm} and @{term "\<Theta>"} in
Section~\ref{sec:outer_algorithm} are good examples.

A nice introduction into such constructions has been published by Goldreich~\cite{goldreich2011}.\<close>

subsection \<open>Definitions and General Lemmas\<close>

theory Pseudorandom_Combinators
  imports
    Finite_Fields.Card_Irreducible_Polynomials
    Universal_Hash_Families.Carter_Wegman_Hash_Family
    Frequency_Moments.Product_PMF_Ext
    Distributed_Distinct_Elements_Preliminary
    Expander_Graphs.Expander_Graphs_Strongly_Explicit
begin

unbundle intro_cong_syntax
hide_const "Quantum.T"
hide_const "Discrete_Topology.discrete"
hide_const "Polynomial.order"
no_notation Digraph.dominates ("_ \<rightarrow>\<index> _" [100,100] 40)

record 'a sample_space =
  size :: "nat"
  sample_space_select :: "nat \<Rightarrow> 'a"

definition sample_pmf
  where "sample_pmf S = map_pmf (sample_space_select S) (pmf_of_set {..<size S})"

definition "sample_space S \<equiv> size S > 0"

definition "select S k = (sample_space_select S (if k < size S then k else 0))"

definition "sample_set S = select S ` {..<size S}"

lemma sample_space_imp_ne:
  assumes "sample_space S"
  shows "{..<size S} \<noteq> {}"
  using assms unfolding sample_space_def by auto

lemma sample_pmf_alt:
  assumes "sample_space S"
  shows "sample_pmf S = map_pmf (select S) (pmf_of_set {..<size S})"
  using sample_space_imp_ne[OF assms] unfolding sample_pmf_def select_def
  by (intro map_pmf_cong refl) simp

lemma sample_space_alt:
  assumes "sample_space S"
  shows "sample_set S = set_pmf (sample_pmf S)"
  using sample_space_imp_ne[OF assms]
  unfolding sample_set_def sample_pmf_alt[OF assms]
  by simp

lemma sample_set_alt:
  assumes "sample_space S"
  shows "sample_set S = sample_space_select S ` {..<size S}"
  unfolding sample_set_def select_def
  by (intro image_cong) auto

lemma select_range:
  assumes "sample_space S"
  shows "select S i \<in> sample_set S"
  using assms unfolding sample_space_def select_def sample_set_def by auto

declare [[coercion sample_pmf]]

lemma integrable_sample_pmf[simp]:
  fixes f :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "sample_space S"
  shows "integrable (measure_pmf (sample_pmf S)) f"
proof -
  have "finite (set_pmf (pmf_of_set {..<size S}))"
    using assms sample_space_def
    by (subst set_pmf_of_set) auto
  hence "finite (set_pmf (sample_pmf S))"
    unfolding sample_pmf_def by simp
  thus ?thesis
    by (intro integrable_measure_pmf_finite)
qed

subsection \<open>Basic sample spaces\<close>

text \<open>Sample space for uniformly selecting a natural number less than a given bound:\<close>

definition nat_sample_space :: "nat \<Rightarrow> nat sample_space" ("[_]\<^sub>S")
  where "nat_sample_space n = \<lparr> size = n, select = id \<rparr>"

lemma nat_sample_pmf:
  "sample_pmf ([x]\<^sub>S) = pmf_of_set {..<x}"
  unfolding nat_sample_space_def sample_pmf_def by simp

lemma nat_sample_space[simp]:
  assumes "n > 0"
  shows "sample_space [n]\<^sub>S"
  using assms
  unfolding sample_space_def nat_sample_space_def by simp

text \<open>Sample space for the product of two sample spaces:\<close>

definition prod_sample_space ::
  "'a sample_space \<Rightarrow> 'b sample_space \<Rightarrow> ('a \<times> 'b) sample_space" (infixr "\<times>\<^sub>S" 65)
  where
    "prod_sample_space s t =
      \<lparr> size = size s * size t,
        select = (\<lambda>i. (select s (i mod (size s)), select t (i div (size s)))) \<rparr>"

lemma split_pmf_mod_div':
  assumes "a > (0::nat)"
  assumes "b > 0"
  shows "map_pmf (\<lambda>x. (x mod a, x div a)) (pmf_of_set {..<a * b}) = pmf_of_set ({..<a} \<times> {..<b})"
proof -
  have "x + a * y < a * b" if "x < a" "y < b" for x y
  proof -
    have a:"y+1 \<le> b" using that by simp
    have "x + a * y < a + a * y"
      using that by simp
    also have "... = a * (y+1)"
      by simp
    also have "... \<le> a * b"
      by (intro mult_left_mono a) auto
    finally show ?thesis by simp
  qed

  hence "bij_betw (\<lambda>x. (x mod a, x div a)) {..<a * b} ({..<a} \<times> {..<b})"
    using assms less_mult_imp_div_less
    by (intro bij_betwI[where g="(\<lambda>x. fst x + a * snd x)"])
     (auto simp add:mult.commute)

  moreover have "a * b > 0" using assms by simp
  hence "{..<a * b} \<noteq> {}" by blast
  ultimately show "?thesis"
    by (intro map_pmf_of_set_bij_betw) auto
qed

lemma pmf_of_set_prod_eq:
  assumes "A \<noteq> {}" "finite A"
  assumes "B \<noteq> {}" "finite B"
  shows  "pmf_of_set (A \<times> B) = pair_pmf (pmf_of_set A) (pmf_of_set B)"
proof -
  have "indicat_real (A \<times> B) (i, j) = indicat_real A i * indicat_real B j" for i j
    by (cases "i \<in> A"; cases "j \<in> B") auto
  hence "pmf (pmf_of_set (A \<times> B)) (i,j) = pmf (pair_pmf (pmf_of_set A) (pmf_of_set B)) (i,j)"
    for i j using assms by (simp add:pmf_pair)
  thus ?thesis
    by (intro pmf_eqI) auto
qed

lemma split_pmf_mod_div:
  assumes "a > (0::nat)"
  assumes "b > 0"
  shows "map_pmf (\<lambda>x. (x mod a, x div a)) (pmf_of_set {..<a * b}) =
    pair_pmf (pmf_of_set {..<a}) (pmf_of_set {..<b})"
  using assms by (auto intro!: pmf_of_set_prod_eq simp add:split_pmf_mod_div')

lemma split_pmf_mod:
  assumes "a > (0::nat)"
  assumes "b > 0"
  shows "map_pmf (\<lambda>x. x mod a) (pmf_of_set {..<a * b}) = pmf_of_set {..<a}"
proof -
  have "map_pmf (\<lambda>x. x mod a) (pmf_of_set {..<a * b}) =
   map_pmf (fst \<circ> (\<lambda>x. (x mod a, x div a))) (pmf_of_set {..<a * b})"
    by (simp add:comp_def)
  also have "... = map_pmf fst (pair_pmf (pmf_of_set {..<a}) (pmf_of_set {..<b}))"
    by (simp add:map_pmf_compose split_pmf_mod_div[OF assms])
  also have "... = pmf_of_set {..<a}"
    by (simp add:map_fst_pair_pmf)
  finally show ?thesis by simp
qed

lemma prod_sample_pmf:
  assumes "sample_space S"
  assumes "sample_space T"
  shows "sample_pmf (S \<times>\<^sub>S T) = pair_pmf (sample_pmf S) (sample_pmf T)" (is "?L = ?R")
proof -
  have size: "size S * size T > 0"
    using assms sample_space_def by (metis nat_0_less_mult_iff)
  hence a:"{..<size S * size T} \<noteq> {}" "finite {..<size S * size T}"
    using lessThan_empty_iff by auto
  have b:"x div size S mod size T = x div size S" if "x < size S * size T" for x
    by (simp add: algebra_simps less_mult_imp_div_less that)

  have "?L = map_pmf (\<lambda>i. (select S (i mod size S), select T (i div size S)))
    (pmf_of_set {..<size S * size T})"
    unfolding sample_pmf_def prod_sample_space_def by simp
  also have "... = map_pmf ((\<lambda>(x,y). (select S x, select T y)) \<circ> (\<lambda>i. (i mod size S, i div size S)))
    (pmf_of_set {..<size S * size T})"
    by (simp add:comp_def)
  also have "... = map_pmf (\<lambda>(x,y). (select S x, select T y))
    (map_pmf (\<lambda>i. (i mod size S, i div size S)) (pmf_of_set {..<size S * size T}))"
    by (subst map_pmf_compose)  simp
  also have "... = map_pmf (\<lambda>(x,y). (select S x, select T y))
    (pair_pmf (pmf_of_set {..<size S}) (pmf_of_set {..<size T}))"
    using size by (subst split_pmf_mod_div) auto
  also have "... = ?R"
    unfolding sample_pmf_alt[OF assms(1)] sample_pmf_alt[OF assms(2)] map_pair by simp
  finally show ?thesis
    by simp
qed

lemma prod_sample_space[simp]:
  assumes "sample_space S" "sample_space T"
  shows "sample_space (S \<times>\<^sub>S T)"
  using assms
  unfolding sample_space_def prod_sample_space_def by simp

lemma prod_sample_set:
  assumes "sample_space S"
  assumes "sample_space T"
  shows "sample_set (S \<times>\<^sub>S T) = sample_set S \<times> sample_set T" (is "?L = ?R")
  using assms by (simp add:sample_space_alt prod_sample_pmf)

subsection \<open>Hash Families\<close>

lemma indep_vars_map_pmf:
  assumes "prob_space.indep_vars (measure_pmf p) (\<lambda>_. discrete) (\<lambda>i \<omega>. X' i (f \<omega>)) I"
  shows "prob_space.indep_vars (measure_pmf (map_pmf f p)) (\<lambda>_. discrete) X' I"
proof -
  have "prob_space.indep_vars (measure_pmf p) (\<lambda>_. discrete) (\<lambda>i. X' i \<circ> f) I"
    using assms by (simp add:comp_def)
  hence "prob_space.indep_vars (distr (measure_pmf p) discrete f) (\<lambda>_. discrete) X' I"
    by (intro prob_space.indep_vars_distr prob_space_measure_pmf) auto
  thus ?thesis
    using map_pmf_rep_eq by metis
qed

lemma k_wise_indep_vars_map_pmf:
  assumes "prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>i \<omega>. X' i (f \<omega>)) I"
  shows "prob_space.k_wise_indep_vars (measure_pmf (map_pmf f p)) k (\<lambda>_. discrete) X' I"
  using assms indep_vars_map_pmf
  unfolding prob_space.k_wise_indep_vars_def[OF prob_space_measure_pmf]
  by blast

lemma (in prob_space) k_wise_indep_subset:
  assumes "J \<subseteq> I"
  assumes "k_wise_indep_vars k M' X' I"
  shows "k_wise_indep_vars k M' X' J"
  using assms unfolding k_wise_indep_vars_def by simp

lemma (in prob_space) k_wise_indep_vars_reindex:
  assumes "inj_on f I"
  assumes "k_wise_indep_vars k M' X' (f ` I)"
  shows "k_wise_indep_vars k (M' \<circ> f) (\<lambda>k \<omega>. X' (f k) \<omega>) I"
proof -
  have "indep_vars (M' \<circ> f) (\<lambda>k. X' (f k)) J" if "finite J" "card J \<le> k" "J \<subseteq> I" for J
  proof -
    have "f ` J \<subseteq> f ` I" using that by auto
    moreover have "card (f ` J) \<le> k"
      using card_image_le[OF that(1)] that(2) order.trans by auto
    moreover have "finite (f ` J)" using that by auto
    ultimately have "indep_vars M' X' (f ` J)"
      using assms(2) unfolding k_wise_indep_vars_def by simp
    thus ?thesis
      using that assms(1) inj_on_subset
      by (intro indep_vars_reindex)
  qed
  thus ?thesis
    unfolding k_wise_indep_vars_def by simp
qed

definition GF :: "nat \<Rightarrow> int set list set ring"
  where "GF n = (SOME F. finite_field F \<and> order F = n)"

definition is_prime_power :: "nat \<Rightarrow> bool"
  where "is_prime_power n \<longleftrightarrow> (\<exists>p k. Factorial_Ring.prime p \<and> k > 0 \<and> n = p^k)"

lemma
  assumes "is_prime_power n"
  shows GF: "finite_field (GF n)" "order (GF n) = n"
proof -
  obtain p k where p_k: "Factorial_Ring.prime p" "k > 0" "n = p^k"
    using assms unfolding is_prime_power_def by blast
  have a:"\<exists>(F :: int set list set ring). finite_field F \<and> order F = n"
    using existence[OF p_k(2,1)] p_k(3) by simp
  show  "finite_field (GF n)" "order (GF n) = n"
    unfolding GF_def
    using someI_ex[OF a]
    by auto
qed

lemma is_prime_power: "Factorial_Ring.prime p \<Longrightarrow> k > 0 \<Longrightarrow> is_prime_power (p^k)"
  unfolding is_prime_power_def by auto

definition split_prime_power :: "nat \<Rightarrow> (nat \<times> nat)"
  where "split_prime_power n = (THE (p, k). p^k = n \<and> Factorial_Ring.prime p \<and> k > 0)"

lemma split_prime_power:
  assumes "Factorial_Ring.prime p"
  assumes "k > 0"
  shows "split_prime_power (p^k) = (p,k)"
proof -
  have "q = p \<and> l = k" if "q^l = p^k" "Factorial_Ring.prime q" "l > 0" for q l
  proof -
    have "q dvd p^k" using that by (metis dvd_power)
    hence "q dvd p" using prime_dvd_power that by auto
    moreover have "p dvd q^l" using that assms(2) by (metis dvd_power)
    hence "p dvd q" using prime_dvd_power that assms by blast
    ultimately have a:"p = q" by auto
    hence "l = k" using that prime_power_inj by auto
    thus ?thesis using a by simp
  qed
  thus ?thesis
    unfolding split_prime_power_def using assms
    by (intro the_equality) auto
qed

definition \<H> :: "nat \<Rightarrow> nat \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<H> k d R = (
    let (p,n) = split_prime_power (size R);
        m = (LEAST j. d \<le> p^j \<and> j \<ge> n);
        f = from_nat_into (carrier (GF (p^m)));
        f' = to_nat_on (carrier (GF (p^m)));
        g = from_nat_into (bounded_degree_polynomials (GF (p^m)) k) in
    \<lparr> size = p^(m*k), select = (\<lambda>i x. select R ((f' (ring.hash (GF (p^m)) (f x) (g i))) mod p^n))\<rparr>)"

locale hash_sample_space =
  fixes k d p n :: nat
  fixes R :: "'a sample_space"
  assumes p_prime: "Factorial_Ring.prime p"
  assumes size_R: "size R = p ^ n"
  assumes k_gt_0: "k > 0"
  assumes n_gt_0: "n > 0"
begin

abbreviation S where "S \<equiv> \<H> k d R"

lemma p_n_def: "(p,n) = split_prime_power (size R)"
  unfolding size_R
  by (intro split_prime_power[symmetric] n_gt_0 p_prime)

definition m where "m = (LEAST j. d \<le> p^j \<and> j \<ge> n)"
definition f where "f = from_nat_into (carrier (GF (p^m)))"
definition f' where "f' = to_nat_on (carrier (GF (p^m)))"

lemma n_lt_m: "n \<le> m" and d_lt_p_m: "d \<le> p^m"
proof -
  define j :: nat where "j = max n d"
  have "d \<le> 2^d" by simp
  also have "... \<le> 2^j"
    unfolding j_def
    by (intro iffD2[OF power_increasing_iff]) auto
  also have "... \<le> p^j"
    using p_prime prime_ge_2_nat
    by (intro power_mono) auto
  finally have "d \<le> p^j" by simp
  moreover have "n \<le> j" unfolding j_def by simp
  ultimately have "d \<le> p^m \<and> m \<ge> n"
    unfolding m_def
    by (intro LeastI[where P="\<lambda>x. d \<le> p^ x \<and> x \<ge> n" and k="j"]) auto
  thus "n \<le> m" "d \<le> p^m"
    by auto
qed

lemma
  is_field: "finite_field (GF (p^m))" (is "?A") and
  field_order: "order (GF(p^m)) = p^m"  (is "?B")
proof -
  have "is_prime_power (p^m)"
    using n_gt_0 n_lt_m
    by (intro is_prime_power p_prime) auto

  thus "?A" "?B"
    using GF by auto
qed

interpretation cw: carter_wegman_hash_family "GF (p^m)" "k"
  using finite_field_def is_field finite_field_axioms_def
  by (intro carter_wegman_hash_familyI k_gt_0) auto

lemma field_size: "cw.field_size = p^m"
  using field_order unfolding Coset.order_def by simp

lemma f_bij: "bij_betw f {..<p^m} (carrier (GF (p^m)))"
  unfolding f_def using field_size  bij_betw_from_nat_into_finite[where S="carrier (GF (p^m))"]
  by simp

definition g where "g = from_nat_into cw.space"

lemma p_n_gt_0: "p^n > 0"
  by (metis p_prime gr0I not_prime_0 power_not_zero)

lemma p_m_gt_0: "p^m > 0"
  by (metis p_prime gr0I not_prime_0 power_not_zero)

lemma S_eq: "S = \<lparr> size = p^(m*k), sample_space_select = (\<lambda> i x. select R (f' (cw.hash (f x) (g i)) mod p^n )) \<rparr>"
  unfolding \<H>_def
  by (simp add:p_n_def[symmetric] m_def[symmetric] f_def[symmetric] g_def f'_def Let_def cw.space_def)

lemma \<H>_size: "size S > 0"
  unfolding S_eq using p_m_gt_0 k_gt_0 by simp

lemma sample_space: "sample_space S"
  using \<H>_size unfolding sample_space_def by simp

lemma sample_space_R: "sample_space R"
  using size_R p_n_gt_0 unfolding sample_space_def by auto

lemma range: "range (select S i) \<subseteq> sample_set R"
proof -
  define \<alpha> where "\<alpha> = select S i"
  have "\<alpha> x \<in> sample_set R" for x
  proof -
    have "\<alpha> \<in> sample_set S"
      unfolding \<alpha>_def by (intro select_range sample_space)
    then obtain j where \<alpha>_alt: "\<alpha> = (\<lambda>x. select R (f' (cw.hash (f x) (g j)) mod p^n))" "j < p^(m*k)"
      unfolding sample_set_alt[OF sample_space] unfolding S_eq by auto
    thus "\<alpha> x \<in> sample_set R"
      unfolding \<alpha>_alt
      by (intro select_range sample_space_R)
  qed
  thus ?thesis
    unfolding \<alpha>_def by auto
qed

lemma cw_space: "map_pmf g (pmf_of_set {..<p^(m*k)}) = pmf_of_set cw.space"
proof-
  have card_cw_space: "p ^ (m * k) = card (cw.space)"
    unfolding cw.space_def cw.bounded_degree_polynomials_card  field_size
    by (simp add:power_mult)
  have card_cw_space_gt_0: "card (cw.space) > 0"
    using card_gt_0_iff cw.finite_space cw.non_empty_bounded_degree_polynomials by blast

  show ?thesis
    unfolding g_def using card_cw_space card_cw_space_gt_0
      bij_betw_from_nat_into_finite[where S="cw.space"]
    by (intro map_pmf_of_set_bij_betw) auto
qed

lemma single:
  assumes "x < d"
  shows "map_pmf (\<lambda>\<omega>. \<omega> x) (sample_pmf S) = sample_pmf R" (is "?L = ?R")
proof -
  have f_x_carr: "f x \<in> carrier (GF (p^m))"
    using assms d_lt_p_m
    by (intro bij_betw_apply[OF f_bij]) auto

  have "pmf (map_pmf (cw.hash (f x)) (pmf_of_set cw.space)) i =
    pmf (pmf_of_set (carrier (GF (p ^ m)))) i" (is "?L1 = ?R1") for i
  proof -
    have "?L1 = cw.prob (cw.hash (f x) -` {i})"
      unfolding cw.M_def by (simp add:pmf_map)
    also have "... = real (card ({i} \<inter> carrier (GF (p ^ m)))) / real cw.field_size"
      using cw.prob_range[OF f_x_carr, where A="{i}" ] by (simp add:vimage_def)
    also have "... = ?R1"
      by (cases "i \<in> carrier (GF (p^m))", auto)
    finally  show ?thesis by simp
  qed

  hence b: "map_pmf (cw.hash (f x)) (pmf_of_set cw.space) = pmf_of_set (carrier (GF (p^m)))"
    by (intro pmf_eqI) simp

  have c: "map_pmf f' (pmf_of_set (carrier (GF (p^m)))) = pmf_of_set {..<p^m}"
    unfolding f'_def using to_nat_on_finite[where S="carrier (GF (p^m))"] field_size
    by (intro map_pmf_of_set_bij_betw) auto

  have "n \<le> m" "p > 0"
    using n_lt_m p_prime prime_gt_0_nat by auto
  hence d: "map_pmf (\<lambda>x. x mod p^n) (pmf_of_set {..<p^m}) = pmf_of_set {..<p^n}"
    using split_pmf_mod[where a = "p^n" and b="p^(m-n)"]
    by (simp add:power_add[symmetric])

  have "?L = map_pmf ((\<lambda>\<omega>. \<omega> x) \<circ> (sample_space_select S)) (pmf_of_set {..<size S})"
    unfolding sample_pmf_def by (simp add:map_pmf_compose)
  also have "... = map_pmf (\<lambda>\<omega>. sample_space_select S \<omega> x) (pmf_of_set {..<size S})"
    by (simp add:comp_def)
  also have "... = map_pmf (select R \<circ> (\<lambda>x. x mod p^n) \<circ> f' \<circ> (cw.hash (f x)) \<circ> g) (pmf_of_set {..<p^(m*k)})"
    unfolding S_eq by (simp add:comp_def)
  also have "... = map_pmf (select R) (pmf_of_set {..<p^n})"
    by (simp add:map_pmf_compose cw_space b c d)
  also have "... = ?R"
    unfolding sample_pmf_alt[OF sample_space_R] size_R by simp
  finally show ?thesis by simp
qed

lemma indep:
  "prob_space.k_wise_indep_vars (sample_pmf S) k (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<d}"
proof -
  let ?p = "map_pmf g (pmf_of_set {..<p ^ (m * k)})"
  let ?h = "(\<lambda>i x. select R (f' (cw.hash (f x) i) mod p ^ n))"

  have a:"cw.k_wise_indep_vars k (\<lambda>_. discrete) cw.hash (f ` {..<d})"
    using d_lt_p_m
    by (intro cw.k_wise_indep_subset[OF _ cw.k_wise_indep] image_subsetI bij_betw_apply[OF f_bij])
    auto

  have "cw.k_wise_indep_vars k (\<lambda>_. discrete) (\<lambda>i \<omega>. select R (f' (cw.hash i \<omega>) mod p^n)) (f ` {..<d})"
    by (intro cw.k_wise_indep_vars_compose[OF a]) auto
  moreover
  have "inj_on f {..<p^m}"
    using f_bij bij_betw_def by auto
  hence "inj_on f {..<d}"
    using inj_on_subset d_lt_p_m by blast
  ultimately have "cw.k_wise_indep_vars k (\<lambda>_. discrete) (\<lambda>i \<omega>. select R (f' (cw.hash (f i) \<omega>) mod p ^ n)) {..<d}"
    using cw.k_wise_indep_vars_reindex[where f="f"] unfolding comp_def by auto

  hence "prob_space.k_wise_indep_vars (measure_pmf ((map_pmf ?h \<circ> map_pmf g) (pmf_of_set {..<p^(m*k)}))) k
     (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<d}"
    unfolding cw.M_def cw_space[symmetric] comp_def by (intro k_wise_indep_vars_map_pmf[where p="?p"]) auto

  hence "prob_space.k_wise_indep_vars (measure_pmf (map_pmf (\<lambda>i x. ?h (g i) x) (pmf_of_set {..<p^(m*k)}))) k
     (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<d}"
    unfolding map_pmf_compose[symmetric] by (simp add:comp_def)

  thus ?thesis
    unfolding sample_pmf_def S_eq by simp
qed

lemma size:
  fixes m :: nat
  assumes "d > 0"
  defines m_altdef: "m \<equiv> max n (nat \<lceil>log p d\<rceil>)"
  shows "size S = p^(m*k)"
proof -
  have "real d = p powr (log p d)"
    using assms prime_gt_1_nat[OF p_prime]
    by (intro powr_log_cancel[symmetric]) auto
  also have "... \<le> p powr (nat \<lceil>log p d\<rceil>)"
    using prime_gt_1_nat[OF p_prime] by (intro powr_mono) linarith+
  also have "... = p^ (nat \<lceil>log p d\<rceil>)"
    using prime_gt_1_nat[OF p_prime] by (subst powr_realpow) auto
  also have "... \<le> p^m"
    using prime_gt_1_nat[OF p_prime] unfolding m_altdef
    by (intro power_increasing Nat.of_nat_mono) auto
  finally have "d \<le> p ^ m"
    by simp

  moreover have "n \<le> m"
    unfolding m_altdef by simp
  moreover have "m \<le> y" if "d \<le> p ^ y" "n \<le> y" for y
  proof -
    have "log p d \<le> log p (p ^ y)"
      using assms prime_gt_1_nat[OF p_prime]
      by (intro iffD2[OF log_le_cancel_iff] that(1) Nat.of_nat_mono) auto
    also have "... = log p (p powr (real y))"
      using prime_gt_1_nat[OF p_prime] by (subst powr_realpow) auto
    also have "... = y"
      using prime_gt_1_nat[OF p_prime] by (intro log_powr_cancel) auto
    finally have "log p d \<le> y" by simp
    hence "nat \<lceil>log p d\<rceil> \<le> y"
      by simp
    thus "m \<le> y"
      using that(2) unfolding m_altdef by simp
  qed
  ultimately have m_eq: "m = (LEAST j. d \<le> p ^ j \<and> n \<le> j)"
    by (intro Least_equality[symmetric]) auto

  show ?thesis
    unfolding S_eq m_def m_eq by simp
qed

end

text \<open>Sample space with a geometric distribution\<close>

fun count_zeros :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "count_zeros 0 k = 0" |
  "count_zeros (Suc n) k = (if odd k then 0 else 1 + count_zeros n (k div 2))"

lemma count_zeros_iff: "j \<le> n \<Longrightarrow> count_zeros n k \<ge> j \<longleftrightarrow> 2^j dvd k"
proof (induction j arbitrary: n k)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then obtain n' where n_def: "n = Suc n'" using Suc_le_D by presburger
  show ?case using Suc unfolding n_def by auto
qed

lemma count_zeros_max:
  "count_zeros n k \<le> n"
  by (induction n arbitrary: k) auto

definition \<G> :: "nat \<Rightarrow> nat sample_space" where
  "\<G> n = \<lparr> size = 2^n, sample_space_select = count_zeros n \<rparr>"

lemma \<G>_sample_space[simp]: "sample_space (\<G> n)"
  unfolding sample_space_def \<G>_def by simp

lemma \<G>_range: "sample_set (\<G> n) \<subseteq> {..n}"
  using count_zeros_max
  unfolding sample_set_alt[OF \<G>_sample_space] unfolding \<G>_def by auto

lemma \<G>_prob:
  "measure  (sample_pmf (\<G> n)) {\<omega>. \<omega> \<ge> j} = of_bool (j \<le> n) / 2^j" (is "?L = ?R")
proof (cases "j \<le> n")
  case True
  have a:"{..<(2^n)::nat} \<noteq> {}"
    by (simp add: lessThan_empty_iff)
  have b:"finite {..<(2^n)::nat}" by simp

  define f :: "nat \<Rightarrow> nat" where "f = (\<lambda>x. x * 2^j)"
  have d:"inj_on  f {..<2^(n-j)}" unfolding f_def by (intro inj_onI) simp

  have e:"2^j > (0::nat)" by simp

  have "y \<in> f ` {..< 2^(n-j)} \<longleftrightarrow> y \<in> {x. x < 2^n \<and> 2^j dvd x}" for y :: nat
  proof -
    have "y \<in> f ` {..< 2^(n-j)} \<longleftrightarrow> (\<exists>x. x < 2 ^ (n - j) \<and> y = 2 ^ j * x)"
      unfolding f_def by auto
    also have "... \<longleftrightarrow> (\<exists>x. 2^j * x < 2^j * 2 ^ (n-j) \<and> y = 2 ^ j * x)"
      using e by simp
    also have "... \<longleftrightarrow> (\<exists>x. 2^j * x < 2^n \<and> y = 2 ^ j * x)"
      using True by (subst power_add[symmetric]) simp
    also have "... \<longleftrightarrow> (\<exists>x. y < 2^n \<and> y = x * 2 ^ j)"
      by (metis Groups.mult_ac(2))
    also have "... \<longleftrightarrow> y \<in> {x. x < 2^n \<and> 2^j dvd x}" by auto
    finally show ?thesis by simp
  qed

  hence c:"f ` {..< 2^(n-j)} = {x. x < 2^n \<and> 2^j dvd x}" by auto

  have "?L = measure (pmf_of_set {..<2^n}) {\<omega>. count_zeros n \<omega> \<ge> j}"
    unfolding sample_pmf_def \<G>_def by simp
  also have "... = real (card {x::nat. x < 2^n \<and> 2^j dvd x}) / 2^n"
    by (simp add: measure_pmf_of_set[OF a b] count_zeros_iff[OF True])
     (simp add:lessThan_def Collect_conj_eq)
  also have "... = real (card (f ` {..<2^(n-j)})) / 2^n"
    by (simp add:c)
  also have "... = real (card ({..<(2^(n-j)::nat)})) / 2^n"
    by (simp add: card_image[OF d])
  also have "... = ?R"
    using True by (simp add:frac_eq_eq power_add[symmetric])
  finally show ?thesis by simp
next
  case False
  have "set_pmf (sample_pmf (\<G> n)) \<subseteq> {..n}"
    unfolding sample_space_alt[OF \<G>_sample_space, symmetric]
    using \<G>_range by simp
  hence "?L = measure (sample_pmf (\<G> n)) {}"
    using False by (intro measure_pmf_cong) auto
  also have "... = ?R"
    using False by simp
  finally show ?thesis
    by simp
qed

lemma \<G>_prob_single:
  "measure  (sample_pmf (\<G> n)) {j} \<le> 1 / 2^j" (is "?L \<le> ?R")
proof -
  have "?L = measure (sample_pmf (\<G> n)) ({j..}-{j+1..})"
    by (intro measure_pmf_cong) auto
  also have "... = measure (sample_pmf (\<G> n)) {j..} - measure (sample_pmf (\<G> n)) {j+1..}"
    by (intro measure_Diff) auto
  also have "... = measure (sample_pmf (\<G> n)) {\<omega>. \<omega> \<ge> j}-measure (sample_pmf (\<G> n)) {\<omega>. \<omega> \<ge> (j+1)}"
    by (intro arg_cong2[where f="(-)"] measure_pmf_cong) auto
  also have "... = of_bool (j \<le> n) * 1 / 2 ^ j - of_bool (j + 1 \<le> n) / 2 ^ (j + 1)"
    unfolding \<G>_prob by simp
  also have "... \<le> 1/2^j - 0"
    by (intro diff_mono) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

subsection \<open>Expander Walks\<close>

definition \<E> :: "nat \<Rightarrow> real \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<E> l \<Lambda> S = (let e = see_standard (size S) \<Lambda> in
    \<lparr> size = see_size e * see_degree e^(l-1),
      sample_space_select = (\<lambda>i j. select S (see_sample_walk e (l-1) i ! j)) \<rparr>) "

locale expander_sample_space =
  fixes l :: nat
  fixes \<Lambda> :: real
  fixes S :: "'a sample_space"
  assumes l_gt_0: "l > 0"
  assumes \<Lambda>_gt_0: "\<Lambda> > 0"
  assumes sample_space_S: "sample_space S"
begin

definition e where "e = see_standard (size S) \<Lambda>"

lemma size_S_gt_0: "size S > 0"
  using sample_space_S unfolding sample_space_def by simp

lemma \<E>_alt: "(\<E> l \<Lambda> S) =
  \<lparr> size = see_size e * see_degree e^(l-1),
    sample_space_select = (\<lambda>i j. select S (see_sample_walk e (l-1) i ! j)) \<rparr>"
  unfolding \<E>_def e_def[symmetric] by (simp add:Let_def)

lemmas see_standard = see_standard[OF size_S_gt_0 \<Lambda>_gt_0]

sublocale E: regular_graph "graph_of e"
  using see_standard(1) unfolding is_expander_def e_def by auto

lemma e_deg_gt_0: "see_degree e > 0"
  unfolding e_def see_standard by simp

lemma e_size_gt_0: "see_size e > 0"
  unfolding e_def see_standard using size_S_gt_0 by simp

lemma sample_space: "sample_space (\<E> l \<Lambda> S)"
  unfolding sample_space_def \<E>_alt using e_size_gt_0 e_deg_gt_0 by simp

lemma range: "select (\<E> l \<Lambda> S) i j \<in> sample_set S"
proof -
  define \<alpha> where "\<alpha> = select (\<E> l \<Lambda> S) i"
  have "\<alpha> \<in> sample_set (\<E> l \<Lambda> S)"
    unfolding \<alpha>_def by (intro select_range sample_space)
  then obtain k where "\<alpha> = sample_space_select  (\<E> l \<Lambda> S) k"
    using sample_set_alt[OF sample_space] by auto
  hence "\<alpha> j \<in> sample_set S"
    unfolding \<E>_alt using select_range[OF sample_space_S] by simp
  thus ?thesis
    unfolding \<alpha>_def by simp
qed

lemma sample_set: "sample_set (\<E> l \<Lambda> S) \<subseteq> (UNIV \<rightarrow> sample_set S)"
proof (rule subsetI)
  fix x assume "x \<in> sample_set (\<E> l \<Lambda> S)"

  then obtain i where "x = select (\<E> l \<Lambda> S) i"
    unfolding sample_set_def by auto
  thus "x \<in> UNIV \<rightarrow> sample_set S"
    using range by auto
qed

lemma walks:
  defines "R \<equiv> map_pmf (\<lambda>xs i. select S (xs ! i)) (pmf_of_multiset (walks (graph_of e) l))"
  shows "sample_pmf (\<E> l \<Lambda> S) = R"
proof -
  let ?S = "{..<see_size e * see_degree e ^ (l-1)}"
  let ?T = "(map_pmf (see_sample_walk e (l-1)) (pmf_of_set ?S))"

  have "0 \<in> ?S"
    using e_size_gt_0 e_deg_gt_0 l_gt_0 by auto
  hence "?S \<noteq> {}"
    by blast
  hence "?T = pmf_of_multiset {#see_sample_walk e (l-1) i. i \<in># mset_set ?S#}"
    by (subst map_pmf_of_set) simp_all
  also have "... = pmf_of_multiset (walks' (graph_of e) (l-1))"
    by (subst see_sample_walk) auto
  also have "... = pmf_of_multiset (walks (graph_of e) l)"
    unfolding walks_def using l_gt_0 by (cases l, simp_all)
  finally have 0:"?T = pmf_of_multiset (walks (graph_of e) l)"
    by simp

  have "sample_pmf (\<E> l \<Lambda> S) = map_pmf (\<lambda>xs j. select S (xs ! j)) ?T"
    unfolding map_pmf_comp sample_pmf_def \<E>_alt by simp
  also have "... = R"
    unfolding 0 R_def by simp
  finally show ?thesis by simp
qed

lemma uniform_property:
  assumes "i < l"
  shows "map_pmf (\<lambda>w. w i) (\<E> l \<Lambda> S) = sample_pmf S" (is "?L = ?R")
proof -
  have "?L = map_pmf (select S) (map_pmf (\<lambda>xs. (xs ! i)) (pmf_of_multiset (walks (graph_of e) l)))"
    unfolding walks by (simp add: map_pmf_comp)
  also have "... = map_pmf (select S) (pmf_of_set (verts (graph_of e)))"
    unfolding E.uniform_property[OF assms] by simp
  also have "... = ?R"
    unfolding sample_pmf_alt[OF sample_space_S] e_def graph_of_def using see_standard by simp
  finally show ?thesis
    by simp
qed

lemma size:
  "size (\<E> l \<Lambda> S) =  size S * (16 ^ ((l-1) * nat \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>))" (is "?L = ?R")
proof -
  have "?L = see_size e * see_degree e ^ (l - 1)"
    unfolding \<E>_alt by simp
  also have "... = size S *  (16 ^ nat \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>) ^ (l - 1)"
    using see_standard unfolding e_def by simp
  also have "... = size S * (16 ^ ((l-1) * nat \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>))"
    unfolding power_mult[symmetric] by (simp add:ac_simps)
  finally show ?thesis
    by simp
qed

end

end