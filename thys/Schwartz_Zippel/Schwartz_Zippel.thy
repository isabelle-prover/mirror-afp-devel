section \<open>The Schwartz-Zippel Lemma\<close>
theory Schwartz_Zippel imports
    Factor_Algebraic_Polynomial.Poly_Connection
    Polynomials.MPoly_Type
    "HOL-Probability.Product_PMF"
begin

text \<open>This theory formalizes the Schwartz-Zippel lemma
   for multivariate polynomials (@{type mpoly}). \<close>

lemma schwartz_zippel_uni:
  fixes P :: "('a::idom) Polynomial.poly"
  fixes S :: "'a set"
  assumes "finite S" "S \<noteq> {}"
  assumes "Polynomial.degree P \<le> d"
  assumes "P \<noteq> 0"
  shows "measure_pmf.prob (pmf_of_set S) {r. poly P r = 0} \<le> real d / card S"
proof -
  have 1: " ({r. poly P r = 0} \<inter> S) = {r. poly P r = 0 \<and> r \<in> S}"
    by auto  
  have 2: "prob_space.prob (pmf_of_set S) {r. poly P r = 0} =
    prob_space.prob (pmf_of_set S) {r. poly P r = 0 \<and> r \<in> S}"
    by (metis (full_types) "1" assms(1) assms(2) measure_Int_set_pmf set_pmf_of_set)
  have card: "card {r. poly P r = 0  \<and> r \<in> S} \<le> d"
    using poly_roots_degree assms(3) assms(4) by (smt (verit) Collect_mono_iff card_mono le_trans poly_roots_finite) 
  have inter: "S \<inter> {r. poly P r = 0 \<and> r \<in> S} =                                        
    {r. poly P r = 0 \<and> r \<in> S} "
    by auto

  have prob:"prob_space.prob (pmf_of_set S) {r. poly P r = 0 \<and> r \<in> S} \<le> real d / card S"
    by (simp add: assms(1) assms(2) assms(4) card inter measure_pmf_of_set divide_right_mono)

  thus "prob_space.prob (pmf_of_set S) {r. poly P r = 0 } \<le> real d / card S "
    by (simp add: 2)
qed

(* Copied from degree_mpoly_to_mpoly_poly *)
(* TODO: cleanup possible duplication? *)
lemma degree_mpoly_to_poly [simp]:
  assumes "vars p = {x}"
  shows "Polynomial.degree (mpoly_to_poly x p) = MPoly_Type.degree p x"
proof (rule antisym)
  show "Polynomial.degree (mpoly_to_poly x p) \<le> MPoly_Type.degree p x"
  proof (intro Polynomial.degree_le allI impI)
    fix i assume i: "i > MPoly_Type.degree p x"
    have "poly.coeff (mpoly_to_poly x p) i =
            (\<Sum>m. 0 when lookup m x = i)"
      unfolding coeff_mpoly_to_mpoly_poly using i
      by (metis (no_types, lifting) Sum_any.cong Sum_any.neutral coeff_mpoly_to_poly degree_geI leD lookup_single_eq when_neq_zero)
    also have "\<dots> = 0"
      by simp
    finally show "poly.coeff (mpoly_to_poly x p) i = 0" .
  qed
next
  show "Polynomial.degree (mpoly_to_poly x p) \<ge> MPoly_Type.degree p x"
  proof (cases "p = 0")
    case False
    then obtain m where m: "MPoly_Type.coeff p m \<noteq> 0" "lookup m x = MPoly_Type.degree p x"
      using monom_of_degree_exists by blast
    show "Polynomial.degree (mpoly_to_poly x p) \<ge> MPoly_Type.degree p x"
    proof (rule Polynomial.le_degree)
      have "0 \<noteq> MPoly_Type.coeff p m"
        using m by auto
      have "poly.coeff (mpoly_to_poly x p) (MPoly_Type.degree p x) = 
        MPoly_Type.coeff p (monomial (MPoly_Type.degree p x) x)"
        unfolding coeff_mpoly_to_poly by auto
      also have "monomial (MPoly_Type.degree p x) x = m"
        unfolding m(2)[symmetric] using assms coeff_notin_vars m(1)
        by (intro keys_subset_singleton_imp_monomial) blast
      finally show "poly.coeff (mpoly_to_poly x p) (MPoly_Type.degree p x) \<noteq> 0"
        using m by auto
    qed
  qed auto
qed

(* TODO Move *)
lemma total_degree_add: "total_degree (x + y) \<le> max (total_degree x) (total_degree y)"
proof -
  define h :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> nat" where "h = (\<lambda>m. sum (lookup m) (keys m))"
  have "insert 0 (h ` keys (mapping_of (x + y))) \<subseteq>
        insert 0 (h ` (keys (mapping_of x) \<union> keys (mapping_of y)))"
    unfolding plus_mpoly.rep_eq
    by (intro Set.insert_mono image_mono Poly_Mapping.keys_add)
  also have "\<dots> = insert 0 (h ` keys (mapping_of x)) \<union>
                  insert 0 (h ` keys (mapping_of y))"
    by (simp add: image_Un)
  finally have "Max (insert 0 (h ` keys (mapping_of (x + y)))) \<le> Max \<dots>"
    by (intro Max_mono) simp_all
  also have "?this \<longleftrightarrow> ?thesis"
    unfolding total_degree_def map_fun_def o_def id_def h_def [symmetric]
    by (subst Max_Un [symmetric]; simp)
  finally show ?thesis .
qed

(* TODO Move *)
lemma total_degree_sum:
  assumes "finite S"
  shows"total_degree (sum f S) \<le>
    Max ((total_degree \<circ> f) ` S)"
  using assms
proof (induction S)
  case empty
  then show ?case
    by auto
next
  case (insert x F)
  show ?case
  proof (cases "F = {}")
    case False
    have "total_degree (f x + sum f F) \<le>
      max (total_degree (f x)) (total_degree (sum f F))"
      using total_degree_add by blast
    moreover have "... \<le>
       max (total_degree (f x)) (Max ((total_degree \<circ> f) ` F))"
      using local.insert(3) by linarith
    also have "\<dots> = (Max ((total_degree \<circ> f) ` insert x F))"
      using insert False by simp
    finally show ?thesis
      using insert.hyps by simp
  qed simp_all
qed

(* TODO Move *)
lemma coeff_mpoly_to_mpoly_poly_restrict:
  shows "coeff (mpoly_to_mpoly_poly x P) i =
    sum (\<lambda>m.
      MPoly_Type.monom (remove_key x m)
       (MPoly_Type.coeff P m) when lookup m x = i)
    (Poly_Mapping.keys (mapping_of P))"
  unfolding coeff_mpoly_to_mpoly_poly
  by (auto intro!: Sum_any.expand_superset simp: coeff_keys)

lemma Max_le_Max:
  assumes "A \<noteq> {}"
  assumes "finite A" "finite B"
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>b. b \<in> B \<and> a \<le> b"
  shows "Max A \<le> Max B"
proof -
  from assms have "B \<noteq> {}"
    by blast
  thus ?thesis
    using assms by (intro Max.boundedI) (auto simp: Max_ge_iff)
qed

lemma sum_lookup_remove_key:
  "sum (lookup (remove_key x y)) (keys (remove_key x y)) + lookup y x =
   sum (lookup y) (keys y)"
proof -
  have "sum (lookup y) (keys y) =
        sum (lookup y) (keys (remove_key x y + monomial (lookup y x) x))"
    by (subst (2) remove_key_sum [of x, symmetric]) auto
  also have "keys (remove_key x y + monomial (lookup y x) x) =
             keys (remove_key x y) \<union> keys (monomial (lookup y x) x)"
    by (subst keys_add) (auto simp flip: remove_key_keys)
  also have "sum (lookup y) \<dots> = sum (lookup y) (keys (remove_key x y)) +
               sum (lookup y) (keys (monomial (lookup y x) x))"
    by (subst sum.union_disjoint) (auto simp flip: remove_key_keys)
  also have "sum (lookup y) (keys (remove_key x y)) =
             sum (lookup (remove_key x y)) (keys (remove_key x y))"
    by (intro sum.cong) (auto simp: remove_key_lookup when_def simp flip: remove_key_keys)
  also have "sum (lookup y) (keys (monomial (lookup y x) x)) =
             sum (lookup y) {x}"
    by (intro sum.mono_neutral_cong_left) auto
  also have "\<dots> = lookup y x"
    by simp
  finally show ?thesis ..
qed

lemma total_degree_nonzero:
  assumes "P \<noteq> 0"
  shows "total_degree P =
    Max ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of P))"
  unfolding total_degree_def by (auto simp: assms)

lemma poly_mapping_eq_iff: "(m = m') \<longleftrightarrow> (\<forall>i. lookup m i = lookup m' i)"
  by (auto intro: poly_mapping_eqI)

(* TODO: move *)
lemma total_degree_coeff_mpoly_to_mpoly_poly:
  assumes "coeff (mpoly_to_mpoly_poly x P) i \<noteq> 0"
  shows "total_degree (coeff (mpoly_to_mpoly_poly x P) i) + i \<le> total_degree P"
proof -
  have P: "P \<noteq> 0"
    using assms by force

  have nonempty: "keys
   (mapping_of(poly.coeff (mpoly_to_mpoly_poly x P) i)) \<noteq> {}"
    using assms by auto

  have *: "
    {y. \<exists>xa\<in>keys (mapping_of P) \<inter> {xa. lookup xa x = i} \<inter> {x. MPoly_Type.coeff P x \<noteq> 0}. y = sum (lookup xa) (keys xa)} \<subseteq>
    (insert 0
        ((\<lambda>y. sum (lookup y) (keys y)) ` keys (mapping_of P)))"
  by auto
     
  have "total_degree (coeff (mpoly_to_mpoly_poly x P) i) + i =
    (MAX x\<in>keys (mapping_of (poly.coeff (mpoly_to_mpoly_poly x P) i)).
      sum (lookup x) (keys x)) + i"
    by (subst total_degree_nonzero) (use assms in auto)
  moreover have "... =
      (MAX x\<in>keys (mapping_of (poly.coeff (mpoly_to_mpoly_poly x P) i)).
      sum (lookup x) (keys x) + i)"
    by (subst Max_add_commute[symmetric]) (use assms in auto)
  moreover have "... =
    (MAX x\<in>\<Union>xa\<in>keys (mapping_of P) \<inter>
              {xa. lookup xa x = i} \<inter>
              {x. MPoly_Type.coeff P x \<noteq> 0}.
             {remove_key x xa}.
      sum (lookup x) (keys x) + i)"
    unfolding coeff_mpoly_to_mpoly_poly_restrict
    unfolding MPoly_Type.degree_def mapping_of_sum[symmetric]
    apply (subst keys_sum)
    subgoal by simp
    subgoal for i j
      apply (simp add: zero_mpoly.rep_eq poly_mapping_eq_iff remove_key_lookup when_def)
      apply metis
      done
    subgoal
      by (auto simp add: if_distrib zero_mpoly.rep_eq when_def)
    done
  moreover have "... =
    Max {y. \<exists>xa\<in>keys (mapping_of P) \<inter> {xa. lookup xa x = i}  \<inter>
              {x. MPoly_Type.coeff P x \<noteq> 0}.
       y = sum (lookup (remove_key x xa)) (keys (remove_key x xa)) + lookup xa x}"
    by (intro arg_cong[where f = Max]) auto
  moreover have "... =
    Max {y. \<exists>xa\<in>keys (mapping_of P) \<inter> {xa. lookup xa x = i}  \<inter>
              {x. MPoly_Type.coeff P x \<noteq> 0}.
       y = sum (lookup xa) (keys xa)}"
    by (subst sum_lookup_remove_key) auto
  
  moreover have "... \<le>
    Max (insert 0
        ((\<lambda>y. sum (lookup y) (keys y)) ` keys (mapping_of P)))"
    apply (intro Max_mono[OF *])
    subgoal
      using nonempty unfolding coeff_mpoly_to_mpoly_poly_restrict
      by (force elim!: sum.not_neutral_contains_not_neutral)
    subgoal
      by simp
    done
  moreover have "... = total_degree P"
    unfolding total_degree_def by auto
  ultimately show ?thesis by auto
qed

(* TODO: move *)
lemma degree_le_total_degree:
  shows "MPoly_Type.degree P x \<le> total_degree P"
  unfolding total_degree_def degree.rep_eq map_fun_def o_def id_def
proof (rule Max.boundedI; safe?)
  fix k
  assume k: "k \<in> keys (mapping_of P)"
  have "x \<in> keys k \<or> x \<notin> keys k" by auto
  moreover {
    assume "x \<in> keys k"
    then have "lookup k x \<le> sum (lookup k) (keys k)"
      by (simp add: sum.remove)
    then have "lookup k x
         \<le> Max (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of P)))"
      using k
      by (smt (verit, ccfv_SIG) Max_ge dual_order.trans finite_imageI finite_insert finite_keys image_subset_iff subset_insertI) 
  }
  moreover {
    assume "x \<notin> keys k"
    then have "lookup k x = 0"
      by (simp add: in_keys_iff)
    then have "lookup k x
         \<le> Max (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of P)))"
      by linarith
  }
  ultimately show "lookup k x
         \<le> Max (insert 0 ((\<lambda>x. sum (lookup x) (keys x)) ` keys (mapping_of P)))" by auto
qed auto

(* TODO: move *)
lemma insertion_update:
  shows "insertion (f(x := r)) P = poly (map_poly (insertion f) (mpoly_to_mpoly_poly x P)) r"
  by (subst insertion_mpoly_to_mpoly_poly[symmetric,where \<beta> = "f"]) auto

(* TODO: move? *)
lemma measure_pmf_prob_dependent_product_bound:
  assumes "countable A" "\<And>i. countable (B i)"
  assumes "\<And>a. a \<in> A \<Longrightarrow> measure_pmf.prob N (B a) \<le> r"
  shows "measure_pmf.prob (pair_pmf M N) (Sigma A B) \<le> measure_pmf.prob M A * r"
proof -
  have "measure_pmf.prob (pair_pmf M N) (Sigma A B) = (\<Sum>\<^sub>a(a, b)\<in>Sigma A B. pmf M a * pmf N b)"
    by (auto intro!: infsetsum_cong simp add: measure_pmf_conv_infsetsum pmf_pair)
  moreover have "\<dots> = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B a. pmf M a * pmf N b)"
  proof (subst infsetsum_Sigma)
    show "(\<lambda>(a, b). pmf M a * pmf N b) abs_summable_on Sigma A B"
      unfolding case_prod_unfold
      by (metis (no_types, lifting) SigmaE abs_summable_on_cong pmf_abs_summable pmf_pair prod.sel)
  qed (use assms in auto)
  moreover have "... = (\<Sum>\<^sub>aa\<in>A. pmf M a * (measure_pmf.prob N (B a)))"
    by (simp add: infsetsum_cmult_right measure_pmf_conv_infsetsum pmf_abs_summable)
  moreover have "... \<le> (\<Sum>\<^sub>aa\<in>A. pmf M a * r)"
  proof (rule infsetsum_mono)
    show "(\<lambda>a. pmf M a * measure_pmf.prob N (B a)) abs_summable_on A"
    proof (rule abs_summable_on_comparison_test')
      show "norm (pmf M x * measure_pmf.prob N (B x)) \<le> pmf M x * 1" for x
        unfolding norm_mult by (intro mult_mono) auto
    qed auto
  qed (auto intro: mult_mono assms)
  moreover have"... = r  * (\<Sum>\<^sub>aa\<in>A. pmf M a)"
    by (simp add: infsetsum_cmult_left pmf_abs_summable)
  moreover have"... = measure_pmf.prob M A * r"
    by (simp add: measure_pmf_conv_infsetsum)
  ultimately show ?thesis
    by linarith
qed

(* TODO: move? *)
lemma measure_pmf_prob_dependent_product_bound':
  assumes "countable (A \<inter> set_pmf M)" "\<And>i. countable (B i \<inter> set_pmf N)"
  assumes "\<And>a. a \<in> A \<inter> set_pmf M \<Longrightarrow> measure_pmf.prob N (B a \<inter> set_pmf N) \<le> r"
  shows "measure_pmf.prob (pair_pmf M N) (Sigma A B) \<le> measure_pmf.prob M A * r"
proof -
  have *: "Sigma A B \<inter> (set_pmf M \<times> set_pmf N) =
    Sigma (A \<inter> set_pmf M) (\<lambda>i. B i \<inter> set_pmf N)"
    by auto

  have "measure_pmf.prob (pair_pmf M N) (Sigma A B) =
    measure_pmf.prob (pair_pmf M N) (Sigma (A \<inter> set_pmf M) (\<lambda>i. B i \<inter> set_pmf N))"
    by (metis * measure_Int_set_pmf set_pair_pmf)
  moreover have "... \<le>
    measure_pmf.prob M (A \<inter> set_pmf M) * r"
    using measure_pmf_prob_dependent_product_bound[OF assms(1-3)]
    by auto
  moreover have "... = measure_pmf.prob M A * r"
    by (simp add: measure_Int_set_pmf)
  ultimately show ?thesis by linarith
qed

(* TODO: move? *)
lemma finite_set_pmf_Pi_pmf:
  assumes "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> finite (set_pmf (p x))"
  shows "finite (set_pmf (Pi_pmf A def p))"
proof -
  from set_Pi_pmf_subset'[OF assms(1)]
  have 1: "set_pmf (Pi_pmf A def p)
    \<subseteq> PiE_dflt A def (set_pmf \<circ> p)"
    by fastforce
  have 2: "finite ..."
    by (intro finite_PiE_dflt) (use assms in auto)
  show ?thesis using 1 2
    using finite_subset by auto 
qed

theorem schwartz_zippel:
  fixes P :: "('a::idom) mpoly"
  fixes S :: "'a set"
  assumes S: "finite S" "S \<noteq> {}"
  assumes V: "finite V"
  assumes P: "total_degree P \<le> d" "P \<noteq> 0" "vars P \<subseteq> V"
  shows "measure_pmf.prob (Pi_pmf V 0 (\<lambda>i. pmf_of_set S)) {f. insertion f P = 0} \<le> real d / card S"
  using V P
proof (induction V arbitrary: P d)
  case empty
  then show ?case
    by (metis (mono_tags, lifting) Collect_empty_eq divide_nonneg_nonneg insertion_Const lead_coeff_eq_0_iff measure_empty of_nat_0_le_iff subset_empty vars_empty_iff)
next
  case (insert x V)
  have "x \<notin> vars P \<or> x \<in> vars P" by auto
  moreover {
    assume x: "x \<notin> vars P"
    have *: "prob_space.prob (Pi_pmf V 0 (\<lambda>i. pmf_of_set S)) {f. insertion f P = 0} \<le> real d / card S "
      by (smt (verit) Collect_cong Diff_insert2 Diff_insert_absorb \<open>x \<notin> vars P\<close> diff_shunt_var insert.IH insert.prems(3) insert_Diff_single local.insert(2) local.insert(4) local.insert(5) subset_insertI)
 
    have inser: "Pi_pmf V 0 (\<lambda>i. pmf_of_set S) =
      map_pmf (\<lambda>f. f(x := 0)) ((Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)))"
      by (metis Diff_insert_absorb Pi_pmf_remove finite_insert local.insert(1) local.insert(2) local.insert(6) )

    have f_aux: "insertion (f(x := 0)) P = 0 \<longleftrightarrow> insertion f P = 0" for f
      by (metis x array_rules(4) insertion_irrelevant_vars)
    have f: "(\<lambda>f. f(x := 0))-`{f. insertion f P = 0 \<and> f x = 0} = {f. insertion f P = 0}"
      by (simp add: f_aux)
    
    have "prob_space.prob ((Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)))
      {f. insertion f P = 0} = prob_space.prob (Pi_pmf V 0 (\<lambda>i. pmf_of_set S)) {f. insertion f P = 0 }"
      using inser f by fastforce
    moreover have "... \<le> real d / card S"
      by (simp add: *)
    ultimately have ?case
      by linarith
  }
  moreover {
    assume x: "x \<in> vars P"
    define px where "px = mpoly_to_mpoly_poly x P"
    define q where "q = Polynomial.lead_coeff px" 

    have xnV: "x \<notin> V"
      by (simp add: local.insert(2))

    have split: "{f. insertion f P = 0} \<subseteq>
      {f. insertion f q = 0} \<union>
      {f. insertion f q \<noteq> 0 \<and> insertion f P = 0}" (is "_ \<subseteq> ?E2 \<union> ?E12") by blast

    obtain l where l: "MPoly_Type.degree P x = l"  by simp

    have ld: "l \<le> d"
      using l degree_le_total_degree le_trans local.insert(4) by blast
    
    (* Prove Pr(?E2) \<le> (d - l) / |S| *)

    have varq: "vars q \<subseteq> V"
      by (metis x dual_order.trans insert.prems(3) px_def q_def subset_insert_iff vars_coeff_mpoly_to_mpoly_poly)

    have dl: "degree (mpoly_to_mpoly_poly x P) = l"
      by (simp add: l)
    have qnz: "q \<noteq> 0"            
      unfolding q_def
      by (metis degree_0 degree_eq_0_iff dl l leading_coeff_neq_0 px_def x)
                      
    have "total_degree P \<ge>
        degree (mpoly_to_mpoly_poly x P) +
        total_degree (Polynomial.lead_coeff (mpoly_to_mpoly_poly x P))"
      by (metis Groups.add_ac(2) px_def q_def qnz total_degree_coeff_mpoly_to_mpoly_poly)

    then have tdq: "total_degree q \<le> d-l"
      using local.insert(4) px_def q_def dl by force

    from insert.IH[OF tdq qnz varq]
    have *: "measure_pmf.prob (Pi_pmf V 0 (\<lambda>i. pmf_of_set S)) {f. insertion f q = 0} \<le> real (d-l) /real (card S)" by auto

    have inser: "Pi_pmf V 0 (\<lambda>i. pmf_of_set S) =
      map_pmf (\<lambda>f. f(x := 0)) ((Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)))"
      by (metis Diff_insert_absorb Pi_pmf_remove finite_insert local.insert(1) local.insert(2) local.insert(6) )

    have aux: "insertion (f(x := 0)) q = 0 \<longleftrightarrow> insertion f q = 0" for f
      by  (metis \<open>vars q \<subseteq> V\<close> array_rules(4) insertion_irrelevant_vars local.insert(2) subsetD)
    have "(\<lambda>f. f(x := 0))-`{f. insertion f q = 0 \<and> f x = 0} = {f. insertion f q = 0}"
      by (simp add: aux)
  
    then have "prob_space.prob (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)) {f. insertion f q = 0} =
      prob_space.prob (map_pmf (\<lambda>f. f(x := 0)) (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S))) {f. insertion f q = 0 \<and> f x = 0}"
      using local.insert(6) by force
    moreover have "... = prob_space.prob (Pi_pmf V 0 (\<lambda>i. pmf_of_set S)) {f. insertion f q = 0 }"
      using inser by fastforce
    
    ultimately have e2: "measure_pmf.prob (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)) ?E2 \<le> (d - l) / card S"
      using * by presburger
      
    have ib: "prob_space.prob (pmf_of_set S) {r. poly (map_poly (insertion f) px) r = 0}
                \<le> real l / real (card S)" if "insertion f q \<noteq> 0" for f
    proof (rule schwartz_zippel_uni[OF S])
      show "Polynomial.degree (map_poly (insertion f) px) \<le> l"
        unfolding px_def using that dl degree_map_poly_le by blast
      show "map_poly (insertion f) px \<noteq> 0"
        by (metis Ring_Hom_Poly.degree_map_poly degree_0 degree_eq_0_iff dl l px_def q_def that x)
    qed

    have insertion_upd: "insertion (f(x := r)) q = insertion f q" for f r
      by (metis array_rules(4) insertion_irrelevant_vars local.insert(2) subsetD varq)

    then have *: "{y. insertion ((fst y)(x := snd y)) q \<noteq> 0 \<and>
           insertion ((fst y)(x := snd y)) P = 0} =
      Sigma {f. insertion f q \<noteq> 0} (\<lambda>f. {r. insertion (f(x := r)) P = 0})"
      by auto

    have "measure_pmf.prob (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)) ?E12 =
            measure_pmf.prob (pair_pmf (Pi_pmf V 0 (\<lambda>i. pmf_of_set S)) (pmf_of_set S))
              ((\<lambda>(f, y). f(x := y)) -` {f. insertion f q \<noteq> 0 \<and> insertion f P = 0})"
      by (subst Pi_pmf_insert)
         (use xnV insert in \<open>auto simp add: pair_commute_pmf[of "pmf_of_set S"] 
                               case_prod_unfold * px_def insertion_update[symmetric]\<close>)
    also have "(\<lambda>(f, y). f(x := y)) -` {f. insertion f q \<noteq> 0 \<and> insertion f P = 0} =
               Sigma {f. insertion f q \<noteq> 0} (\<lambda>f. {r. poly (map_poly (insertion f) px) r = 0})"
      by (auto simp: Sigma_def case_prod_unfold insertion_upd px_def simp flip: insertion_update)

    also have "measure_pmf.prob (pair_pmf (Pi_pmf V 0 (\<lambda>i. pmf_of_set S)) (pmf_of_set S)) ... \<le>
      measure_pmf.prob (Pi_pmf V 0 (\<lambda>i. pmf_of_set S)) {f. insertion f q \<noteq> 0} *
       (real l / real (card S))"
      by (intro measure_pmf_prob_dependent_product_bound') (auto simp: ib measure_Int_set_pmf)
    also have "... \<le> real l / real (card S)"
      by (intro mult_left_le_one_le) auto
    finally have e12: "measure_pmf.prob (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)) ?E12 \<le> l / card S" .

    have "measure_pmf.prob (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)) {f. insertion f P = 0} \<le>
      measure_pmf.prob (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)) ({f. insertion f q = 0} \<union> {f. insertion f q \<noteq> 0 \<and> insertion f P = 0})"
      by (intro measure_pmf.finite_measure_mono) (use split in auto)

    moreover have " ... \<le> 
      measure_pmf.prob (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)) ?E2 +
      measure_pmf.prob (Pi_pmf (insert x V) 0 (\<lambda>i. pmf_of_set S)) ?E12"
      by (auto intro!: measure_pmf.finite_measure_subadditive)
    moreover have "... \<le> (d-l) / card S + l / card S"
      using e2 e12 by auto
    
    moreover have "... \<le> real d / card S"
      by (simp add: ld diff_divide_distrib of_nat_diff)
       
    ultimately have ?case
      by linarith
  }
  ultimately show ?case by auto
qed

end
