section \<open>Frequency Moment $k$\<close>

theory Frequency_Moment_k
  imports 
    Frequency_Moments
    Landau_Ext 
    Lp.Lp
    Median_Method.Median
    Product_PMF_Ext 
begin

text \<open>This section contains a formalization of the algorithm for the $k$-th frequency moment.
It is based on the algorithm described in \<^cite>\<open>\<open>\textsection 2.1\<close> in "alon1999"\<close>.\<close>

type_synonym fk_state = "nat \<times> nat \<times> nat \<times> nat \<times> (nat \<times> nat \<Rightarrow> (nat \<times> nat))"

fun fk_init :: "nat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> fk_state pmf" where
  "fk_init k \<delta> \<epsilon> n =
    do {
      let s\<^sub>1 = nat \<lceil>3 * real k * n powr (1-1/real k) / (real_of_rat \<delta>)\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-18 * ln (real_of_rat \<epsilon>)\<rceil>;
      return_pmf (s\<^sub>1, s\<^sub>2, k, 0, (\<lambda>_ \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (0,0)))
    }"

fun fk_update :: "nat \<Rightarrow> fk_state \<Rightarrow> fk_state pmf" where
  "fk_update a (s\<^sub>1, s\<^sub>2, k, m, r) = 
    do {
      coins \<leftarrow> prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. bernoulli_pmf (1/(real m+1)));
      return_pmf (s\<^sub>1, s\<^sub>2, k, m+1, \<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
        if coins i then 
          (a,0) 
        else (
          let (x,l) = r i in (x, l + of_bool (x=a))
        )
      )
    }"

fun fk_result :: "fk_state \<Rightarrow> rat pmf" where
  "fk_result (s\<^sub>1, s\<^sub>2, k, m, r) = 
    return_pmf (median s\<^sub>2 (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}.
      (\<Sum>i\<^sub>1\<in>{0..<s\<^sub>1}. rat_of_nat (let t = snd (r (i\<^sub>1, i\<^sub>2)) + 1 in m * (t^k - (t - 1)^k))) / (rat_of_nat s\<^sub>1))
    )"

lemma bernoulli_pmf_1: "bernoulli_pmf 1 = return_pmf True"
  by (rule pmf_eqI, simp add:indicator_def)

fun fk_space_usage :: "(nat \<times> nat \<times> nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "fk_space_usage (k, n, m, \<epsilon>, \<delta>) = (
    let s\<^sub>1 = nat \<lceil>3*real k* (real n) powr (1-1/ real k) / (real_of_rat \<delta>)\<^sup>2 \<rceil> in
    let s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil> in 
    4 +
    2 * log 2 (s\<^sub>1 + 1) +
    2 * log 2 (s\<^sub>2 + 1) +
    2 * log 2 (real k + 1) +
    2 * log 2 (real m + 1) +
    s\<^sub>1 * s\<^sub>2 * (2 + 2 * log 2 (real n+1) + 2 * log 2 (real m+1)))"

definition encode_fk_state :: "fk_state \<Rightarrow> bool list option" where
  "encode_fk_state = 
    N\<^sub>e \<Join>\<^sub>e (\<lambda>s\<^sub>1. 
    N\<^sub>e \<Join>\<^sub>e (\<lambda>s\<^sub>2. 
    N\<^sub>e \<times>\<^sub>e  
    N\<^sub>e \<times>\<^sub>e  
    (List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e (N\<^sub>e \<times>\<^sub>e N\<^sub>e))))"

lemma "inj_on encode_fk_state (dom encode_fk_state)"
proof -
  have "is_encoding encode_fk_state"
    by (simp add:encode_fk_state_def)
     (intro dependent_encoding exp_golomb_encoding fun_encoding)

  thus ?thesis by (rule encoding_imp_inj)
qed

text \<open>This is an intermediate non-parallel form @{term "fk_update"} used only in the correctness proof.\<close>

fun fk_update_2 :: "'a \<Rightarrow> (nat \<times> 'a \<times> nat) \<Rightarrow> (nat \<times> 'a \<times> nat) pmf" where
  "fk_update_2 a (m,x,l) = 
    do {
      coin \<leftarrow> bernoulli_pmf (1/(real m+1));
      return_pmf (m+1,if coin then (a,0) else (x, l + of_bool (x=a)))
    }"

definition sketch where "sketch as i = (as ! i, count_list (drop (i+1) as) (as ! i))"

lemma fk_update_2_distr:
  assumes "as \<noteq> []"
  shows "fold (\<lambda>x s. s \<bind> fk_update_2 x) as (return_pmf (0,0,0)) =
  pmf_of_set {..<length as} \<bind> (\<lambda>k. return_pmf (length as, sketch as k))"
  using assms
proof (induction as rule:rev_nonempty_induct)
  case (single x)
  show ?case using single 
    by (simp add:bind_return_pmf pmf_of_set_singleton bernoulli_pmf_1 lessThan_def sketch_def) 
next
  case (snoc x xs)
  let ?h = "(\<lambda>xs k. count_list (drop (Suc k) xs) (xs ! k))"
  let ?q = "(\<lambda>xs k. (length xs, sketch xs k))"

  have non_empty: " {..<Suc (length xs)} \<noteq> {}" " {..<length xs} \<noteq> {}" using snoc by auto

  have fk_update_2_eta:"fk_update_2 x = (\<lambda>a. fk_update_2 x (fst a, fst (snd a), snd (snd a)))" 
    by auto

  have "pmf_of_set {..<length xs} \<bind> (\<lambda>k. bernoulli_pmf (1 / (real (length xs) + 1)) \<bind>
    (\<lambda>coin. return_pmf (if coin then length xs else k))) = 
    bernoulli_pmf (1 / (real (length xs) + 1)) \<bind> (\<lambda>y. pmf_of_set {..<length xs} \<bind>
      (\<lambda>k. return_pmf (if y then length xs else k)))"
    by (subst bind_commute_pmf, simp)
  also have "... = pmf_of_set {..<length xs + 1}"
    using snoc(1) non_empty
    by (intro pmf_eqI, simp add: pmf_bind measure_pmf_of_set)
     (simp add:indicator_def algebra_simps frac_eq_eq)
  finally have b: "pmf_of_set {..<length xs} \<bind> (\<lambda>k. bernoulli_pmf (1 / (real (length xs) + 1)) \<bind>
    (\<lambda>coin. return_pmf (if coin then length xs else k))) = pmf_of_set {..<length xs +1}" by simp
   
  have "fold (\<lambda>x s. (s \<bind> fk_update_2 x)) (xs@[x]) (return_pmf (0,0,0)) =
    (pmf_of_set {..<length xs} \<bind> (\<lambda>k. return_pmf (length xs, sketch xs k))) \<bind> fk_update_2 x"
    using snoc by (simp add:case_prod_beta')
  also have "... = (pmf_of_set {..<length xs} \<bind> (\<lambda>k. return_pmf (length xs, sketch xs k))) \<bind> 
    (\<lambda>(m,a,l). bernoulli_pmf (1 / (real m + 1)) \<bind> (\<lambda>coin. 
    return_pmf (m + 1, if coin then (x, 0) else (a, (l + of_bool (a = x))))))"
    by (subst fk_update_2_eta, subst fk_update_2.simps, simp add:case_prod_beta')
  also have "... = pmf_of_set {..<length xs} \<bind> (\<lambda>k. bernoulli_pmf (1 / (real (length xs) + 1)) \<bind>
    (\<lambda>coin. return_pmf (length xs + 1, if coin then (x, 0) else (xs ! k, ?h xs k + of_bool (xs ! k = x)))))"
    by (subst bind_assoc_pmf, simp add: bind_return_pmf sketch_def)
  also have "... = pmf_of_set {..<length xs} \<bind> (\<lambda>k. bernoulli_pmf (1 / (real (length xs) + 1)) \<bind>
    (\<lambda>coin. return_pmf (if coin then length xs else k) \<bind> (\<lambda>k'. return_pmf (?q (xs@[x]) k'))))"
    using non_empty
    by (intro bind_pmf_cong, auto simp add:bind_return_pmf nth_append count_list_append sketch_def)
  also have "... = pmf_of_set {..<length xs} \<bind> (\<lambda>k. bernoulli_pmf (1 / (real (length xs) + 1)) \<bind>
    (\<lambda>coin. return_pmf (if coin then length xs else k))) \<bind> (\<lambda>k'. return_pmf (?q (xs@[x]) k'))"
    by (subst bind_assoc_pmf, subst bind_assoc_pmf, simp)
  also have "... = pmf_of_set {..<length (xs@[x])} \<bind> (\<lambda>k'. return_pmf (?q (xs@[x]) k'))"
    by (subst b, simp)
  finally show ?case by simp
qed

context
  fixes \<epsilon> \<delta> :: rat
  fixes n k :: nat
  fixes as
  assumes k_ge_1: "k \<ge> 1"
  assumes \<epsilon>_range: "\<epsilon> \<in> {0<..<1}"
  assumes \<delta>_range: "\<delta> > 0"
  assumes as_range: "set as \<subseteq> {..<n}"
begin

definition s\<^sub>1 where "s\<^sub>1 = nat \<lceil>3 * real k * (real n) powr (1-1/real k) / (real_of_rat \<delta>)\<^sup>2\<rceil>"
definition s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>"

definition "M\<^sub>1 = {(u, v). v < count_list as u}"
definition "\<Omega>\<^sub>1 = measure_pmf (pmf_of_set M\<^sub>1)"

definition "M\<^sub>2 = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set M\<^sub>1)"
definition "\<Omega>\<^sub>2 = measure_pmf M\<^sub>2"

interpretation prob_space "\<Omega>\<^sub>1"
  unfolding \<Omega>\<^sub>1_def by (simp add:prob_space_measure_pmf)

interpretation \<Omega>\<^sub>2:prob_space "\<Omega>\<^sub>2"
  unfolding \<Omega>\<^sub>2_def by (simp add:prob_space_measure_pmf)

lemma split_space: "(\<Sum>a\<in>M\<^sub>1. f (snd a)) = (\<Sum>u \<in> set as. (\<Sum>v \<in>{0..<count_list as u}. f v))"
proof -
  define A where "A = (\<lambda>u. {u} \<times> {v. v < count_list as u})"

  have a: "inj_on snd (A x)" for x 
    by (simp add:A_def inj_on_def) 

  have "\<And>u v. u < count_list as v \<Longrightarrow> v \<in> set as"
    by (subst count_list_gr_1, force)
  hence "M\<^sub>1 = \<Union> (A ` set as)"
    by (auto simp add:set_eq_iff A_def M\<^sub>1_def)
  hence "(\<Sum>a\<in>M\<^sub>1. f (snd a)) = sum (f \<circ> snd)  (\<Union> (A ` set as))"
    by (intro sum.cong, auto)
  also have "... = sum (\<lambda>x. sum (f \<circ> snd) (A x)) (set as)"
    by (rule sum.UNION_disjoint, simp, simp add:A_def, simp add:A_def, blast) 
  also have "... = sum (\<lambda>x. sum f (snd ` A x)) (set as)"
    by (intro sum.cong, auto simp add:sum.reindex[OF a])
  also have "... = (\<Sum>u \<in> set as. (\<Sum>v \<in>{0..<count_list as u}. f v))"
    unfolding A_def by (intro sum.cong, auto)
  finally show ?thesis by blast
qed

lemma
  assumes "as \<noteq> []"
  shows fin_space: "finite M\<^sub>1" 
    and non_empty_space: "M\<^sub>1 \<noteq> {}"
    and card_space: "card M\<^sub>1 = length as"
proof -
  have "M\<^sub>1 \<subseteq> set as \<times> {k. k < length as}"
  proof (rule subsetI)
    fix x
    assume a:"x \<in> M\<^sub>1"
    have "fst x \<in> set as"
      using a by (simp add:case_prod_beta count_list_gr_1 M\<^sub>1_def)
    moreover have "snd x < length as"
      using a count_le_length order_less_le_trans
      by (simp add:case_prod_beta M\<^sub>1_def) fast
    ultimately show "x \<in> set as \<times> {k. k < length as}"
      by (simp add:mem_Times_iff)
  qed
  thus fin_space: "finite M\<^sub>1"
    using finite_subset by blast

  have "(as ! 0, 0) \<in> M\<^sub>1" 
    using assms(1) unfolding M\<^sub>1_def
    by (simp, metis count_list_gr_1 gr0I length_greater_0_conv not_one_le_zero nth_mem)
  thus "M\<^sub>1 \<noteq> {}" by blast

  show "card M\<^sub>1 = length as"
    using fin_space split_space[where f="\<lambda>_. (1::nat)"]
    by (simp add:sum_count_set[where X="set as" and xs="as", simplified])
qed

lemma
  assumes "as \<noteq> []"
  shows integrable_1: "integrable \<Omega>\<^sub>1 (f :: _ \<Rightarrow> real)" and
    integrable_2: "integrable \<Omega>\<^sub>2 (g :: _ \<Rightarrow> real)"
proof -
  have fin_omega: "finite (set_pmf (pmf_of_set M\<^sub>1))"
    using fin_space[OF assms] non_empty_space[OF assms] by auto
  thus "integrable \<Omega>\<^sub>1 f"
    unfolding \<Omega>\<^sub>1_def
    by (rule integrable_measure_pmf_finite)

  have "finite (set_pmf M\<^sub>2)"
    unfolding M\<^sub>2_def using fin_omega
    by (subst set_prod_pmf) (auto intro:finite_PiE)

  thus "integrable \<Omega>\<^sub>2 g"
    unfolding \<Omega>\<^sub>2_def by (intro integrable_measure_pmf_finite)
qed

lemma sketch_distr:
  assumes "as \<noteq> []"
  shows "pmf_of_set {..<length as} \<bind> (\<lambda>k. return_pmf (sketch as k)) = pmf_of_set M\<^sub>1"
proof -
  have "x < y \<Longrightarrow> y < length as \<Longrightarrow> 
    count_list (drop (y+1) as) (as ! y) < count_list (drop (x+1) as) (as ! y)" for x y
    by (intro count_list_lt_suffix suffix_drop_drop, simp_all)
     (metis Suc_diff_Suc diff_Suc_Suc diff_add_inverse lessI less_natE)
  hence a1: "inj_on (sketch as) {k. k < length as}"
    unfolding sketch_def by (intro inj_onI) (metis Pair_inject mem_Collect_eq nat_neq_iff)

  have "x < length as \<Longrightarrow> count_list (drop (x+1) as) (as ! x) < count_list as (as ! x)" for x
    by (rule count_list_lt_suffix, auto simp add:suffix_drop)
  hence "sketch as ` {k. k < length as} \<subseteq> M\<^sub>1"
    by (intro image_subsetI, simp add:sketch_def M\<^sub>1_def)
  moreover have "card M\<^sub>1 \<le> card (sketch as ` {k. k < length as})"
    by (simp add: card_space[OF assms(1)] card_image[OF a1])
  ultimately have "sketch as ` {k. k < length as} = M\<^sub>1"
    using fin_space[OF assms(1)] by (intro card_seteq, simp_all)
  hence "bij_betw (sketch as) {k. k < length as} M\<^sub>1"
    using a1 by (simp add:bij_betw_def)
  hence "map_pmf (sketch as) (pmf_of_set {k. k < length as}) = pmf_of_set M\<^sub>1"
    using assms by (intro map_pmf_of_set_bij_betw, auto)
  thus ?thesis by (simp add: sketch_def map_pmf_def lessThan_def)
qed

lemma fk_update_distr:
  "fold (\<lambda>x s. s \<bind> fk_update x) as (fk_init k \<delta> \<epsilon> n) = 
  prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. fold (\<lambda>x s. s \<bind> fk_update_2 x) as (return_pmf (0,0,0))) 
    \<bind> (\<lambda>x. return_pmf (s\<^sub>1,s\<^sub>2,k, length as, \<lambda>i\<in>{0..<s\<^sub>1}\<times>{0..<s\<^sub>2}. snd (x i)))"
proof (induction as rule:rev_induct)
  case Nil
  then show ?case 
    by (auto simp:Let_def s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] bind_return_pmf)
next
  case (snoc x xs)

  have fk_update_2_eta:"fk_update_2 x = (\<lambda>a. fk_update_2 x (fst a, fst (snd a), snd (snd a)))" 
    by auto

  have a: "fk_update x (s\<^sub>1, s\<^sub>2, k, length xs, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. snd (f i)) =
    prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>i. fk_update_2 x (f i)) \<bind> 
    (\<lambda>a. return_pmf (s\<^sub>1,s\<^sub>2, k, Suc (length xs), \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. snd (a i)))"
    if b: "f \<in> set_pmf (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) 
                  (\<lambda>_. fold (\<lambda>a s. s \<bind> fk_update_2 a) xs (return_pmf (0, 0, 0))))" for f
  proof -
    have c:"fst (f i) = length xs" if d:"i \<in> {0..<s\<^sub>1} \<times>{0..<s\<^sub>2}" for i
    proof (cases "xs = []")
      case True
      then show ?thesis using b d by (simp add: set_Pi_pmf)
    next  
      case False
      hence "{..<length xs} \<noteq> {}" by force
      thus ?thesis using b d 
        by (simp add:set_Pi_pmf fk_update_2_distr[OF False] PiE_dflt_def) force
    qed
    show ?thesis
      apply (subst fk_update_2_eta, subst fk_update_2.simps, simp)
      apply (simp add: Pi_pmf_bind_return[where d'="undefined"] bind_assoc_pmf)
      apply (rule bind_pmf_cong, simp add:c cong:Pi_pmf_cong)
      by (auto simp add:bind_return_pmf case_prod_beta)
  qed
 
  have "fold (\<lambda>x s. s \<bind> fk_update x) (xs @ [x]) (fk_init k \<delta> \<epsilon> n) = 
     prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. fold (\<lambda>x s. s \<bind> fk_update_2 x) xs (return_pmf (0,0,0))) 
    \<bind> (\<lambda>\<omega>. return_pmf (s\<^sub>1,s\<^sub>2,k, length xs, \<lambda>i\<in>{0..<s\<^sub>1}\<times>{0..<s\<^sub>2}. snd (\<omega> i)) \<bind> fk_update x)"
    using snoc
    by (simp add:restrict_def bind_assoc_pmf del:fk_init.simps)
  also have "... =  prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) 
    (\<lambda>_. fold (\<lambda>a s. s \<bind> fk_update_2 a) xs (return_pmf (0, 0, 0))) \<bind>
    (\<lambda>f. prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>i. fk_update_2 x (f i)) \<bind>
    (\<lambda>a. return_pmf (s\<^sub>1, s\<^sub>2, k, Suc (length xs), \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. snd (a i))))"
    using a
    by (intro bind_pmf_cong, simp_all add:bind_return_pmf del:fk_update.simps)
  also have "... =  prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) 
    (\<lambda>_. fold (\<lambda>a s. s \<bind> fk_update_2 a) xs (return_pmf (0, 0, 0))) \<bind>
    (\<lambda>f. prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>i. fk_update_2 x (f i))) \<bind>
    (\<lambda>a. return_pmf (s\<^sub>1, s\<^sub>2, k, Suc (length xs), \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. snd (a i)))"
    by (simp add:bind_assoc_pmf)
  also have "... = (prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) 
    (\<lambda>_. fold (\<lambda>a s. s \<bind> fk_update_2 a) (xs@[x]) (return_pmf (0,0,0))) 
    \<bind> (\<lambda>a. return_pmf (s\<^sub>1,s\<^sub>2,k, length (xs@[x]), \<lambda>i\<in>{0..<s\<^sub>1}\<times>{0..<s\<^sub>2}. snd (a i))))"
    by (simp, subst Pi_pmf_bind, auto)

  finally show ?case by blast
qed

lemma power_diff_sum:
  fixes a b :: "'a :: {comm_ring_1,power}"
  assumes "k > 0"
  shows "a^k - b^k = (a-b) * (\<Sum>i = 0..<k. a ^ i * b ^ (k - 1 - i))" (is "?lhs = ?rhs")
proof -
  have insert_lb: "m < n \<Longrightarrow> insert m {Suc m..<n} = {m..<n}" for m n :: nat
    by auto

  have "?rhs = sum (\<lambda>i. a * (a^i * b^(k-1-i))) {0..<k} - 
    sum (\<lambda>i. b * (a^i * b^(k-1-i))) {0..<k}"
    by (simp add: sum_distrib_left[symmetric] algebra_simps)
  also have "... = sum ((\<lambda>i. (a^i * b^(k-i))) \<circ> (\<lambda>i. i+1)) {0..<k} - 
    sum (\<lambda>i. (a^i * (b^(1+(k-1-i))))) {0..<k}"
    by (simp add:algebra_simps)
  also have "... = sum ((\<lambda>i. (a^i * b^(k-i))) \<circ> (\<lambda>i. i+1)) {0..<k} - 
    sum (\<lambda>i. (a^i * b^(k-i))) {0..<k}"
    by (intro arg_cong2[where f="(-)"] sum.cong arg_cong2[where f="(*)"] 
        arg_cong2[where f="(\<lambda>x y. x ^ y)"]) auto
  also have "... = sum (\<lambda>i. (a^i * b^(k-i))) (insert k {1..<k}) - 
    sum (\<lambda>i. (a^i * b^(k-i))) (insert 0 {Suc 0..<k})"
    using assms
    by (subst sum.reindex[symmetric], simp, subst insert_lb, auto)
  also have "... = ?lhs"
    by simp
  finally show ?thesis by presburger
qed

lemma power_diff_est:
  assumes "k > 0"
  assumes "(a :: real) \<ge> b"
  assumes "b \<ge> 0"
  shows "a^k -b^k \<le> (a-b) * k * a^(k-1)"
proof -
  have " \<And>i. i < k \<Longrightarrow> a ^ i * b ^ (k - 1 - i) \<le> a ^ i * a ^ (k-1-i)"
    using assms by (intro mult_left_mono power_mono) auto
  also have "\<And>i. i < k \<Longrightarrow> a ^ i * a ^ (k - 1 - i) = a ^ (k - Suc 0)"
    using assms(1) by (subst power_add[symmetric], simp)
  finally have a: "\<And>i. i < k \<Longrightarrow> a ^ i * b ^ (k - 1 - i) \<le> a ^ (k - Suc 0)"
    by blast
  have "a^k - b^k = (a-b) * (\<Sum>i = 0..<k. a ^ i * b ^ (k - 1 - i))"
    by (rule power_diff_sum[OF assms(1)])
  also have "... \<le> (a-b) * (\<Sum>i = 0..<k.  a^(k-1))"
    using a assms by (intro mult_left_mono sum_mono, auto)
  also have "... = (a-b) * (k * a^(k-Suc 0))"
    by simp
  finally show ?thesis by simp
qed

text \<open>Specialization of the Hoelder inquality for sums.\<close>
lemma Holder_inequality_sum:
  assumes "p > (0::real)" "q > 0" "1/p + 1/q = 1"
  assumes "finite A"
  shows "\<bar>\<Sum>x\<in>A. f x * g x\<bar> \<le> (\<Sum>x\<in>A. \<bar>f x\<bar> powr p) powr (1/p) * (\<Sum>x\<in>A. \<bar>g x\<bar> powr q) powr (1/q)"
proof -
  have "\<bar>LINT x|count_space A. f x * g x\<bar> \<le> 
    (LINT x|count_space A. \<bar>f x\<bar> powr p) powr (1 / p) * 
    (LINT x|count_space A. \<bar>g x\<bar> powr q) powr (1 / q)"
    using assms integrable_count_space
    by (intro Lp.Holder_inequality, auto)
  thus ?thesis
    using assms by (simp add: lebesgue_integral_count_space_finite[symmetric])
qed

lemma real_count_list_pos:
  assumes "x \<in> set as"
  shows "real (count_list as x) > 0"
  using count_list_gr_1 assms by force

lemma fk_estimate:
  assumes "as \<noteq> []"
  shows "length as * of_rat (F (2*k-1) as) \<le> n powr (1 - 1 / real k) * (of_rat (F k as))^2"
  (is "?lhs \<le> ?rhs")
proof (cases "k \<ge> 2")
  case True
  define M where "M = Max (count_list as ` set as)" 
  have "M \<in> count_list as ` set as"
    unfolding M_def using assms by (intro Max_in, auto)
  then obtain m where m_in: "m \<in> set as" and m_def: "M = count_list as m"
    by blast

  have a: "real M > 0" using m_in count_list_gr_1 by (simp add:m_def, force)
  have b: "2*k-1 = (k-1) + k" by simp

  have " 0 < real (count_list as m)" 
    using m_in count_list_gr_1 by force
  hence "M powr k = real (count_list as m) ^ k"
    by (simp add: powr_realpow m_def)
  also have "... \<le> (\<Sum>x\<in>set as. real (count_list as x) ^ k)"
    using m_in by (intro member_le_sum, simp_all)
  also have "... \<le> real_of_rat (F k as)"
    by (simp add:F_def of_rat_sum of_rat_power)
  finally have d: "M powr k \<le> real_of_rat (F k as)" by simp

  have e: "0 \<le> real_of_rat (F k as)" 
    using F_gr_0[OF assms(1)] by (simp add: order_le_less)

  have "real (k - 1) / real k + 1 = real (k - 1) / real k + real k / real k"
    using assms True by simp
  also have "... =  real (2 * k - 1) / real k"
    using b by (subst add_divide_distrib[symmetric], force)
  finally have f: "real (k - 1) / real k + 1 = real (2 * k - 1) / real k"
    by blast

  have "real_of_rat (F (2*k-1) as) = 
    (\<Sum>x\<in>set as. real (count_list as x) ^ (k - 1) * real (count_list as x) ^ k)" 
    using b by (simp add:F_def of_rat_sum sum_distrib_left of_rat_mult power_add of_rat_power)
  also have "... \<le> (\<Sum>x\<in>set as. real M ^ (k - 1) * real (count_list as x) ^ k)"
    by (intro sum_mono mult_right_mono power_mono of_nat_mono) (auto simp:M_def)
  also have "... = M powr (k-1) * of_rat (F k as)" using a
    by (simp add:sum_distrib_left F_def of_rat_mult of_rat_sum of_rat_power powr_realpow)
  also have "... = (M powr k) powr (real (k - 1) / real k) * of_rat (F k as) powr 1"
    using e by (simp add:powr_powr)
  also have "... \<le>  (real_of_rat (F k as)) powr ((k-1)/k) * (real_of_rat (F k as) powr 1)"
    using d by (intro mult_right_mono powr_mono2, auto)
  also have "... = (real_of_rat (F k as)) powr ((2*k-1) / k)"
    by (subst powr_add[symmetric], subst f, simp)
  finally have a: "real_of_rat (F (2*k-1) as) \<le> (real_of_rat (F k as)) powr ((2*k-1) / k)"
    by blast

  have g: "card (set as) \<le> n"
    using card_mono[OF _ as_range] by simp

  have "length as = abs (sum (\<lambda>x. real (count_list as x)) (set as))"
    by (subst of_nat_sum[symmetric], simp add: sum_count_set)
  also have "... \<le> card (set as) powr ((k-Suc 0)/k) * 
    (sum (\<lambda>x. \<bar>real (count_list as x)\<bar> powr k) (set as)) powr (1/k)"
    using assms True
    by (intro Holder_inequality_sum[where p="k/(k-1)" and q="k" and f="\<lambda>_.1", simplified])
     (auto simp add:algebra_simps add_divide_distrib[symmetric])
  also have "... = (card (set as)) powr ((k-1) / real k) * of_rat (F k as) powr (1/ k)"
    using real_count_list_pos
    by (simp add:F_def of_rat_sum of_rat_power powr_realpow)
  also have "... = (card (set as)) powr (1 - 1 / real k) * of_rat (F k as) powr (1/ k)"
    using k_ge_1
    by (subst of_nat_diff[OF k_ge_1], subst diff_divide_distrib, simp)
  also have "... \<le> n powr (1 - 1 / real k) * of_rat (F k as) powr (1/ k)"
    using k_ge_1 g
    by (intro mult_right_mono powr_mono2, auto)
  finally have h: "length as \<le> n powr (1 - 1 / real k) * of_rat (F k as) powr (1/real k)"
    by blast

  have i:"1 / real k + real (2 * k - 1) / real k = real 2"
    using True by (subst add_divide_distrib[symmetric], simp_all add:of_nat_diff)

  have "?lhs \<le> n powr (1 - 1/k) * of_rat (F k as) powr (1/k) * (of_rat (F k as)) powr ((2*k-1) / k)"
    using a h F_ge_0 by (intro mult_mono mult_nonneg_nonneg, auto)
  also have "... = ?rhs"
    using i F_gr_0[OF assms] by (simp add:powr_add[symmetric] powr_realpow[symmetric])
  finally show ?thesis
    by blast
next
  case False
  have "n = 0 \<Longrightarrow> False"
    using as_range assms by auto
  hence "n > 0" 
    by auto
  moreover have "k = 1"
    using assms k_ge_1 False by linarith
  moreover have "length as = real_of_rat (F (Suc 0) as)"
    by (simp add:F_def sum_count_set of_nat_sum[symmetric] del:of_nat_sum)
  ultimately show ?thesis
    by (simp add:power2_eq_square)
qed

definition result
  where "result a = of_nat (length as) * of_nat (Suc (snd a) ^ k - snd a ^ k)"

lemma result_exp_1:
  assumes "as \<noteq> []"
  shows "expectation result = real_of_rat (F k as)"
proof -
  have "expectation result = (\<Sum>a\<in>M\<^sub>1. result a * pmf (pmf_of_set M\<^sub>1) a)"
    unfolding \<Omega>\<^sub>1_def using non_empty_space assms fin_space
    by (subst integral_measure_pmf_real) auto
  also have "... = (\<Sum>a\<in>M\<^sub>1. result a / real (length as))"
   using non_empty_space assms fin_space card_space by simp
  also have "... = (\<Sum>a\<in>M\<^sub>1. real (Suc (snd a) ^ k - snd a ^ k))"
    using assms by (simp add:result_def)
  also have "... = (\<Sum>u\<in>set as. \<Sum>v = 0..<count_list as u. real (Suc v ^ k) - real (v ^ k))"
    using k_ge_1 by (subst split_space, simp add:of_nat_diff)
  also have "... = (\<Sum>u\<in>set as. real (count_list as u)^k)"
    using k_ge_1 by (subst sum_Suc_diff') (auto simp add:zero_power)
  also have "... = of_rat (F k as)"
    by (simp add:F_def of_rat_sum of_rat_power)
  finally show ?thesis by simp
qed

lemma result_var_1:
  assumes "as \<noteq> []"
  shows "variance result \<le> (of_rat (F k as))\<^sup>2 * k * n powr (1 - 1 / real k)"
proof -  
  have k_gt_0: "k > 0" using k_ge_1 by linarith

  have c:"real (Suc v ^ k) - real (v ^ k) \<le> k * real (count_list as a) ^ (k - Suc 0)"
    if c_1: "v < count_list as a" for a v
  proof -
    have "real (Suc v ^ k) - real (v ^ k) \<le> (real (v+1) - real v) * k * (1 + real v) ^ (k - Suc 0)"
      using k_gt_0 power_diff_est[where a="Suc v" and b="v"] by simp
    moreover have "(real (v+1) - real v) = 1" by auto
    ultimately have "real (Suc v ^ k) - real (v ^ k) \<le> k * (1 + real v) ^ (k - Suc 0)"
      by auto
    also have "... \<le> k * real (count_list as a) ^ (k- Suc 0)"
      using c_1 by (intro mult_left_mono power_mono, auto)
    finally show ?thesis by blast
  qed
      
  have "length as * (\<Sum>a\<in> M\<^sub>1. (real (Suc (snd a)  ^ k - (snd a) ^ k))\<^sup>2) =
    length as * (\<Sum>a\<in> set as. (\<Sum>v \<in> {0..<count_list as a}. 
    real (Suc v ^ k - v ^ k) * real (Suc v ^ k - v^k)))"
    by (subst split_space, simp add:power2_eq_square)
  also have "... \<le> length as * (\<Sum>a\<in> set as. (\<Sum>v \<in> {0..<count_list as a}. 
    k * real (count_list as a) ^ (k-1) * real (Suc v ^ k - v ^ k)))"
    using c by (intro mult_left_mono sum_mono mult_right_mono) (auto simp:power_mono of_nat_diff)
  also have "... = length as * k * (\<Sum>a\<in> set as. real (count_list as a) ^ (k-1) * 
    (\<Sum>v \<in> {0..<count_list as a}. real (Suc v ^ k) - real (v ^ k)))"
    by (simp add:sum_distrib_left ac_simps of_nat_diff power_mono)
  also have "... = length as * k * (\<Sum>a\<in> set as. real (count_list as a ^ (2*k-1)))"
    using assms k_ge_1
    by (subst sum_Suc_diff', auto simp: zero_power[OF k_gt_0] mult_2 power_add[symmetric])
  also have "... = k * (length as * of_rat (F (2*k-1) as))"
    by (simp add:sum_distrib_left[symmetric] F_def of_rat_sum of_rat_power)
  also have "... \<le> k * (of_rat (F k as)^2 * n powr (1 - 1 / real k))"
    using fk_estimate[OF assms] by (intro mult_left_mono) (auto simp: mult.commute)
  finally have b: "real (length as) * (\<Sum>a\<in> M\<^sub>1. (real (Suc (snd a) ^ k - (snd a) ^ k))\<^sup>2) \<le> 
    k * ((of_rat (F k as))\<^sup>2 * n powr (1 - 1 / real k))"
    by blast

  have "expectation (\<lambda>\<omega>. (result \<omega> :: real)^2) - (expectation result)^2 \<le> expectation (\<lambda>\<omega>. result \<omega>^2)"
    by simp
  also have "... = (\<Sum>a\<in>M\<^sub>1. (length as * real (Suc (snd a) ^ k - snd a ^ k))\<^sup>2 * pmf (pmf_of_set M\<^sub>1) a)"
    using fin_space non_empty_space assms unfolding \<Omega>\<^sub>1_def result_def
    by (subst integral_measure_pmf_real[where A="M\<^sub>1"], auto)
  also have "... = (\<Sum>a\<in>M\<^sub>1. length as * (real (Suc (snd a) ^ k - snd a ^ k))\<^sup>2)"
    using assms non_empty_space fin_space by (subst pmf_of_set)
     (simp_all add:card_space power_mult_distrib power2_eq_square ac_simps)
  also have "... \<le> k * ((of_rat (F k as))\<^sup>2 * n powr (1 - 1 / real k))"
    using b by (simp add:sum_distrib_left[symmetric])
  also have "... = of_rat (F k as)^2 * k * n powr (1 - 1 / real k)"
    by (simp add:ac_simps)
  finally have "expectation (\<lambda>\<omega>. result \<omega>^2) - (expectation result)^2 \<le> 
    of_rat (F k as)^2 * k * n powr (1 - 1 / real k)"
    by blast

  thus ?thesis
    using integrable_1[OF assms] by (simp add:variance_eq)
qed

theorem fk_alg_sketch:
  assumes "as \<noteq> []"
  shows "fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n) = 
    map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length as, x)) M\<^sub>2" (is "?lhs = ?rhs")
proof -
  have "?lhs = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) 
    (\<lambda>_. fold (\<lambda>x s. s \<bind> fk_update_2 x) as (return_pmf (0, 0, 0))) \<bind>
    (\<lambda>x. return_pmf (s\<^sub>1, s\<^sub>2, k, length as, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. snd (x i)))"
    by (subst fk_update_distr, simp)
  also have "... = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set {..<length as} \<bind> 
    (\<lambda>k. return_pmf (length as, sketch as k))) \<bind>
    (\<lambda>x. return_pmf (s\<^sub>1, s\<^sub>2, k, length as, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. snd (x i)))"
    by (subst fk_update_2_distr[OF assms], simp)
  also have "... = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set {..<length as} \<bind> 
    (\<lambda>k. return_pmf (sketch as k)) \<bind> (\<lambda>s. return_pmf (length as, s))) \<bind>
    (\<lambda>x. return_pmf (s\<^sub>1, s\<^sub>2, k, length as, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. snd (x i)))"
    by (subst bind_assoc_pmf, subst bind_return_pmf, simp)
  also have "... = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set {..<length as} \<bind> 
    (\<lambda>k. return_pmf (sketch as k))) \<bind>
    (\<lambda>x. return_pmf (\<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (length as, x i))) \<bind>
    (\<lambda>x. return_pmf (s\<^sub>1, s\<^sub>2, k, length as, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. snd (x i)))"
    by (subst Pi_pmf_bind_return[where d'="undefined"], simp, simp add:restrict_def)
  also have "... = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set {..<length as} \<bind> 
    (\<lambda>k. return_pmf (sketch as k))) \<bind>
    (\<lambda>x. return_pmf (s\<^sub>1, s\<^sub>2, k, length as, restrict x ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})))"
    by (subst bind_assoc_pmf, simp add:bind_return_pmf cong:restrict_cong)
  also have "... = M\<^sub>2 \<bind>
    (\<lambda>x. return_pmf (s\<^sub>1, s\<^sub>2, k, length as, restrict x ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})))"
    by (subst sketch_distr[OF assms], simp add:M\<^sub>2_def)
  also have "... = M\<^sub>2 \<bind> (\<lambda>x. return_pmf (s\<^sub>1, s\<^sub>2, k, length as, x))"
    by (rule bind_pmf_cong, auto simp add:PiE_dflt_def M\<^sub>2_def set_Pi_pmf) 
  also have "... = ?rhs"
    by (simp add:map_pmf_def)
  finally show ?thesis by simp
qed

definition mean_rv 
  where "mean_rv \<omega> i\<^sub>2 = (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. result (\<omega> (i\<^sub>1, i\<^sub>2))) / of_nat s\<^sub>1"

definition median_rv 
    where "median_rv \<omega> = median s\<^sub>2 (\<lambda>i\<^sub>2. mean_rv \<omega> i\<^sub>2)"

lemma fk_alg_correct':
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n) \<bind> fk_result"
  shows "\<P>(\<omega> in measure_pmf M. \<bar>\<omega> - F k as\<bar> \<le> \<delta> * F k as) \<ge> 1 - of_rat \<epsilon>"
proof (cases "as = []")
  case True
  have a: "nat \<lceil>- (18 * ln (real_of_rat \<epsilon>))\<rceil> > 0"  using \<epsilon>_range by simp 
  show ?thesis using True \<epsilon>_range 
    by (simp add:F_def M_def bind_return_pmf median_const[OF a] Let_def)
next
  case False

  have "set as \<noteq> {}" using assms False by blast
  hence n_nonzero: "n > 0" using as_range by fastforce

  have fk_nonzero: "F k as > 0"
    using F_gr_0[OF False] by simp

  have s1_nonzero: "s\<^sub>1 > 0"
    using \<delta>_range k_ge_1 n_nonzero by (simp add:s\<^sub>1_def)
  have s2_nonzero: "s\<^sub>2 > 0"
    using \<epsilon>_range by (simp add:s\<^sub>2_def) 

  have real_of_rat_mean_rv: "\<And>x i. mean_rv x = (\<lambda>i. real_of_rat (mean_rv x i))"
    by (rule ext, simp add:of_rat_divide of_rat_sum of_rat_mult result_def mean_rv_def)
  have real_of_rat_median_rv: "\<And>x. median_rv x = real_of_rat (median_rv x)"
    unfolding median_rv_def using s2_nonzero
    by (subst real_of_rat_mean_rv, simp add: median_rat median_restrict)


  have space_\<Omega>\<^sub>2: "space \<Omega>\<^sub>2 = UNIV" by (simp add:\<Omega>\<^sub>2_def)

  have fk_result_eta: "fk_result = (\<lambda>(x,y,z,u,v). fk_result (x,y,z,u,v))" 
    by auto 

  have a:"fold (\<lambda>x state. state \<bind> fk_update x) as (fk_init k \<delta> \<epsilon> n) = 
    map_pmf (\<lambda>x. (s\<^sub>1,s\<^sub>2,k,length as, x)) M\<^sub>2"
    by (subst fk_alg_sketch[OF False]) (simp add:s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric])

  have "M =  map_pmf (\<lambda>x. (s\<^sub>1, s\<^sub>2, k, length as, x)) M\<^sub>2 \<bind> fk_result"
    by (subst M_def, subst a, simp)
  also have "... = M\<^sub>2 \<bind> return_pmf \<circ> median_rv"
    by (subst fk_result_eta)
     (auto simp add:map_pmf_def bind_assoc_pmf bind_return_pmf median_rv_def mean_rv_def comp_def 
       M\<^sub>1_def result_def median_restrict)
  finally have b: "M = M\<^sub>2 \<bind> return_pmf \<circ> median_rv"
    by simp

  have result_exp: 
    "i\<^sub>1 < s\<^sub>1 \<Longrightarrow> i\<^sub>2 < s\<^sub>2 \<Longrightarrow> \<Omega>\<^sub>2.expectation (\<lambda>x. result (x (i\<^sub>1, i\<^sub>2))) = real_of_rat (F k as)"
    for i\<^sub>1 i\<^sub>2
    unfolding \<Omega>\<^sub>2_def M\<^sub>2_def
    using integrable_1[OF False] result_exp_1[OF False]
    by (subst expectation_Pi_pmf_slice, auto simp:\<Omega>\<^sub>1_def)


  have result_var: "\<Omega>\<^sub>2.variance (\<lambda>\<omega>. result (\<omega> (i\<^sub>1, i\<^sub>2))) \<le> of_rat (\<delta> * F k as)^2 * real s\<^sub>1 / 3" 
    if result_var_assms: "i\<^sub>1 < s\<^sub>1" "i\<^sub>2 < s\<^sub>2" for i\<^sub>1 i\<^sub>2
  proof -
    have "3 * real k * n powr (1 - 1 / real k) =
      (of_rat \<delta>)\<^sup>2 * (3 * real k * n powr (1 - 1 / real k) / (of_rat \<delta>)\<^sup>2)"
      using \<delta>_range by simp
    also have "... \<le>  (real_of_rat \<delta>)\<^sup>2 * (real s\<^sub>1)"
      unfolding s\<^sub>1_def
      by (intro mult_mono of_nat_ceiling, simp_all)
    finally have f2_var_2: "3 * real k * n powr (1 - 1 / real k) \<le> (of_rat \<delta>)\<^sup>2 * (real s\<^sub>1)"
      by blast

    have "\<Omega>\<^sub>2.variance (\<lambda>\<omega>. result (\<omega> (i\<^sub>1, i\<^sub>2)) :: real)  = variance result"
      using result_var_assms integrable_1[OF False]
      unfolding \<Omega>\<^sub>2_def M\<^sub>2_def \<Omega>\<^sub>1_def 
      by (subst variance_prod_pmf_slice, auto)
    also have "... \<le> of_rat (F k as)^2 * real k * n powr (1 - 1 / real k)"
      using assms False result_var_1 \<Omega>\<^sub>1_def by simp
    also have "... =
      of_rat (F k as)^2 * (real k * n powr (1 - 1 / real k))"
      by (simp add:ac_simps)
    also have "... \<le> of_rat (F k as)^2 * (of_rat \<delta>^2 * (real s\<^sub>1 / 3))"
      using f2_var_2 by (intro mult_left_mono, auto) 
    also have "... = of_rat (F k as * \<delta>)^2 * (real s\<^sub>1 / 3)"
      by (simp add: of_rat_mult power_mult_distrib) 
    also have "... = of_rat (\<delta> * F k as)^2 * real s\<^sub>1 / 3"
      by (simp add:ac_simps)
    finally show ?thesis
      by simp
  qed

  have mean_rv_exp: "\<Omega>\<^sub>2.expectation (\<lambda>\<omega>. mean_rv \<omega> i) = real_of_rat (F k as)"
    if mean_rv_exp_assms: "i < s\<^sub>2" for i
  proof -
    have "\<Omega>\<^sub>2.expectation (\<lambda>\<omega>. mean_rv \<omega> i) = \<Omega>\<^sub>2.expectation (\<lambda>\<omega>. \<Sum>n = 0..<s\<^sub>1. result (\<omega> (n, i)) / real s\<^sub>1)"
      by (simp add:mean_rv_def sum_divide_distrib)
    also have "... = (\<Sum>n = 0..<s\<^sub>1. \<Omega>\<^sub>2.expectation (\<lambda>\<omega>. result (\<omega> (n, i))) / real s\<^sub>1)"
      using integrable_2[OF False]
      by (subst Bochner_Integration.integral_sum, auto)
    also have "... = of_rat (F k as)"
      using s1_nonzero mean_rv_exp_assms
      by (simp add:result_exp)
    finally show ?thesis by simp
  qed

  have mean_rv_var: "\<Omega>\<^sub>2.variance (\<lambda>\<omega>. mean_rv \<omega> i) \<le> real_of_rat (\<delta> * F k as)^2/3" 
    if mean_rv_var_assms: "i < s\<^sub>2" for i
  proof -
    have a:"\<Omega>\<^sub>2.indep_vars (\<lambda>_. borel) (\<lambda>n x. result (x (n, i)) / real s\<^sub>1) {0..<s\<^sub>1}"
      unfolding \<Omega>\<^sub>2_def M\<^sub>2_def using mean_rv_var_assms
      by (intro indep_vars_restrict_intro'[where f="fst"], simp, simp add:restrict_dfl_def, simp, simp)
    have "\<Omega>\<^sub>2.variance (\<lambda>\<omega>. mean_rv \<omega> i) = \<Omega>\<^sub>2.variance (\<lambda>\<omega>. \<Sum>j = 0..<s\<^sub>1. result (\<omega> (j, i)) / real s\<^sub>1)"
      by (simp add:mean_rv_def sum_divide_distrib)
    also have "... = (\<Sum>j = 0..<s\<^sub>1. \<Omega>\<^sub>2.variance (\<lambda>\<omega>. result (\<omega> (j, i)) / real s\<^sub>1))"
      using a integrable_2[OF False]
      by (subst \<Omega>\<^sub>2.var_sum_all_indep, auto simp add:\<Omega>\<^sub>2_def)
    also have "... = (\<Sum>j = 0..<s\<^sub>1. \<Omega>\<^sub>2.variance (\<lambda>\<omega>. result (\<omega> (j, i))) / real s\<^sub>1^2)"
      using integrable_2[OF False]
      by (subst \<Omega>\<^sub>2.variance_divide, auto)
    also have "... \<le> (\<Sum>j = 0..<s\<^sub>1. ((real_of_rat (\<delta> * F k as))\<^sup>2 * real s\<^sub>1 / 3) / (real s\<^sub>1^2))"
      using result_var[OF _ mean_rv_var_assms]
      by (intro sum_mono divide_right_mono, auto)
    also have "... = real_of_rat (\<delta> * F k as)^2/3"
      using s1_nonzero
      by (simp add:algebra_simps power2_eq_square)
    finally show ?thesis by simp
  qed

  have "\<Omega>\<^sub>2.prob {y. of_rat (\<delta> * F k as) < \<bar>mean_rv y i - real_of_rat (F k as)\<bar>} \<le> 1/3" 
    (is "?lhs \<le> _") if c_assms: "i < s\<^sub>2" for i
  proof -
    define a where "a = real_of_rat (\<delta> * F k as)"
    have c: "0 < a" unfolding  a_def
      using assms \<delta>_range fk_nonzero
      by (metis zero_less_of_rat_iff mult_pos_pos)
    have "?lhs \<le> \<Omega>\<^sub>2.prob {y \<in> space \<Omega>\<^sub>2. a \<le> \<bar>mean_rv y i -  \<Omega>\<^sub>2.expectation (\<lambda>\<omega>. mean_rv \<omega> i)\<bar>}"
      by (intro \<Omega>\<^sub>2.pmf_mono[OF \<Omega>\<^sub>2_def], simp add:a_def mean_rv_exp[OF c_assms] space_\<Omega>\<^sub>2) 
    also have "... \<le> \<Omega>\<^sub>2.variance (\<lambda>\<omega>. mean_rv \<omega> i)/a^2"
      by (intro \<Omega>\<^sub>2.Chebyshev_inequality integrable_2 c False)  (simp add:\<Omega>\<^sub>2_def)
    also have "... \<le> 1/3" using c
      using mean_rv_var[OF c_assms] 
      by (simp add:algebra_simps, simp add:a_def)
    finally show ?thesis
      by blast
  qed

  moreover have "\<Omega>\<^sub>2.indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. mean_rv \<omega> i) {0..<s\<^sub>2}"
    using s1_nonzero unfolding \<Omega>\<^sub>2_def M\<^sub>2_def
    by (intro indep_vars_restrict_intro'[where f="snd"] finite_cartesian_product)
     (simp_all add:mean_rv_def restrict_dfl_def space_\<Omega>\<^sub>2)
  moreover have " - (18 * ln (real_of_rat \<epsilon>)) \<le> real s\<^sub>2"
    by (simp add:s\<^sub>2_def, linarith)
  ultimately have "1 - of_rat \<epsilon> \<le> 
    \<Omega>\<^sub>2.prob {y \<in> space \<Omega>\<^sub>2. \<bar>median s\<^sub>2 (mean_rv y) - real_of_rat (F k as)\<bar> \<le> of_rat (\<delta> * F k as)}" 
    using \<epsilon>_range
    by (intro \<Omega>\<^sub>2.median_bound_2, simp_all add:space_\<Omega>\<^sub>2)
  also have "... = \<Omega>\<^sub>2.prob {y. \<bar>median_rv y - real_of_rat (F k as)\<bar> \<le> real_of_rat (\<delta> * F k as)}" 
    by (simp add:median_rv_def space_\<Omega>\<^sub>2)
  also have "... =  \<Omega>\<^sub>2.prob {y. \<bar>median_rv y - F k as\<bar> \<le> \<delta> * F k as}"
    by (simp add:real_of_rat_median_rv of_rat_less_eq flip: of_rat_diff)
  also have "... = \<P>(\<omega> in measure_pmf M. \<bar>\<omega> - F k as\<bar> \<le> \<delta> * F k as)"
    by (simp add: b comp_def map_pmf_def[symmetric] \<Omega>\<^sub>2_def)
  finally show ?thesis by simp
qed

lemma fk_exact_space_usage':
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n)"
  shows "AE \<omega> in M. bit_count (encode_fk_state \<omega>) \<le> fk_space_usage (k, n, length as, \<epsilon>, \<delta>)"
    (is "AE \<omega> in M. (_  \<le> ?rhs)")
proof -
  define H where "H = (if as = [] then return_pmf (\<lambda>i\<in> {0..<s\<^sub>1}\<times>{0..<s\<^sub>2}. (0,0)) else M\<^sub>2)"

  have a:"M = map_pmf (\<lambda>x.(s\<^sub>1,s\<^sub>2,k,length as, x)) H"
  proof (cases "as \<noteq> []")
    case True
    then show ?thesis 
      unfolding M_def fk_alg_sketch[OF True] H_def
      by (simp add:M\<^sub>2_def)
  next
    case False
    then show ?thesis
      by (simp add:H_def M_def s\<^sub>1_def[symmetric] Let_def s\<^sub>2_def[symmetric] map_pmf_def bind_return_pmf)
  qed

  have "bit_count (encode_fk_state (s\<^sub>1, s\<^sub>2, k, length as, y)) \<le> ?rhs"
    if b:"y \<in> set_pmf H" for y
  proof -
    have b0:" as \<noteq> [] \<Longrightarrow> y \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E M\<^sub>1"
      using b non_empty_space fin_space by (simp add:H_def M\<^sub>2_def set_prod_pmf)

    have "bit_count ((N\<^sub>e \<times>\<^sub>e N\<^sub>e) (y x)) \<le> 
      ereal (2 * log 2 (real n + 1) + 1) + ereal (2 * log 2 (real (length as) + 1) + 1)"
      (is "_ \<le> ?rhs1")
      if b1_assms: "x \<in> {0..<s\<^sub>1}\<times>{0..<s\<^sub>2}" for x
    proof -
      have "fst (y x) \<le> n"
      proof (cases "as = []")
        case True
        then show ?thesis using b b1_assms by (simp add:H_def)
      next
        case False
        hence "1 \<le> count_list as (fst (y x))"
          using b0 b1_assms by (simp add:PiE_iff case_prod_beta M\<^sub>1_def, fastforce)
        hence "fst (y x) \<in> set as"
          using count_list_gr_1 by metis
        then show ?thesis 
          by (meson lessThan_iff less_imp_le_nat subsetD as_range)
      qed
      moreover have "snd (y x) \<le> length as" 
      proof (cases "as = []")
        case True
        then show ?thesis using b b1_assms by (simp add:H_def)
      next
        case False
        hence "(y x) \<in> M\<^sub>1"
          using b0 b1_assms by auto
        hence "snd (y x) \<le> count_list as (fst (y x))"
          by (simp add:M\<^sub>1_def case_prod_beta)
        then show ?thesis using count_le_length by (metis order_trans)
      qed
      ultimately have "bit_count (N\<^sub>e (fst (y x))) + bit_count (N\<^sub>e (snd (y x))) \<le> ?rhs1"
        using exp_golomb_bit_count_est  by (intro add_mono, auto)
      thus ?thesis
        by (subst dependent_bit_count_2, simp)
    qed

    moreover have "y \<in> extensional ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})"
      using b0 b PiE_iff by (cases "as = []", auto simp:H_def PiE_iff)

    ultimately have "bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e N\<^sub>e \<times>\<^sub>e N\<^sub>e) y) \<le> 
      ereal (real s\<^sub>1 * real s\<^sub>2) * (ereal (2 * log 2 (real n + 1) + 1) +
      ereal (2 * log 2 (real (length as) + 1) + 1))"
      by (intro fun_bit_count_est[where xs="(List.product [0..<s\<^sub>1] [0..<s\<^sub>2])", simplified], auto)
    hence "bit_count (encode_fk_state (s\<^sub>1, s\<^sub>2, k, length as, y)) \<le> 
       ereal (2 * log 2 (real s\<^sub>1 + 1) + 1) + 
      (ereal (2 * log 2 (real s\<^sub>2 + 1) + 1) +  
      (ereal (2 * log 2 (real k + 1) + 1) + 
      (ereal (2 * log 2 (real (length as) + 1) + 1) +  
      (ereal (real s\<^sub>1 * real s\<^sub>2) * (ereal (2 * log 2 (real n+1) + 1) + 
       ereal (2 * log 2 (real (length as)+1) + 1))))))"
      unfolding encode_fk_state_def dependent_bit_count
      by (intro add_mono exp_golomb_bit_count, auto)
    also have "... \<le> ?rhs" 
      by (simp add: s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] Let_def) (simp add:ac_simps)
    finally show "bit_count (encode_fk_state (s\<^sub>1, s\<^sub>2, k, length as, y)) \<le> ?rhs"
      by blast
  qed
  thus ?thesis
    by (simp add: a AE_measure_pmf_iff del:fk_space_usage.simps)
qed

end

text \<open>Main results of this section:\<close>

theorem fk_alg_correct:
  assumes "k \<ge> 1"
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n) \<bind> fk_result"
  shows "\<P>(\<omega> in measure_pmf M. \<bar>\<omega> - F k as\<bar> \<le> \<delta> * F k as) \<ge> 1 - of_rat \<epsilon>"
  unfolding M_def using fk_alg_correct'[OF assms(1-4)] by blast

theorem fk_exact_space_usage:
  assumes "k \<ge> 1"
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> fk_update a) as (fk_init k \<delta> \<epsilon> n)"
  shows "AE \<omega> in M. bit_count (encode_fk_state \<omega>) \<le> fk_space_usage (k, n, length as, \<epsilon>, \<delta>)"
  unfolding M_def using fk_exact_space_usage'[OF assms(1-4)] by blast

theorem fk_asymptotic_space_complexity:
  "fk_space_usage \<in> 
  O[at_top \<times>\<^sub>F at_top \<times>\<^sub>F at_top \<times>\<^sub>F at_right (0::rat) \<times>\<^sub>F at_right (0::rat)](\<lambda> (k, n, m, \<epsilon>, \<delta>).
  real k * real n powr (1-1/ real k) / (of_rat \<delta>)\<^sup>2 * (ln (1 / of_rat \<epsilon>)) * (ln (real n) + ln (real m)))"
  (is "_ \<in> O[?F](?rhs)")
proof -
  define k_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "k_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). k)"
  define n_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "n_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). n)"
  define m_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "m_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). m)"
  define \<epsilon>_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<epsilon>_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). \<epsilon>)"
  define \<delta>_of :: "nat \<times> nat \<times> nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<delta>_of = (\<lambda>(k, n, m, \<epsilon>, \<delta>). \<delta>)"

  define g1 where 
    "g1 = (\<lambda>x. real (k_of x)*(real (n_of x)) powr (1-1/ real (k_of x)) * (1 / of_rat (\<delta>_of x)^2))"

  define g where 
    "g = (\<lambda>x. g1 x * (ln (1 / of_rat (\<epsilon>_of x))) * (ln (real (n_of x)) + ln (real (m_of x))))"

  define s1_of where "s1_of = (\<lambda>x. 
    nat \<lceil>3 * real (k_of x) * real (n_of x) powr (1 - 1 / real (k_of x)) / (real_of_rat (\<delta>_of x))\<^sup>2\<rceil>)"
  define s2_of where "s2_of = (\<lambda>x. nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>)"

  have evt: "(\<And>x. 
    0 < real_of_rat (\<delta>_of x) \<and> 0 < real_of_rat (\<epsilon>_of x) \<and> 
    1/real_of_rat (\<delta>_of x) \<ge> \<delta> \<and> 1/real_of_rat (\<epsilon>_of x) \<ge> \<epsilon> \<and>
    real (n_of x) \<ge> n \<and> real (k_of x) \<ge> k \<and> real (m_of x) \<ge> m\<Longrightarrow> P x) 
    \<Longrightarrow> eventually P ?F"  (is "(\<And>x. ?prem x \<Longrightarrow> _) \<Longrightarrow> _")
    for \<delta> \<epsilon> n k m P
    apply (rule eventually_mono[where P="?prem" and Q="P"])
    apply (simp add:\<epsilon>_of_def case_prod_beta' \<delta>_of_def n_of_def k_of_def m_of_def)
     apply (intro eventually_conj eventually_prod1' eventually_prod2'
        sequentially_inf eventually_at_right_less inv_at_right_0_inf)
    by (auto simp add:prod_filter_eq_bot)

  have 1: 
    "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x))"
    "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (m_of x))"
    "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (k_of x))"
    by (intro landau_o.big_mono eventually_mono[OF evt], auto)+


  have "(\<lambda>x. ln (real (m_of x) + 1)) \<in> O[?F](\<lambda>x. ln (real (m_of x)))"
    by (intro landau_ln_2[where a="2"] evt[where m="2"] sum_in_bigo 1, auto)
  hence 2: " (\<lambda>x. log 2 (real (m_of x) + 1)) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    by (intro landau_sum_2  eventually_mono[OF evt[where n="1" and m="1"]])
     (auto simp add:log_def)

  have 3: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))" 
    using order_less_le_trans[OF exp_gt_zero] ln_ge_iff
    by (intro landau_o.big_mono  evt[where \<epsilon>="exp 1"])
     (simp add: abs_ge_iff, blast)

  have 4: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    using one_le_power
    by (intro landau_o.big_mono evt[where \<delta>="1"])
     (simp add:power_one_over[symmetric], blast)

  have "(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)))"
    using order_less_le_trans[OF exp_gt_zero] ln_ge_iff
    by (intro landau_o.big_mono  evt[where n="exp 1"])
     (simp add: abs_ge_iff, blast)

  hence 5: "(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    by (intro landau_sum_1 evt[where n="1" and m="1"], auto)

  have "(\<lambda>x. -ln(of_rat (\<epsilon>_of x))) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))" 
    by (intro landau_o.big_mono evt) (auto simp add:ln_div)
  hence 6: "(\<lambda>x. real (s2_of x)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    unfolding s2_of_def
    by (intro landau_nat_ceil 3, simp)

  have 7: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x) powr (1 - 1 / real (k_of x)))"
    by (intro landau_o.big_mono evt[where n="1" and k="1"])
     (auto simp add: ge_one_powr_ge_zero)

  have 8: "(\<lambda>_. 1) \<in> O[?F](g1)"
    unfolding g1_def by (intro landau_o.big_mult_1 1 7 4)

  have "(\<lambda>x. 3 * (real (k_of x) * (n_of x) powr (1 - 1 / real (k_of x)) / (of_rat (\<delta>_of x))\<^sup>2))
    \<in> O[?F](g1)"
    by (subst landau_o.big.cmult_in_iff, simp, simp add:g1_def)
  hence 9: "(\<lambda>x. real (s1_of x)) \<in> O[?F](g1)"
    unfolding s1_of_def by (intro landau_nat_ceil 8, auto simp:ac_simps)

  have 10: "(\<lambda>_. 1) \<in> O[?F](g)" 
    unfolding g_def by (intro landau_o.big_mult_1 8 3 5)
  
  have "(\<lambda>x. real (s1_of x)) \<in> O[?F](g)"
    unfolding g_def by (intro landau_o.big_mult_1 5 3 9)
  hence "(\<lambda>x. ln (real (s1_of x) + 1)) \<in> O[?F](g)"
    using 10 by (intro landau_ln_3 sum_in_bigo, auto)
  hence 11: "(\<lambda>x. log 2 (real (s1_of x) + 1)) \<in> O[?F](g)"
    by (simp add:log_def)

  have 12: " (\<lambda>x. ln (real (s2_of x) + 1)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    using evt[where \<epsilon>="2"] 6 3
    by (intro landau_ln_3 sum_in_bigo, auto)

  have 13: "(\<lambda>x. log 2 (real (s2_of x) + 1)) \<in> O[?F](g)" 
    unfolding g_def 
    by (rule landau_o.big_mult_1, rule landau_o.big_mult_1', auto simp add: 8 5 12 log_def)

  have "(\<lambda>x. real (k_of x)) \<in> O[?F](g1)"
    unfolding g1_def using 7 4
    by (intro landau_o.big_mult_1, simp_all)
  hence "(\<lambda>x. log 2 (real (k_of x) + 1)) \<in> O[?F](g1)"
    by (simp add:log_def) (intro landau_ln_3 sum_in_bigo 8, auto)
  hence 14: "(\<lambda>x. log 2 (real (k_of x) + 1)) \<in> O[?F](g)"
    unfolding g_def  by (intro landau_o.big_mult_1 3 5)

  have 15: "(\<lambda>x. log 2 (real (m_of x) + 1)) \<in> O[?F](g)"
    unfolding g_def using 2 8 3
    by (intro landau_o.big_mult_1', simp_all)

  have "(\<lambda>x. ln (real (n_of x) + 1)) \<in> O[?F](\<lambda>x. ln (real (n_of x)))"
    by (intro landau_ln_2[where a="2"] eventually_mono[OF evt[where n="2"]] sum_in_bigo 1, auto)
  hence " (\<lambda>x. log 2 (real (n_of x) + 1)) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    by (intro landau_sum_1 evt[where n="1" and m="1"])
     (auto simp add:log_def)
  hence 16: "(\<lambda>x. real (s1_of x) * real (s2_of x) *
    (2 + 2 * log 2 (real (n_of x) + 1) + 2 * log 2 (real (m_of x) + 1))) \<in> O[?F](g)" 
    unfolding g_def using 9 6 5 2
    by (intro landau_o.mult sum_in_bigo, auto)

  have "fk_space_usage = (\<lambda>x. fk_space_usage (k_of x, n_of x, m_of x, \<epsilon>_of x, \<delta>_of x))"
    by (simp add:case_prod_beta' k_of_def n_of_def \<epsilon>_of_def \<delta>_of_def m_of_def)
  also have "... \<in> O[?F](g)"
    using 10 11 13 14 15 16
    by (simp add:fun_cong[OF s1_of_def[symmetric]] fun_cong[OF s2_of_def[symmetric]] Let_def)
     (intro sum_in_bigo, auto)
  also have "... = O[?F](?rhs)"
    by (simp add:case_prod_beta' g1_def g_def n_of_def \<epsilon>_of_def \<delta>_of_def m_of_def k_of_def)
  finally show ?thesis by simp
qed

end
