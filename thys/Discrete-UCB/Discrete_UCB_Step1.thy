theory Discrete_UCB_Step1
  imports "MSc_Project_Discrete_Prop15_1"

begin

locale bandit_policy = bandit_problem +  prob_space  +
  fixes \<Omega> :: "'b set"
    and \<F> :: "'b set set"
    and \<omega> :: 'b
    and \<pi> :: "nat \<Rightarrow> 'b \<Rightarrow> 'a"
    and N_n :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> nat"  
  assumes  measurable_policy: "\<forall>t. \<pi> t \<in> measurable M (count_space A)"
    and N_n_def: "\<forall>n a \<omega>. N_n n a \<omega> = card {t \<in> {0..<n}. \<pi> (t+1) \<omega> = a}"
    and count_assm_pointwise: "\<forall>n \<omega>. (\<Sum>a \<in> A. real (N_n n a \<omega>)) = real n" 
begin

lemma union_eq:
  fixes a :: 'a and n k :: nat 
  assumes "k \<le> n"
  shows "{t. t < n \<and> \<pi> (t+1) \<omega> = a} = {t. t < k \<and> \<pi> (t+1) \<omega> = a} \<union> {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
proof
  show "{t. t < n \<and> \<pi> (t+1) \<omega> = a} \<subseteq> {t. t < k \<and> \<pi> (t+1) \<omega> = a} \<union> {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
  proof
    fix x assume "x \<in> {t. t < n \<and> \<pi> (t+1) \<omega> = a}"
    then have "x < n" and "\<pi> (x+1) \<omega> = a" by auto
    then have "x < k \<or> k \<le> x" by auto
    thus "x \<in> {t. t < k \<and> \<pi> (t+1) \<omega> = a} \<union> {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
      using \<open>x < n\<close> \<open>\<pi> (x+1) \<omega> = a\<close> by auto
  qed
next
  show "{t. t < k \<and> \<pi> (t+1) \<omega> = a} \<union> {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a} \<subseteq> {t. t < n \<and> \<pi> (t+1) \<omega> = a}"
  proof
    fix x assume "x \<in> {t. t < k \<and> \<pi> (t+1) \<omega> = a} \<union> {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
    then have "x < k \<and> \<pi> (x+1) \<omega> = a \<or> (k \<le> x \<and> x < n \<and> \<pi> (x+1) \<omega> = a)" by auto
    hence "x < n \<and> \<pi> (x+1) \<omega> = a" using assms by auto
    thus "x \<in> {t. t < n \<and> \<pi> (t+1) \<omega> = a}" by auto
  qed
qed

lemma cardinality_indic_eq:
  fixes I :: "nat \<Rightarrow> bool"
  assumes "finite {t. k \<le> t \<and> t < n}"
  shows "card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> I t} = (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> I t then 1 else 0)"
proof -
  have fin: "finite {t. k \<le> t \<and> t < n}" using assms by simp
  have sum_eq:
    "sum (indicator {t. \<pi> (t+1) \<omega> = a \<and> I t}) {t. k \<le> t \<and> t < n} = card ({t. k \<le> t \<and> t < n} \<inter> {t. \<pi> (t+1) \<omega> = a \<and> I t})"
    by (rule sum_indicator_eq_card[OF fin])
  have sets_eq:
    "{t. k \<le> t \<and> t < n} \<inter> {t. \<pi> (t+1) \<omega> = a \<and> I t} = {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> I t}"
    by auto
  hence card_eq:
    "card ({t. k \<le> t \<and> t < n} \<inter> {t. \<pi> (t+1) \<omega> = a \<and> I t}) = card {t. k \<le> t \<and> t < n \<and> \<pi>(t+1) \<omega> = a \<and> I t}"
    by simp
  have card_sum_eq:
    "sum (indicator {t. \<pi> (t+1) \<omega> = a \<and> I t}) {t. k \<le> t \<and> t < n} = card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> I t}"
    using sum_eq sets_eq by simp
  have ind_eq:
    "sum (indicator {t. \<pi> (t+1) \<omega> = a \<and> I t}) {t. k \<le> t \<and> t < n} = sum (\<lambda>t. of_bool (\<pi> (t+1) \<omega> = a \<and> I t)) {t. k \<le> t \<and> t < n}"
    by (simp add: indicator_def)
  have bool_if_eq:
    "sum (\<lambda>t. of_bool (\<pi> (t+1) \<omega> = a \<and> I t)) {t. k \<le> t \<and> t < n} = sum (\<lambda>t. if \<pi> (t+1) \<omega> = a \<and> I t then 1 else 0) {t. k \<le> t \<and> t < n}"
    by (simp add: of_bool_def)
  have set_eq: "{t. k \<le> t \<and> t < n} = {k..} \<inter> {..<n}" by auto
  have sum_set_eq:
    "sum (\<lambda>t. if \<pi> (t+1) \<omega> = a \<and> I t then 1 else 0) {t. k \<le> t \<and> t < n} = sum (\<lambda>t. if \<pi> (t+1) \<omega> = a \<and> I t then 1 else 0) ({k..} \<inter> {..<n})"
    by (simp add: set_eq)
  have atLeastLessThan_eq:
    "sum (\<lambda>t. if \<pi> (t+1) \<omega> = a \<and> I t then 1 else 0) ({k..} \<inter> {..<n}) = sum (\<lambda>t. if \<pi> (t+1) \<omega> = a \<and> I t then 1 else 0) (atLeastLessThan k n)"
    by (simp add: atLeastLessThan_def)
  have final_sum_eq:
    "sum (\<lambda>t. if \<pi> (t+1) \<omega> = a \<and> I t then 1 else 0) (atLeastLessThan k n) = (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> I t then 1 else 0)"
    by simp
  show ?thesis
    apply (subst card_sum_eq[symmetric])
    apply (subst ind_eq)
    apply (subst bool_if_eq)
    apply (subst sum_set_eq)
    apply (subst atLeastLessThan_eq)
    apply (simp add: final_sum_eq)
    done
qed

lemma ge_rewrite: "(x::real) \<ge> y \<Longrightarrow> y \<le> x" by simp

lemma Nn_expression:
  fixes a :: 'a and s :: "nat \<Rightarrow> real"
    and k :: nat and n :: nat
  assumes "a \<in> A"
    and "k \<le> n"
    and "0 < n"
    and "\<forall> t \<in> {0..n}. 0 < s t"
    and "\<forall>t < n - 1.  s t \<le> s (t + 1)"  (* s non-decreasing *)
    and init_play_once: "\<forall>\<omega>. a \<in> A \<longrightarrow> N_n k a \<omega> = 1"
    and finite_played_sets:
    "finite {t. t < n \<and> \<pi> (t+1) \<omega> = a}"
    "finite {t. t < k \<and> \<pi> (t+1) \<omega> = a}"
    "finite {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
  shows
    "(N_n n a \<omega>) = 1 + (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) +
                      (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t then 1 else 0)"
proof -
  have Nn_def: "(N_n n a \<omega>) = card {t. t < n \<and> \<pi> (t+1) \<omega> = a}"
    by (simp add: N_n_def)

  have init_count: "1 \<le> card {t. t < k \<and> \<pi> (t+1) \<omega> = a}"
  proof -
    have eq_card: "N_n k a \<omega> = card {t. t < k \<and> \<pi> (t+1) \<omega> = a}"
      by (simp add: N_n_def)
    moreover from init_play_once and \<open>a \<in> A\<close> have "1 \<le> N_n k a \<omega>"
      by simp
    ultimately show ?thesis by simp
  qed

  have disj: "{t. t < k \<and> \<pi> (t+1) \<omega> = a} \<inter> {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a} = {}"
    by auto

  have union_eq_set:
    "{t. t < n \<and> \<pi> (t+1) \<omega> = a} = {t. t < k \<and> \<pi> (t+1) \<omega> = a} \<union> {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
    using union_eq assms by blast

  have finite1: "finite {t. t < k \<and> \<pi> (t+1) \<omega> = a}" and finite2: "finite {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
    using finite_played_sets by auto

  have card_eq:
    "card {t. t < n \<and> \<pi> (t+1) \<omega> = a} = card {t. t < k \<and> \<pi> (t+1) \<omega> = a} + card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
    using card_Un_disjoint[OF finite1 finite2 disj] union_eq_set by simp

  have eq_card_k: "card {t. t < k \<and> \<pi> (t+1) \<omega> = a} = N_n k a \<omega>"
    by (simp add: N_n_def)

  have card_k_eq_1: "card {t. t < k \<and> \<pi> (t+1) \<omega> = a}  = 1"
    using init_play_once assms eq_card_k by simp

  have card_eq_1:
    "card {t. t < n \<and> \<pi> (t+1) \<omega> = a} = 1 + card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
    using card_eq eq_card_k card_k_eq_1 by simp

  have finite_lt: "finite {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t}"
    using finite2 finite_subset by simp

  have finite_ge: "finite {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t}"
    using finite2 finite_subset by simp

  have card_eq_partition:
    "card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a} =
     card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t} +
     card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t}"
  proof -
    have union_eq_partition:
      "{t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a} =
       {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t} \<union>
       {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t}" by auto

    have disj_partition:
      "{t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t} \<inter>
       {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t} = {}"
      by auto

    show ?thesis
      using card_Un_disjoint[OF finite_lt finite_ge disj_partition] union_eq_partition by simp
  qed

  have card_eq_sum_lt:
    "card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t} =
     (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0)"
    using cardinality_indic_eq by simp

  have card_eq_sum_ge:
    "card {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t} =
     (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t then 1 else 0)"
    using cardinality_indic_eq by simp

  have "(N_n n a \<omega>) = card {t. t < n \<and> \<pi> (t+1) \<omega> = a}"
    using N_n_def by simp

  also have "... = 1 +
    (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) +
    (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t then 1 else 0)"
    using card_eq_partition card_eq_1 card_eq_sum_lt card_eq_sum_ge by simp

  also have "... = 1 +
    (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) +
    (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
    using ge_rewrite by simp

  have rewrite_eq:" (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t then 1 else 0) =
       (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
    using sum.cong by simp

  ultimately have final_eq: "(N_n n a \<omega>) = 1 + (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) +
                      (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t then 1 else 0) "
    by simp

  show "(N_n n a \<omega>) = 1 + (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) +
                      (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) \<ge> s t then 1 else 0)"
    apply (subst rewrite_eq)
    apply (subst final_eq)
    apply simp
    done

qed

lemma upper_bound_expression_contradiction:
  fixes a :: 'a and s :: "nat \<Rightarrow> real"
    and k :: nat and n :: nat
    and s_n_nat :: nat
  assumes "a \<in> A"
    and "k \<le> n"
    and "0 < n"
    and non_neg_s: "\<forall> t \<in> {0..n}. 0 < s t"
    and base_le: "s 0 \<le> s 1" 
    and non_dec: "\<forall>t < n - 1. s t \<le> s (t + 1)"  (* s is non-decreasing *)
    and s_mono: "\<And>t. k \<le> t \<and> t \<le> n \<Longrightarrow> s t \<le> s n"
    and init_play_once: "\<forall>\<omega>. a \<in> A \<longrightarrow> N_n k a \<omega> = 1"
    and finite_played_sets:
    "finite {t. t < n \<and> \<pi> (t+1) \<omega> = a}"
    "finite {t. t < k \<and> \<pi> (t+1) \<omega> = a}"
    "finite {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
    and xs_sorted_def: "xs = sorted_list_of_set {t \<in> {k..<n}. \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t}"
    and s_nat_def: "s_n_nat = nat (\<lfloor>s n\<rfloor>)"
    and len_bound_def: "s_n_nat < length xs" (* s_n_nat is an existing element *)
    and distinct_xs: "distinct xs"
    and gt_ineq: "length xs + 1 > \<lfloor>s n\<rfloor>"
    and  N_n_increasing_with_plays:
    "\<forall> t t'. k \<le> t \<and> t < t' \<and> \<pi> (t+1) \<omega> = a \<and> \<pi> (t'+1) \<omega> = a \<longrightarrow> N_n t' a \<omega> \<ge> N_n t a \<omega> + 1"
    and neg: "1 + real (\<Sum> t=k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) > s n"
    and "t_hat \<in> set xs" 
    and " t_hat = xs ! s_n_nat"
    and " real (N_n t_hat a \<omega>) \<ge> real s_n_nat + 1"
    (* By construction of xs, and since t_hat is the s_n_nat-th element in xs,
     the count N_n t_hat a \<omega> is at least s_n_nat + 1 *)
    (* The argument depends on repeated increments due to monotonicity *)

shows "(real (N_n t_hat a \<omega>) \<ge> \<lfloor>s n\<rfloor> + 1) \<and> (\<pi> (t_hat+1) \<omega> = a \<and> (real (N_n t_hat a \<omega>) < s t_hat))"

proof -
  have sn_nat_def:"s_n_nat = nat (\<lfloor>s n\<rfloor>)" by fact

  let ?I = "{t \<in> {k..<n}. \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t}"
  have sum_eq_card: "real (\<Sum> t=k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) = real (card ?I)"
    using cardinality_indic_eq by simp

  have finI: "finite {t \<in> {k..<n}. \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t}"
  proof -
    have subset: "{t \<in> {k..<n}. \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t} \<subseteq> {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
      by auto
    moreover have "finite {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
      using finite_played_sets(3) .
    ultimately show ?thesis
      using finite_subset by blast
  qed


  have xs_props: "sorted xs" "distinct xs" "set xs = {t \<in> {k..<n}. \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t}"
    using List.linorder_class.set_sorted_list_of_set
    using finite_played_sets
    unfolding xs_sorted_def
    by auto


  have sum_eq_length:
    "(\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) = length xs"
  proof -
    let ?P = "\<lambda>t. \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t"
    let ?I = "{t \<in> {k..<n}. ?P t}"

    have sum_card: "(\<Sum> t = k..<n. if ?P t then 1 else 0) = card ?I"
      using cardinality_indic_eq by simp

    also have "... = card (set xs)"
      using xs_props(3) by simp

    also have "... = length xs"
      using xs_props(2) distinct_card by auto 

    finally show ?thesis .
  qed  

  have gt_ineq: "1 + real(length xs) > s n"
  proof -
    (* First show sum over indicator = length xs *)

    have eq1:"1 + (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) = 1 + length xs"
      using sum_eq_length by simp

    then have eq2: "real (1 + (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0)) = 1 + real ( length xs)"  
      by simp
        (* Use assumption neg to get strict inequality *)
    from neg have "\<not> (1 + real (\<Sum>t=k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) \<le> s n)"
      by simp

    hence gt: "1 + real (\<Sum> t=k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) > s n"
      by simp

(* Coerce nat to real for final goal *)
    then show ?thesis
      using eq1 eq2 neg gt by simp
  qed

  then have len_bound_assm: "s_n_nat < length xs"
    using len_bound_def assms
    by auto

  then have  distinct_xs: "distinct xs" (* distinct assumption already assumed in the global  scope*)
    using assms by simp

  then have  gt_ineq: "length xs + 1 > \<lfloor>s n\<rfloor>"  (* ineq already assumed *)
    using assms by simp

  have part_1_glob: "\<pi> (t_hat +1 ) \<omega> = a \<and> real (N_n t_hat a \<omega>)  <  s t_hat"
  proof -
    have floor_le_sn: "\<lfloor>s n\<rfloor> \<le> s n"
      using Archimedean_Field.of_int_floor_le by simp

    from gt_ineq have len_bound: "length xs + 1 > \<lfloor>s n\<rfloor>"
      using len_bound_assm by simp

    have nat_expression_sn: "length xs \<ge> nat (\<lfloor>s n\<rfloor>)"
    proof -
      from len_bound have "length xs \<ge> nat (\<lfloor>s n\<rfloor>)"
        by (simp add: nat_less_iff)
      then show ?thesis .
    qed


    have sn_lt_len_plus_1: "\<lfloor>s n\<rfloor> <  1 + real (length xs)"
      using gt_ineq by simp


    then have final_eq_glob:"\<pi> (t_hat+1) \<omega> = a \<and> real (N_n t_hat a \<omega>)  <  s t_hat"
    proof - 

      have \<pi>_eq: "\<pi> (t_hat+1) \<omega> = a" 
        using assms xs_sorted_def by simp

      then have "\<pi> (t_hat +1) \<omega> = a" using \<pi>_eq by simp

      then have intermid_eq: "k \<le> t_hat \<and> t_hat < n \<and> \<pi> (t_hat +1) \<omega> = a \<and> real (N_n t_hat a \<omega>) < s t_hat"
        using xs_sorted_def `t_hat \<in> set xs` by auto

      have fin_eq:"\<pi> (t_hat + 1) \<omega> = a \<and> real (N_n t_hat a \<omega>) < s t_hat"
        using intermid_eq
        by simp
      then show ?thesis by simp
    qed

    show ?thesis using  final_eq_glob by simp
  qed

(*this should hold as we now have verified 
but is in fact impossible as arm a must have played at least 1 +\<lfloor>s n\<rfloor> times, let's continue exploring
*)


  have floor_le_sn: "\<lfloor>s n\<rfloor> \<le> s n"
    using Archimedean_Field.of_int_floor_le by simp

  have one_plus_length_gt_floor: "1 + real (length xs) > s n"
    using `1 + real (length xs) > s n` .

  have floor_less_length_plus_one: "real (nat (\<lfloor>s n\<rfloor>)) < 1 + real (length xs)"
    using one_plus_length_gt_floor floor_le_sn
    by linarith

  from gt_ineq have len_result: "length xs  > \<lfloor>s n\<rfloor> - 1" by simp
  then have "length xs \<ge> nat (\<lfloor>s n\<rfloor>)" by (simp add: nat_less_iff)
  hence t_hat_in_set:"t_hat \<in> set xs"
    using assms distinct_xs len_bound_assm by auto

(* Since t_hat \<in> xs and xs \<subseteq> {k..<n}, we have k \<le> t_hat < n, so t_hat \<le> n *)
  have t_hat_le_n: "t_hat + 1 \<le> n"
    using xs_sorted_def t_hat_in_set by auto

(* Then by monotonicity: *)
  have k_le_t_hat: "k \<le> t_hat"
    using xs_sorted_def t_hat_in_set by auto

  have s_t_hat_le_s_n: "s t_hat \<le> s n"
    using s_mono[of t_hat] 
    using xs_sorted_def t_hat_in_set by auto


  have "real (N_n t_hat a \<omega>) \<ge> real s_n_nat + 1"
    using assms by simp

  have final_result: "real (N_n t_hat a \<omega>) \<ge> \<lfloor>s n\<rfloor> + 1"
    using \<open>real (N_n t_hat a \<omega>) \<ge> real (s_n_nat) + 1\<close>
    by (simp add: sn_nat_def )


  show ?thesis using final_result and part_1_glob by auto

qed


(* We have identified an element t_hat \<in> xs such that t_hat is the element at position s_n_nat
   in the sorted list xs. This corresponds to the floor index of s n in the sorted set of indices
   where arm a was played and the count N_n(t, a, \<omega>) is less than s(t).

   In simpler terms:

   Since there are at least \<lfloor>s n\<rfloor> + 1 such times in xs,
  N_t_hat_a \<ge> 1 +\<lfloor>s n\<rfloor> . *)


lemma Nn_upper_bound:
  fixes a :: 'a and s :: "nat \<Rightarrow> real"
    and k :: nat and n :: nat
  assumes asm: "real(1 + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0)) \<le> s n"
    and a_in_A: "a \<in> A"
    and k_le_n: "k \<le> n"
    and n_pos: "0 < n"
    and s_pos: "\<forall> t \<in> {0..n}. 0 < s t"
    and s_nondec: "\<forall> t < n - 1. s t \<le> s (t + 1)"
    and init_play_once: "\<forall>\<omega>. a \<in> A \<longrightarrow> N_n k a \<omega> = 1"
    and finite_played_sets_1: "finite {t. t < n \<and> \<pi> (t+1) \<omega> = a}"
    and finite_played_sets_2: "finite {t. t < k \<and> \<pi> (t+1) \<omega> = a}"
    and finite_played_sets_3: "finite {t. k \<le> t \<and> t < n \<and> \<pi> (t+1) \<omega> = a}"
  shows "real(N_n n a \<omega>) \<le> s n + real((\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
proof -
  have expr_nat: "N_n n a \<omega> =
    1 + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) +
        (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
    using Nn_expression[OF a_in_A k_le_n n_pos s_pos s_nondec init_play_once
        finite_played_sets_1 finite_played_sets_2 finite_played_sets_3]
    by simp

  from asm have bound:"real(1 + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0)) \<le> s n" by simp

  have "real (N_n n a \<omega>) = real ( 1 + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> real (N_n t a \<omega>) < s t then 1 else 0) +
        (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
    using expr_nat by simp

  also have "... \<le> s n + real ( (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
    using assms
    by simp

  then show ?thesis
    using expr_nat asm
    by simp
qed


theorem ENn_upper_bound:
  assumes
    a_in_A: "a \<in> A"
    and k_le_n: "k \<le> n"
    and n_pos: "0 < n"
    and s_pos: "\<forall>t \<in> {0..n}. 0 < s t"
    and s_nondec: "\<forall>t < n. s t \<le> s (t + 1)"
    and init_play_once: "\<forall>\<omega>. a \<in> A \<longrightarrow> N_n k a \<omega> = 1"
    and integrable_Nn: "integrable M (\<lambda>\<omega>. real (N_n n a \<omega>))"
    and integrable_rhs_sum: "integrable M (\<lambda>\<omega>. s n + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
    and integrable_s: "integrable M (\<lambda>\<omega>. s n)"
    and integrable_indicator_sum: "integrable M (\<lambda>\<omega>. \<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
    and linearity: "integral\<^sup>L M (\<lambda>\<omega>. s n + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)) = 
                 integral\<^sup>L M (\<lambda>\<omega>. s n) + integral\<^sup>L M (\<lambda>\<omega>. \<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
    and pointwise_bound: "real (N_n n a \<omega>) \<le> s n + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
    and mono_intgrl: " integral\<^sup>L M (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> integral\<^sup>L M (\<lambda>\<omega>. s n + (\<Sum>t = k..<n. 
if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
  shows
    "expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> 
     s n + expectation (\<lambda>\<omega>. (\<Sum>t = k..<n.  if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
proof -
  let ?f = "\<lambda>\<omega>. real (N_n n a \<omega>)"
  let ?g = "\<lambda>\<omega>. s n + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
  let ?g1 = "\<lambda>\<omega>. s n"
  let ?g2 = "\<lambda>\<omega>. (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
  have pointwise_le: " ?f \<omega> \<le> ?g \<omega>"
    using pointwise_bound .

  have intg_f: "integrable M ?f" using integrable_Nn .
  have intg_g: "integrable M ?g" using integrable_rhs_sum .
  then have eq_f:"integral\<^sup>L M ?f = expectation (?f)"
    using prob_space by simp
  then have eq_g: "integral\<^sup>L M ?g = expectation (?g)"
    by simp

  then have sub_eqg1:"integral\<^sup>L M ?g1 = expectation (\<lambda>\<omega>. s n)"
    by simp
  then have sub_eqg2:"integral\<^sup>L M ?g2 = expectation(\<lambda>\<omega>. (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
    by simp


  have "real (N_n n a \<omega>) \<le> s n + (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
    using assms by simp 

  have const_measure: "Sigma_Algebra.measure M (space M) = 1"
    using prob_space Probability_Measure.prob_space.prob_space by blast

  have exp_sn: "expectation (\<lambda>\<omega>. s n) = s n"
  proof -
    have "expectation (\<lambda>\<omega>. s n) = integral\<^sup>L M (\<lambda>\<omega>. s n)"
      by simp
    also have "... = s n"
      using prob_space by (simp add: prob_space.prob_space)
    then show ?thesis .
  qed

  have rhs_expr:
    "integral\<^sup>L M ?g =  integral\<^sup>L M (\<lambda>\<omega>. s n) + integral\<^sup>L M (\<lambda>\<omega>. \<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0)"
    using linearity by auto

  then have rhs_expr: 
    "expectation (?g) = expectation (\<lambda>\<omega>. s n) + expectation (\<lambda>\<omega>. (\<Sum>t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
    by simp

  also have final_eq: "expectation (?g) = s n + expectation (\<lambda>\<omega>. (\<Sum>t = k..<n.  if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
    using rhs_expr exp_sn
    by simp

  have glob_final_eq:"expectation (?f) \<le> expectation (?g)"
    using assms intg_f intg_g pointwise_le mono_intgrl
    by auto


  thus ?thesis
    using glob_final_eq final_eq by simp
qed

end
end
