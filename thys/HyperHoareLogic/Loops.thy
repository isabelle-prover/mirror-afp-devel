theory Loops
  imports Logic HOL.Wellfounded Expressivity
begin

section \<open>Rules for Loops\<close>

definition lnot where
  "lnot b \<sigma> = (\<not>b \<sigma>)"

definition if_then_else where
  "if_then_else b C1 C2 = If (Assume b;; C1) (Assume (lnot b);; C2)"

definition low_exp where
  "low_exp e S = (\<forall>\<phi> \<phi>'. \<phi> \<in> S \<and> \<phi>' \<in> S \<longrightarrow> (e (snd \<phi>) = e (snd \<phi>')))"

lemma low_exp_lnot:
  "low_exp b S \<longleftrightarrow> low_exp (lnot b) S"
  by (simp add: lnot_def low_exp_def)

definition holds_forall where
  "holds_forall b S \<longleftrightarrow> (\<forall>\<phi>\<in>S. b (snd \<phi>))"

lemma holds_forallI:
  assumes "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> b (snd \<phi>)"
  shows "holds_forall b S"
  using assms holds_forall_def by blast

lemma low_exp_two_cases:
  assumes "low_exp b S"
  shows "holds_forall b S \<or> holds_forall (lnot b) S"
  by (metis assms holds_forall_def lnot_def low_exp_def)

lemma sem_assume_low_exp:
  assumes "holds_forall b S"
  shows "sem (Assume b) S = S"
    and "sem (Assume (lnot b)) S = {}"
  using assume_sem[of b S] assms holds_forall_def[of b S] apply fastforce
  using assume_sem[of "lnot b" S] assms holds_forall_def[of b S] lnot_def[of b]
    by fastforce

lemma sem_assume_low_exp_seq:
  assumes "holds_forall b S"
  shows "sem (Assume b;; C) S = sem C S"
    and "sem (Assume (lnot b);; C) S = {}"
  apply (simp add: assms sem_assume_low_exp(1) sem_seq)
  by (metis assms empty_iff equals0I in_sem sem_assume_low_exp(2) sem_seq)

lemma lnot_involution:
  "lnot (lnot b) = b"
proof (rule ext)
  fix x show "lnot (lnot b) x = b x"
    by (simp add: lnot_def)
qed

lemma sem_if_then_else:
  shows "holds_forall b S \<Longrightarrow> sem (if_then_else b C1 C2) S = sem C1 S"
    and "holds_forall (lnot b) S \<Longrightarrow> sem (if_then_else b C1 C2) S = sem C2 S"
  apply (simp add: if_then_else_def sem_assume_low_exp_seq(1) sem_assume_low_exp_seq(2) sem_if)
  by (metis (no_types, opaque_lifting) if_then_else_def lnot_involution sem_assume_low_exp_seq(1) sem_assume_low_exp_seq(2) sem_if sup_bot_left)

lemma if_synchronized_aux:
  assumes "\<Turnstile> {P} C1 {Q}"
      and "\<Turnstile> {P} C2 {Q}"
      and "entails P (low_exp b)"
    shows "\<Turnstile> {P} if_then_else b C1 C2 {Q}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "P S"
  then have r: "low_exp b S" using assms(3) entailsE
    by metis
  show "Q (sem (if_then_else b C1 C2) S)"
  proof (cases "holds_forall b S")
    case True
    then show ?thesis
      by (metis asm0 assms(1) hyper_hoare_triple_def sem_if_then_else(1))
  next
    case False
    then show ?thesis
      by (metis asm0 assms(2) hyper_hoare_tripleE low_exp_two_cases r sem_if_then_else(2))
  qed
qed

theorem if_synchronized:
  assumes "\<Turnstile> {conj P (holds_forall b)} C1 {Q}"
      and "\<Turnstile> {conj P (holds_forall (lnot b))} C2 {Q}"
    shows "\<Turnstile> {conj P (low_exp b)} if_then_else b C1 C2 {Q}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "conj P (low_exp b) S"
  show "Q (sem (if_then_else b C1 C2) S)"
  proof (cases "holds_forall b S")
    case True
    then show ?thesis
      by (metis asm0 assms(1) conj_def hyper_hoare_triple_def sem_if_then_else(1))
  next
    case False
    then show ?thesis
      by (metis asm0 assms(2) conj_def hyper_hoare_triple_def low_exp_two_cases sem_if_then_else(2))
  qed
qed


definition while_cond where
  "while_cond b C = While (Assume b;; C);; Assume (lnot b)"


lemma while_synchronized_rec:
  assumes "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} Assume b;; C {conj (I (Suc n)) (low_exp b)}"
      and "conj (I 0) (low_exp b) S"
    shows "conj (I n) (low_exp b) (iterate_sem n (Assume b;; C) S) \<or> holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
  using assms
proof (induct n)
  case (Suc n)
  then have r: "conj (I n) (low_exp b) (iterate_sem n (Assume b;; C) S) \<or> holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
    by blast
  then show ?case
  proof (cases "conj (I n) (holds_forall b) (iterate_sem n (Assume b;; C) S)")
    case True
    then show ?thesis
      using Suc.prems(1) hyper_hoare_tripleE by fastforce
  next
    case False
    then have "holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
      by (metis conj_def low_exp_two_cases r)
    then have "iterate_sem (Suc n) (Assume b;; C) S = {}"
      by (metis iterate_sem.simps(2) lnot_involution sem_assume_low_exp_seq(2))
    then show ?thesis
      by (simp add: holds_forall_def)
  qed
qed (auto)

lemma false_then_empty_later:
  assumes "holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
      and "m > n"
    shows "iterate_sem m (Assume b;; C) S = {}"
  using assms
proof (induct "m - n" arbitrary: n m)
  case (Suc x)
  then show ?case
  proof (cases x)
    case 0
    then show ?thesis
      by (metis One_nat_def Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_eq_plus1 iterate_sem.simps(2) le_add_diff_inverse linorder_not_le lnot_involution order.asym sem_assume_low_exp_seq(2))
  next
    case (Suc nat)
    then have "m - 1 > n"
      using Suc.hyps(2) by auto
    then have "iterate_sem (m-1) (Assume b ;; C) S = {}"
      by (metis (no_types, lifting) Suc.hyps(1) Suc.hyps(2) Suc.prems(1) diff_Suc_1 diff_commute)
    then show ?thesis
      by (metis Nat.lessE Suc.prems(1) Suc.prems(2) diff_Suc_1 iterate_sem.simps(2) sem_assume_low_exp_seq(2) sem_seq)
  qed
qed (simp)

lemma split_union_triple:
  "(\<Union>(m::nat). f m) = (\<Union>m\<in>{m |m. m < n}. f m) \<union> f n \<union> (\<Union>m\<in>{m |m. m > n}. f m)" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
    by blast
  show "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then obtain m where "x \<in> f m"
      by blast
    then have "m < n \<or> m = n \<or> m > n"
      by force
    then show "x \<in> ?B"
      using \<open>x \<in> f m\<close> by auto
  qed
qed


lemma sem_union_swap:
  "sem C (\<Union>x\<in>S. f x) = (\<Union>x\<in>S. sem C (f x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix y assume "y \<in> ?A"
    then obtain x where "x \<in> S" "y \<in> sem C (f x)"
      using UN_iff in_sem[of y C] by force
    then show "y \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
    by (simp add: SUP_least SUP_upper sem_monotonic)
qed



lemma while_synchronized_case_1:
  assumes "\<And>m. m < n \<Longrightarrow> holds_forall b (iterate_sem m (Assume b;; C) S)"
      and "holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
      and "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} Assume b;; C {conj (I (Suc n)) (low_exp b)}"
      and "conj (I 0) (low_exp b) S"
    shows "sem (while_cond b C) S = iterate_sem n (Assume b;; C) S"
proof -
  have "\<And>m. m > n \<Longrightarrow> iterate_sem m (Assume b;; C) S = {}"
    using assms(2) false_then_empty_later by blast
  moreover have "sem (While (Assume b;; C)) S =
  (\<Union>m\<in>{m|m. m < n}. iterate_sem m (Assume b ;; C) S) \<union> iterate_sem n (Assume b ;; C) S \<union> (\<Union>m\<in>{m|m. m > n}. iterate_sem m (Assume b ;; C) S)"
    using sem_while[of "Assume b;; C" S] split_union_triple by metis
  ultimately have "sem (While (Assume b;; C)) S = (\<Union>m\<in>{m|m. m < n}. iterate_sem m (Assume b ;; C) S) \<union> iterate_sem n (Assume b ;; C) S "
    by auto
  moreover have "\<And>m. m < n \<Longrightarrow> sem (Assume (lnot b)) (iterate_sem m (Assume b ;; C) S) = {}"
    using assms(1) sem_assume_low_exp(2) by blast
  then have "sem (Assume (lnot b)) (\<Union>m\<in>{m|m. m < n}. iterate_sem m (Assume b ;; C) S) = {}"
    by (simp add: sem_union_swap)
  then have "sem (while_cond b C) S = sem (Assume (lnot b)) (iterate_sem n (Assume b ;; C) S)"
    by (simp add: calculation sem_seq sem_union while_cond_def)
  then show ?thesis
    using assms(2) sem_assume_low_exp(1) by blast
qed

lemma while_synchronized_case_2:
  assumes "\<And>m. holds_forall b (iterate_sem m (Assume b;; C) S)"
      and "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} Assume b;; C {conj (I (Suc n)) (low_exp b)}"
      and "conj (I 0) (low_exp b) S"
  shows "sem (while_cond b C) S = {}"
proof -
  have "sem (While (Assume b ;; C)) S = (\<Union>n. iterate_sem n (Assume b ;; C) S)"
    by (simp add: sem_while)
  then have "holds_forall b (sem (While (Assume b;; C)) S)"
    by (metis (no_types, lifting) UN_iff assms(1) holds_forall_def)
  then show ?thesis
    by (simp add: sem_assume_low_exp(2) sem_seq while_cond_def)
qed

definition emp where
  "emp S \<longleftrightarrow> S = {}"

lemma holds_forall_empty:
  "holds_forall b {}"
  by (simp add: holds_forall_def)

definition exists where
  "exists I S \<longleftrightarrow> (\<exists>n. I n S)"

theorem while_synchronized:
  assumes "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} C {conj (I (Suc n)) (low_exp b)}"
  shows "\<Turnstile> {conj (I 0) (low_exp b)} while_cond b C {conj (disj (exists I) emp) (holds_forall (lnot b))}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "conj (I 0) (low_exp b) S"
  have triple: "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} Assume b ;; C {conj (I (Suc n)) (low_exp b)}"
  proof (rule hyper_hoare_tripleI)
    fix n S assume "conj (I n) (holds_forall b) S"
    then have "sem (Assume b) S = S"
      by (simp add: conj_def sem_assume_low_exp(1))
    then show "conj (I (Suc n)) (low_exp b) (sem (Assume b ;; C) S)"
      by (metis \<open>conj (I n) (holds_forall b) S\<close> assms hyper_hoare_tripleE sem_seq)
  qed
  show "conj (disj (exists I) emp) (holds_forall (lnot b)) (sem (while_cond b C) S)"
  proof (cases "\<forall>m. holds_forall b (iterate_sem m (Assume b;; C) S)")
    case True
    then have "sem (while_cond b C) S = {}"
      using while_synchronized_case_2[of b C S I]
      by (metis (no_types, opaque_lifting) asm0 assms hyper_hoare_tripleI conj_def sem_assume_low_exp(1) seq_rule)
    then show ?thesis
      by (simp add: disj_def conj_def emp_def holds_forall_empty)
  next
    case False
    then have F: "\<not> (\<forall>m. holds_forall b (iterate_sem m (Assume b;; C) S))" by simp
    have "\<exists>n. (\<forall>m. m < n \<longrightarrow> holds_forall b (iterate_sem m (Assume b;; C) S)) \<and> holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
    proof (cases "\<exists>n. \<not> holds_forall b (iterate_sem n (Assume b;; C) S) \<and> iterate_sem n (Assume b;; C) S \<noteq> {}")
      case True
      then obtain n where "\<not> holds_forall b (iterate_sem n (Assume b;; C) S) \<and> iterate_sem n (Assume b;; C) S \<noteq> {}"
        by blast
      then have "holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
        by (metis asm0 conj_def low_exp_two_cases triple while_synchronized_rec)
      moreover have "\<And>m. m < n \<Longrightarrow> holds_forall b (iterate_sem m (Assume b;; C) S)"
      proof -
        fix m assume asm1: "m < n"
        show "holds_forall b (iterate_sem m (Assume b;; C) S)"
        proof (rule ccontr)
          assume "\<not> holds_forall b (iterate_sem m (Assume b ;; C) S)"
          then have "holds_forall (lnot b) (iterate_sem m (Assume b;; C) S)"
            by (metis asm0 conj_def low_exp_two_cases triple while_synchronized_rec)
          then have "iterate_sem n (Assume b;; C) S = {}"
            using asm1 false_then_empty_later by blast
          then show False
            using \<open>\<not> holds_forall b (iterate_sem n (Assume b ;; C) S) \<and> iterate_sem n (Assume b ;; C) S \<noteq> {}\<close> by fastforce
        qed
      qed
      ultimately show ?thesis 
        by blast
    next
      case False
      then have "\<And>n. holds_forall b (iterate_sem n (Assume b;; C) S)"
        using holds_forall_empty by fastforce
      then show ?thesis using F by blast
    qed
    then obtain n where "\<And>m. m < n \<Longrightarrow> holds_forall b (iterate_sem m (Assume b;; C) S)"
      and "holds_forall (lnot b) (iterate_sem n (Assume b;; C) S)"
      by blast
    then have "sem (while_cond b C) S = iterate_sem n (Assume b;; C) S"
      using triple
    proof (rule while_synchronized_case_1)
    qed (simp_all add: asm0)
    moreover have "I n (iterate_sem n (Assume b;; C) S)"
    proof (cases n)
      case 0
      then show ?thesis
        by (metis asm0 iterate_sem.simps(1) conj_def)
    next
      case (Suc k)
      then have "conj (I k) (low_exp b) (iterate_sem k (Assume b ;; C) S) \<or> holds_forall (lnot b) (iterate_sem k (Assume b ;; C) S)"
        using while_synchronized_rec[of I b C S k] asm0 triple by blast      
      then show ?thesis
      proof (cases "conj (I k) (low_exp b) (iterate_sem k (Assume b ;; C) S)")
        case True
        then show ?thesis
          using conj_def[of _ "holds_forall b"] conj_def[of _ "low_exp b"] Suc
            \<open>\<And>m. m < n \<Longrightarrow> holds_forall b (iterate_sem m (Assume b ;; C) S)\<close> assms
            hyper_hoare_triple_def[of ] iterate_sem.simps(2) lessI sem_assume_low_exp(1)[of b "iterate_sem k (Assume b ;; C) S"]
            sem_seq[of "Assume b" C] by metis
      next
        case False
        then show ?thesis
          by (metis F Suc \<open>\<And>m. m < n \<Longrightarrow> holds_forall b (iterate_sem m (Assume b ;; C) S)\<close> \<open>conj (I k) (low_exp b) (iterate_sem k (Assume b ;; C) S) \<or> holds_forall (lnot b) (iterate_sem k (Assume b ;; C) S)\<close> empty_iff false_then_empty_later holds_forall_def not_less_eq)
      qed
    qed
    ultimately show ?thesis
      by (metis disj_def Loops.exists_def \<open>holds_forall (lnot b) (iterate_sem n (Assume b ;; C) S)\<close> conj_def)
  qed
qed

lemma WhileSync_simpler:
  assumes "\<Turnstile> {conj I (holds_forall b)} C {conj I (low_exp b)}"
  shows "\<Turnstile> {conj I (low_exp b)} while_cond b C {conj (disj I emp) (holds_forall (lnot b))}"
  using assms while_synchronized[of "\<lambda>n. I"]
  by (simp add: disj_def Loops.exists_def conj_def hyper_hoare_triple_def)

definition if_then where
  "if_then b C = If (Assume b;; C) (Assume (lnot b))"

definition filter_exp where
  "filter_exp b S = Set.filter (b \<circ> snd) S"

lemma filter_exp_union:
  "filter_exp b (S1 \<union> S2) = filter_exp b S1 \<union> filter_exp b S2" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then show "x \<in> ?B"
    proof (cases "x \<in> S1")
      case True
      then show ?thesis
        by (metis UnI1 \<open>x \<in> filter_exp b (S1 \<union> S2)\<close> filter_exp_def member_filter)
    next
      case False
      then show ?thesis
        by (metis Un_iff \<open>x \<in> filter_exp b (S1 \<union> S2)\<close> filter_exp_def member_filter)
    qed
  qed
  show "?B \<subseteq> ?A"
    by (simp add: filter_exp_def subset_iff)
qed

lemma filter_exp_union_general:
  "filter_exp b (\<Union>x. f x) = (\<Union>x. filter_exp b (f x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix y assume "y \<in> ?A"
    then obtain x where "y \<in> f x"
      by (metis UN_iff filter_exp_def member_filter)
    then show "y \<in> ?B"
      by (metis UN_iff \<open>y \<in> filter_exp b (\<Union> (range f))\<close> filter_exp_def member_filter)
  qed
  show "?B \<subseteq> ?A"
    by (simp add: filter_exp_def subset_iff)
qed

lemma filter_exp_contradict:
  "filter_exp b (filter_exp (lnot b) S) = {}"
  by (metis (mono_tags, lifting) all_not_in_conv filter_exp_def lnot_def member_filter o_apply)

lemma filter_exp_same:
  "filter_exp b (filter_exp b S) = filter_exp b S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    by (metis filter_exp_def member_filter subsetI)
  show "?B \<subseteq> ?A"
    by (metis filter_exp_def member_filter subrelI)
qed

lemma if_then_sem:
  "sem (if_then b C) S = sem C (filter_exp b S) \<union> filter_exp (lnot b) S"
  by (simp add: assume_sem filter_exp_def if_then_def sem_if sem_seq)

fun union_up_to_n where
  "union_up_to_n C S 0 = iterate_sem 0 C S"
| "union_up_to_n C S (Suc n) = iterate_sem (Suc n) C S \<union> union_up_to_n C S n"

lemma union_up_to_increasing:
  assumes "m \<le> n"
  shows "union_up_to_n C S m \<subseteq> union_up_to_n C S n"
  using assms
proof (induct "n - m" arbitrary: m n)
  case (Suc x)
  then show ?case
    by (simp add: lift_Suc_mono_le)
qed (simp)

lemma union_union_up_to_n_equiv_aux:
  "union_up_to_n C S n \<subseteq> (\<Union>m. iterate_sem m C S)"
proof (induct n)
  case 0
  then show ?case
    by (metis UN_upper iso_tuple_UNIV_I union_up_to_n.simps(1))
next
  case (Suc n)
  show ?case
  proof
    fix x assume "x \<in> union_up_to_n C S (Suc n)" (* \<subseteq> (\<Union>m. iterate_sem m C S) *)
    then have "x \<in> iterate_sem (Suc n) C S \<or> x \<in> union_up_to_n C S n"
      by simp
    then show "x \<in> (\<Union>m. iterate_sem m C S)"
      using Suc by blast
  qed
qed

lemma union_union_up_to_n_equiv:
  "(\<Union>n. union_up_to_n C S n) = (\<Union>n. iterate_sem n C S)" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
    by (metis (no_types, lifting) SUP_subset_mono UnCI subsetI union_up_to_n.elims)
  show "?A \<subseteq> ?B"
    by (simp add: SUP_le_iff union_union_up_to_n_equiv_aux)
qed


lemma filter_exp_union_itself:
  "filter_exp b S \<union> S = S"
  by (metis Un_absorb1 filter_exp_def member_filter subsetI)

lemma iterate_sem_equiv:
  "iterate_sem m (if_then b C) S
  = filter_exp (lnot b) (union_up_to_n (Assume b;; C) S m) \<union> iterate_sem m (Assume b;; C) S"
proof (induct m)
  case 0
  have "union_up_to_n (Assume b ;; C) S 0 = S"
    by auto
  then show "iterate_sem 0 (if_then b C) S = filter_exp (lnot b) (union_up_to_n (Assume b ;; C) S 0) \<union> iterate_sem 0 (Assume b ;; C) S"
    using filter_exp_def
    by (metis Un_commute iterate_sem.simps(1) member_filter subset_iff sup.order_iff)
next
  case (Suc m)

  let ?S = "iterate_sem m (if_then b C) S"
  let ?SU = "union_up_to_n (Assume b ;; C) S m"
  let ?SN = "iterate_sem m (Assume b ;; C) S"
  have "iterate_sem (Suc m) (if_then b C) S = sem C (filter_exp b ?S) \<union> filter_exp (lnot b) ?S"
    by (simp add: if_then_sem)
  also have "... = sem C (filter_exp b (filter_exp (lnot b) ?SU)) \<union> sem C (filter_exp b ?SN)
  \<union> filter_exp (lnot b) (filter_exp (lnot b) ?SU) \<union> filter_exp (lnot b) ?SN"
    by (simp add: Suc filter_exp_union sem_union sup_assoc)
  also have "... = sem C (filter_exp b ?SN) \<union> filter_exp (lnot b) ?SU \<union> filter_exp (lnot b) ?SN"
    by (metis Un_empty_left filter_exp_contradict filter_exp_same sem_union)
  moreover have "iterate_sem (Suc m) (Assume b ;; C) S = sem C (filter_exp b ?SN)"
    by (simp add: assume_sem filter_exp_def sem_seq)
  moreover have "union_up_to_n (Assume b ;; C) S (Suc m) = sem C (filter_exp b ?SN) \<union> ?SU"
    using calculation(3) by force
  moreover have "filter_exp (lnot b) (union_up_to_n (Assume b ;; C) S (Suc m)) \<union> iterate_sem (Suc m) (Assume b ;; C) S
  = filter_exp (lnot b) (sem C (filter_exp b ?SN) \<union> ?SU) \<union> sem C (filter_exp b ?SN)"
    using calculation(3) by force
  then have "... = filter_exp (lnot b) ?SU \<union> sem C (filter_exp b ?SN)"
    using filter_exp_union_itself[of "lnot b"] filter_exp_union[of "lnot b"] Un_commute sup_assoc by blast
  moreover have "?SN \<subseteq> ?SU"
    by (metis UnCI subsetI union_up_to_n.elims)
  ultimately have "filter_exp (lnot b) ?SU \<union> sem C (filter_exp b ?SN)
  = sem C (filter_exp b ?SN) \<union> filter_exp (lnot b) ?SU \<union> filter_exp (lnot b) ?SN"
    using filter_exp_union[of "lnot b" ?SU ?SN]
    using Un_commute[of "filter_exp (lnot b) ?SU" "sem C (filter_exp b ?SN)"]
      sup.orderE sup_assoc[of "sem C (filter_exp b ?SN)"] by metis
  then show ?case
    using \<open>filter_exp (lnot b) (sem C (filter_exp b (iterate_sem m (Assume b ;; C) S)) \<union> union_up_to_n (Assume b ;; C) S m) \<union> sem C (filter_exp b (iterate_sem m (Assume b ;; C) S)) = filter_exp (lnot b) (union_up_to_n (Assume b ;; C) S m) \<union> sem C (filter_exp b (iterate_sem m (Assume b ;; C) S))\<close> \<open>iterate_sem (Suc m) (Assume b ;; C) S = sem C (filter_exp b (iterate_sem m (Assume b ;; C) S))\<close> \<open>iterate_sem (Suc m) (if_then b C) S = sem C (filter_exp b (iterate_sem m (if_then b C) S)) \<union> filter_exp (lnot b) (iterate_sem m (if_then b C) S)\<close> \<open>sem C (filter_exp b (filter_exp (lnot b) (union_up_to_n (Assume b ;; C) S m))) \<union> sem C (filter_exp b (iterate_sem m (Assume b ;; C) S)) \<union> filter_exp (lnot b) (filter_exp (lnot b) (union_up_to_n (Assume b ;; C) S m)) \<union> filter_exp (lnot b) (iterate_sem m (Assume b ;; C) S) = sem C (filter_exp b (iterate_sem m (Assume b ;; C) S)) \<union> filter_exp (lnot b) (union_up_to_n (Assume b ;; C) S m) \<union> filter_exp (lnot b) (iterate_sem m (Assume b ;; C) S)\<close> \<open>sem C (filter_exp b (iterate_sem m (if_then b C) S)) \<union> filter_exp (lnot b) (iterate_sem m (if_then b C) S) = sem C (filter_exp b (filter_exp (lnot b) (union_up_to_n (Assume b ;; C) S m))) \<union> sem C (filter_exp b (iterate_sem m (Assume b ;; C) S)) \<union> filter_exp (lnot b) (filter_exp (lnot b) (union_up_to_n (Assume b ;; C) S m)) \<union> filter_exp (lnot b) (iterate_sem m (Assume b ;; C) S)\<close> by auto
qed


lemma sem_while_with_if:
  "sem (while_cond b C) S = filter_exp (lnot b) (\<Union>n. iterate_sem n (if_then b C) S)"
proof -
  have "(\<Union>n. iterate_sem n (if_then b C) S)
  = (\<Union>n. filter_exp (lnot b) (union_up_to_n (Assume b;; C) S n) \<union> iterate_sem n (Assume b;; C) S)"
    by (simp add: iterate_sem_equiv)
  also have "... = filter_exp (lnot b) (\<Union>n. union_up_to_n (Assume b;; C) S n) \<union> (\<Union>n. iterate_sem n (Assume b;; C) S)"
    by (simp add: complete_lattice_class.SUP_sup_distrib filter_exp_union_general)
  also have "... = filter_exp (lnot b) (\<Union>n. iterate_sem n (Assume b;; C) S) \<union> (\<Union>n. iterate_sem n (Assume b;; C) S)"
    by (simp add: union_union_up_to_n_equiv)
  also have "... = (\<Union>n. iterate_sem n (Assume b;; C) S)"
    by (meson filter_exp_union_itself)
  moreover have "sem (while_cond b C) S = filter_exp (lnot b) (\<Union>n. iterate_sem n (Assume b ;; C) S)"
    by (simp add: assume_sem filter_exp_def sem_seq sem_while while_cond_def)
  ultimately show ?thesis
    by presburger
qed

lemma iterate_sem_assume_increasing:
  "filter_exp (lnot b) (iterate_sem n (if_then b C) S) \<subseteq> filter_exp (lnot b) (iterate_sem (Suc n) (if_then b C) S)"
  by (metis (no_types, lifting) UnCI filter_exp_def if_then_sem iterate_sem.simps(2) member_filter subsetI)

lemma iterate_sem_assume_increasing_union_up_to:
  "filter_exp (lnot b) (iterate_sem n (if_then b C) S) = filter_exp (lnot b) (union_up_to_n (if_then b C) S n)"
proof (induct n)
  case (Suc n)
  then show ?case
    by (metis filter_exp_union iterate_sem_assume_increasing sup.orderE union_up_to_n.simps(2))
qed (simp)

(* Set becomes larger *)
definition ascending :: "(nat \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "ascending S \<longleftrightarrow> (\<forall>n m. n \<le> m \<longrightarrow> S n \<subseteq> S m)"

lemma ascendingI_direct:
  assumes "\<And>n m. n \<le> m \<Longrightarrow> S n \<subseteq> S m"
  shows "ascending S"
  by (simp add: ascending_def assms)

lemma ascendingI:
  assumes "\<And>n. S n \<subseteq> S (Suc n)"
  shows "ascending S"
proof (rule ascendingI_direct)
  fix n m :: nat assume asm0: "n \<le> m"
  moreover have "n \<le> m \<Longrightarrow> S n \<subseteq> S m"
  proof (induct "m - n" arbitrary: m n)
    case (Suc x)
    then show ?case
      using assms lift_Suc_mono_le by blast
  qed (simp)
  ultimately show "S n \<subseteq> S m" 
    by blast
qed



definition upwards_closed where
  "upwards_closed P P_inf \<longleftrightarrow> (\<forall>S. ascending S \<and> (\<forall>n. P n (S n)) \<longrightarrow> P_inf (\<Union>n. S n))"

lemma upwards_closedI:
  assumes "\<And>S. ascending S \<Longrightarrow> (\<forall>n. P n (S n)) \<Longrightarrow> P_inf (\<Union>n. S n)"
  shows "upwards_closed P P_inf"
  using assms upwards_closed_def by blast

lemma upwards_closedE:
  assumes "upwards_closed P P_inf"
      and "ascending S"
      and "\<And>n. P n (S n)"
    shows "P_inf (\<Union>n. S n)"
  using assms(1) assms(2) assms(3) upwards_closed_def by blast

lemma ascending_iterate_filter:
  "ascending (\<lambda>n. filter_exp (lnot b) (union_up_to_n (if_then b C) S n))"
  by (metis ascendingI iterate_sem_assume_increasing iterate_sem_assume_increasing_union_up_to)


theorem while_general:
  assumes "\<And>n. \<Turnstile> {P n} if_then b C {P (Suc n)}"
      and "\<And>n. \<Turnstile> {P n} Assume (lnot b) {Q n}"
      and "upwards_closed Q Q_inf"
    shows "\<Turnstile> {P 0} while_cond b C {conj Q_inf (holds_forall (lnot b))}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "P 0 S"
  then have "\<And>n. P n (iterate_sem n (if_then b C) S)"
    by (meson assms(1) indexed_invariant_then_power)
  then have "\<And>n. Q n (filter_exp (lnot b) (union_up_to_n (if_then b C) S n))"
    by (metis assms(2) assume_sem filter_exp_def hyper_hoare_triple_def iterate_sem_assume_increasing_union_up_to)
  moreover have "ascending (\<lambda>n. filter_exp (lnot b) (union_up_to_n (if_then b C) S n))"
    by (simp add: ascending_iterate_filter)
  ultimately have "Q_inf (sem (while_cond b C) S)"
    by (metis (no_types, lifting) SUP_cong assms(3) filter_exp_union_general iterate_sem_assume_increasing_union_up_to sem_while_with_if upwards_closed_def)
  then show "Logic.conj Q_inf (holds_forall (lnot b)) (sem (while_cond b C) S)"
    by (simp add: conj_def filter_exp_def holds_forall_def sem_while_with_if)
qed

definition while_loop_assertion_n where
  "while_loop_assertion_n C S0 n S \<longleftrightarrow> (S = union_up_to_n C S0 n)"

definition while_loop_assertion_inf where
  "while_loop_assertion_inf C S0 S \<longleftrightarrow> (S = (\<Union>n. union_up_to_n C S0 n))"

(* Probably could have completeness with this? *)
lemma while_loop_assertion_upwards_closed:
  "upwards_closed (while_loop_assertion_n C S0) (while_loop_assertion_inf C S0)"
proof (rule upwards_closedI)
  fix S assume asm0: "ascending S" "\<forall>n. while_loop_assertion_n C S0 n (S n)"
  then have "\<And>n. S n = union_up_to_n C S0 n"
    by (simp add: while_loop_assertion_n_def)
  then have "\<Union> (range S) = (\<Union>n. union_up_to_n C S0 n)"
    by auto
  then show "while_loop_assertion_inf C S0 (\<Union> (range S))"
    by (simp add: while_loop_assertion_inf_def)
qed

(* Each element is either always in the sets, or never in the sets, from some point *)
definition converges_sets where
  "converges_sets S \<longleftrightarrow> (\<forall>x. \<exists>n. (\<forall>m. m \<ge> n \<longrightarrow> (x \<in> S m)) \<or> (\<forall>m. m \<ge> n \<longrightarrow> (x \<notin> S m)))"

lemma converges_setsI:
  assumes "\<And>x. \<exists>n. (\<forall>m. m \<ge> n \<longrightarrow> (x \<in> S m)) \<or> (\<forall>m. m \<ge> n \<longrightarrow> (x \<notin> S m))"
  shows "converges_sets S"
  by (simp add: assms converges_sets_def)

lemma ascending_converges:
  assumes "ascending S"
  shows "converges_sets S"
proof (rule converges_setsI)
  fix x
  show "\<exists>n. (\<forall>m\<ge>n. x \<in> S m) \<or> (\<forall>m\<ge>n. x \<notin> S m)"
  proof (cases "x \<in> (\<Union>n. S n)")
    case True
    then show ?thesis
      by (meson ascending_def assms in_mono)
  qed (blast)
qed

(* Set becomes smaller *)
definition descending :: "(nat \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "descending S \<longleftrightarrow> (\<forall>n m. n \<ge> m \<longrightarrow> S n \<subseteq> S m)"

lemma descending_converges:
  assumes "descending S"
  shows "converges_sets S"
proof (rule converges_setsI)
  fix x
  show "\<exists>n. (\<forall>m\<ge>n. x \<in> S m) \<or> (\<forall>m\<ge>n. x \<notin> S m)"
  proof (cases "x \<in> (\<Inter>n. S n)")
    case False
    then show ?thesis
      by (meson assms descending_def in_mono)
  qed (blast)
qed


definition limit_sets where
  "limit_sets S = {x |x. \<exists>n. \<forall>m. m \<ge> n \<longrightarrow> (x \<in> S m)}"

lemma in_limit_sets:
  "x \<in> limit_sets S \<longleftrightarrow> (\<exists>n. \<forall>m. m \<ge> n \<longrightarrow> (x \<in> S m))"
  by (simp add: limit_sets_def)

lemma ascending_limits_union:
  assumes "ascending S"
  shows "limit_sets S = (\<Union>n. S n)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" using limit_sets_def[of S] by auto
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    then obtain n where "x \<in> S n"
      by blast
    then have "\<forall>m. m \<ge> n \<longrightarrow> (x \<in> S m)"
      by (meson ascending_def assms subsetD)
    then show "x \<in> ?A"
      using limit_sets_def[of S] by auto
  qed
qed

lemma descending_limits_union:
  assumes "descending S"
  shows "limit_sets S = (\<Inter>n. S n)" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A" using limit_sets_def[of S] by fastforce
  show "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then obtain n where "\<forall>m. m \<ge> n \<longrightarrow> (x \<in> S m)"
      using limit_sets_def[of S] by blast
    then have "\<forall>m. m < n \<longrightarrow> (x \<in> S m)"
      by (meson assms descending_def lessI less_imp_le_nat subsetD)
    then show "x \<in> ?B"
      by (meson INT_I \<open>\<forall>m\<ge>n. x \<in> S m\<close> linorder_not_le)
  qed
qed



definition t_closed where
  "t_closed P P_inf \<longleftrightarrow> (\<forall>S. converges_sets S \<and> (\<forall>n. P n (S n)) \<longrightarrow> P_inf (limit_sets S))"

lemma t_closed_implies_u_closed:
  assumes "t_closed P P_inf"
  shows "upwards_closed P P_inf"
proof (rule upwards_closedI)
  fix S assume "ascending S" "\<forall>n. P n (S n)"
  then have "converges_sets S"
    using ascending_converges by blast
  then show "P_inf (\<Union> (range S))"
    by (metis \<open>\<forall>n. P n (S n)\<close> \<open>ascending S\<close> ascending_limits_union assms t_closed_def)
qed

(* forall assertions *)
definition downwards_closed where
  "downwards_closed P_inf \<longleftrightarrow> (\<forall>S S'. S \<subseteq> S' \<and> P_inf S' \<longrightarrow> P_inf S)"

(* Slight change compared to Ellora paper *)
definition d_closed where
  "d_closed P P_inf \<longleftrightarrow> t_closed P P_inf \<and> downwards_closed P_inf"

lemma converges_to_merged:
  assumes "\<And>x. x \<in> S_inf \<Longrightarrow> \<exists>n. \<forall>m. m \<ge> n \<longrightarrow> (x \<in> S (m::nat))"
      and "\<And>x. x \<notin> S_inf \<Longrightarrow> \<exists>n. \<forall>m. m \<ge> n \<longrightarrow> (x \<notin> S m)"
    shows "converges_sets S \<and> limit_sets S = S_inf"
proof (rule conjI)
  show "converges_sets S" using converges_setsI assms by metis
  show "limit_sets S = S_inf" (is "?A = ?B")
  proof
    show "?B \<subseteq> ?A"
      by (simp add: assms(1) limit_sets_def subsetI)
    show "?A \<subseteq> ?B"
    proof
      fix x assume "x \<in> ?A"
      then obtain n where n_def: "\<forall>m. m \<ge> n \<longrightarrow> (x \<in> S m)"
        using in_limit_sets by metis
      show "x \<in> ?B"
      proof (rule ccontr)
        assume "x \<notin> S_inf"
        then obtain n' where "\<forall>m. m \<ge> n' \<longrightarrow> (x \<notin> S m)"
          using assms(2) by presburger
        then have "x \<in> S (max n n') \<and> x \<notin> S (max n n')"
          using n_def by fastforce
        then show False by blast
      qed
    qed
  qed
qed

lemma ascending_union_up:
  "ascending (\<lambda>n. union_up_to_n C S n)"
  by (simp add: ascending_def union_up_to_increasing)

(* actually ascending... *)
lemma converges_union:
  "converges_sets (\<lambda>n. union_up_to_n C S n) \<and> limit_sets (\<lambda>n. union_up_to_n C S n) = (\<Union>n. union_up_to_n C S n)"
proof (rule converges_to_merged)
  fix x
  show "x \<in> \<Union> (range (union_up_to_n C S)) \<Longrightarrow> \<exists>n. \<forall>m\<ge>n. x \<in> union_up_to_n C S m"
    by (meson UN_iff subset_eq union_up_to_increasing)
  show "x \<notin> \<Union> (range (union_up_to_n C S)) \<Longrightarrow> \<exists>n. \<forall>m\<ge>n. x \<notin> union_up_to_n C S m"
    by blast
qed


theorem while_d:
  assumes "\<And>n. \<Turnstile> {P n} if_then b C {P (Suc n)}"
      and "upwards_closed P P_inf"
      and "\<And>n. downwards_closed (P n)" \<comment>\<open>Satisfied by hyper-assertions that do not existentially quantify over states\<close>
    shows "\<Turnstile> {P 0} while_cond b C {conj P_inf (holds_forall (lnot b))}"
  using assms(1)
proof (rule while_general)
  show "upwards_closed P P_inf"
    using assms(2) by blast
  fix n show "\<Turnstile> {P n} Assume (lnot b) {P n}"
  proof (rule hyper_hoare_tripleI)
    fix S assume "P n S"
    moreover have "sem (Assume (lnot b)) S \<subseteq> S"
      by (metis assume_sem member_filter subsetI)
    ultimately show "P n (sem (Assume (lnot b)) S)"
      by (meson assms(3) downwards_closed_def)
  qed
qed



lemma in_union_up_to:
  "x \<in> union_up_to_n C S n \<longleftrightarrow> (\<exists>m. m \<le> n \<and> x \<in> iterate_sem m C S)"
proof (induct n)
  case (Suc n)
  then show ?case
    by (metis UnCI UnE le_SucE le_SucI order_refl union_up_to_n.simps(2))
qed (simp)


theorem rule_while_terminates_strong:
  assumes "\<And>n. n < m \<Longrightarrow> \<Turnstile> {P n} if_then b C {P (Suc n)}"
      and "\<And>S. P m S \<longrightarrow> holds_forall (lnot b) S"
  shows "\<Turnstile> {P 0} while_cond b C {P m}"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "P 0 S"
  let ?S = "iterate_sem m (if_then b C) S"
  let ?S' = "iterate_sem (Suc m) (if_then b C) S"
  have "P m ?S"
    using asm0 assms(1) indexed_invariant_then_power_bounded by blast
  then have "holds_forall (lnot b) ?S"    
    using assms(2) by auto
  moreover have "sem (while_cond b C) S = filter_exp (lnot b) (\<Union>n. iterate_sem n (Assume b ;; C) S)"
    by (simp add: assume_sem filter_exp_def sem_seq sem_while while_cond_def)


(* this is constant *)
  then have "P m (filter_exp (lnot b) (union_up_to_n (Assume b;; C) S m) \<union> iterate_sem m (Assume b;; C) S)"
    by (metis \<open>P m (iterate_sem m (if_then b C) S)\<close> iterate_sem_equiv)

  moreover have "iterate_sem m (Assume b;; C) S \<subseteq> filter_exp (lnot b) (union_up_to_n (Assume b;; C) S m)"
  proof
    fix x assume "x \<in> iterate_sem m (Assume b;; C) S"
    then have "x \<in> union_up_to_n (Assume b;; C) S m"
      by (metis UnCI union_up_to_n.elims)
    then have "x \<in> ?S"
      by (simp add: \<open>x \<in> iterate_sem m (Assume b ;; C) S\<close> iterate_sem_equiv)
    then have "lnot b (snd x)"
      by (metis calculation(1) holds_forall_def)
    then show "x \<in> filter_exp (lnot b) (union_up_to_n (Assume b;; C) S m)"
      using \<open>x \<in> union_up_to_n (Assume b;; C) S m\<close> filter_exp_def
      by force
  qed
  moreover have "filter_exp (lnot b) (\<Union>n. iterate_sem n (Assume b ;; C) S)
  = filter_exp (lnot b) (union_up_to_n (Assume b;; C) S m)"
  proof -
    have "\<And>n. n > m \<Longrightarrow> iterate_sem n (Assume b ;; C) S = {}"
    proof -
      fix n show "n > m \<Longrightarrow> iterate_sem n (Assume b ;; C) S = {}"
      proof (induct "n - m - 1")
        case 0
        then show ?case
          by (metis (no_types, lifting) UnCI calculation(1) false_then_empty_later holds_forall_def iterate_sem_equiv)
      next
        case (Suc x)
        then show ?case
          by (metis (no_types, lifting) UnCI calculation(1) false_then_empty_later holds_forall_def iterate_sem_equiv)
      qed
    qed
    moreover have "union_up_to_n (Assume b;; C) S m = (\<Union>n. union_up_to_n (Assume b;; C) S n)" (is "?A = ?B")
    proof
      show "?B \<subseteq> ?A"
      proof
        fix x assume "x \<in> ?B"
        then obtain n where "x \<in> union_up_to_n (Assume b;; C) S n"
          by blast
        then show "x \<in> ?A"
          by (metis calculation empty_iff in_union_up_to linorder_not_le)
      qed
    qed (blast)
    then have "(\<Union>n. iterate_sem n (Assume b ;; C) S) = union_up_to_n (Assume b;; C) S m"
      by (simp add: union_union_up_to_n_equiv)
    then show ?thesis
      by auto
  qed
  ultimately show "P m (sem (while_cond b C) S)"
    by (simp add: \<open>sem (while_cond b C) S = filter_exp (lnot b) (\<Union>n. iterate_sem n (Assume b ;; C) S)\<close> sup.absorb1)
qed


lemma false_state_in_if_then:
  assumes "\<phi> \<in> S"
      and "\<not> b (snd \<phi>)"
    shows "\<phi> \<in> sem (if_then b C) S"
proof -
  have "\<phi> \<in> sem (Assume (lnot b)) S"
    by (metis SemAssume assms(1) assms(2) in_sem lnot_def prod.collapse)
  then show ?thesis
    by (simp add: assume_sem filter_exp_def if_then_sem)
qed

lemma false_state_in_while_cond_aux:
  assumes "\<phi> \<in> S"
      and "\<not> b (snd \<phi>)"
    shows "\<phi> \<in> iterate_sem n (if_then b C) S"
proof (induct n)
  case 0
  then show ?case
    by (simp add: assms(1))
next
  case (Suc n)
  then show ?case
    by (simp add: assms(2) false_state_in_if_then)
qed

lemma false_state_in_while_cond:
  assumes "\<phi> \<in> S"
      and "\<not> b (snd \<phi>)"
    shows "\<phi> \<in> sem (while_cond b C) S"
proof -
  have "\<phi> \<in> (\<Union>n. iterate_sem n (if_then b C) S)"
    by (simp add: assms(1) assms(2) false_state_in_while_cond_aux)
  then show ?thesis using sem_while_with_if[of b C S] filter_exp_def lnot_def
    by (metis assms(2) comp_apply member_filter)
qed

theorem while_exists:
  assumes "\<And>\<phi>. \<Turnstile> { P \<phi> } while_cond b C { Q \<phi> }"
  shows "\<Turnstile> { (\<lambda>S. \<exists>\<phi> \<in> S. \<not> b (snd \<phi>) \<and> P \<phi> S) } while_cond b C { (\<lambda>S. \<exists>\<phi> \<in> S. Q \<phi> S) }"
proof (rule hyper_hoare_tripleI)
  fix S assume "\<exists>\<phi>\<in>S. \<not> b (snd \<phi>) \<and> P \<phi> S"
  then obtain \<phi> where asm0: "\<phi>\<in>S" "\<not> b (snd \<phi>) \<and> P \<phi> S" by blast
  then have "Q \<phi> (sem (while_cond b C) S)"
    using assms hyper_hoare_tripleE by blast
  then show "\<exists>\<phi>\<in>sem (while_cond b C) S. Q \<phi> (sem (while_cond b C) S)"
    using asm0(1) asm0(2) false_state_in_while_cond by blast
qed

lemma sem_while_cond_union_up_to:
  "sem (while_cond b C) S = filter_exp (lnot b) (\<Union>n. union_up_to_n (if_then b C) S n)"
  by (simp add: sem_while_with_if union_union_up_to_n_equiv)

lemma iterate_sem_sum:
  "iterate_sem n C (iterate_sem m C S) = iterate_sem (n + m) C S"
  by (induct n) simp_all


lemma unroll_while_sem:
  "sem (while_cond b C) (iterate_sem n (if_then b C) S) = sem (while_cond b C) S"
proof -
  let ?S = "iterate_sem n (if_then b C) S"
  have "filter_exp (lnot b) (\<Union>m. iterate_sem m (if_then b C) S) = filter_exp (lnot b) (\<Union>m. iterate_sem (n + m) (if_then b C) S)" (is "?A = ?B")
  proof
    show "?A \<subseteq> ?B"
    proof
      fix x assume "x \<in> ?A"
      then obtain m where "x \<in> iterate_sem m (if_then b C) S" "\<not> b (snd x)"
        using filter_exp_def lnot_def
        by (metis (no_types, lifting) UN_iff comp_apply member_filter)
      then have "x \<in> iterate_sem (n + m) (if_then b C) S"
        using false_state_in_while_cond_aux[of x "iterate_sem m (if_then b C) S" b n C] iterate_sem_sum[of n "if_then b C" m S]
        by blast
      then have "x \<in> (\<Union>m. iterate_sem (n + m) (if_then b C) S)"
        by blast
      then show "x \<in> ?B"
        by (metis \<open>x \<in> filter_exp (lnot b) (\<Union>m. iterate_sem m (if_then b C) S)\<close> filter_exp_def member_filter)
    qed
    show "?B \<subseteq> ?A"
    proof
      fix x assume "x \<in> ?B"
      then obtain m where "x \<in> iterate_sem (n + m) (if_then b C) S" "\<not> b (snd x)"
        by (metis (no_types, lifting) UN_iff comp_apply filter_exp_def lnot_def member_filter)
      then show "x \<in> ?A"
        by (metis (no_types, lifting) UNIV_I UN_iff \<open>x \<in> filter_exp (lnot b) (\<Union>m. iterate_sem (n + m) (if_then b C) S)\<close> filter_exp_def member_filter)
    qed
  qed
  then show ?thesis
    using iterate_sem_sum[of _ "if_then b C" n S] sem_while_with_if[of b C S] sem_while_with_if[of b C ?S]
    by (simp add: add.commute)
qed


theorem while_unroll:
  assumes "\<And>n. n < m \<Longrightarrow> \<Turnstile> {P n} if_then b C {P (Suc n)}"
      and "\<Turnstile> {P m} while_cond b C {Q}"
    shows "\<Turnstile> {P 0} while_cond b C {Q}"
proof (rule hyper_hoare_tripleI)
  fix S assume "P 0 S"
  let ?S = "iterate_sem m (if_then b C) S"
  have "(\<forall>n. n < m \<longrightarrow> (\<Turnstile> {P n} if_then b C {P (Suc n)})) \<longrightarrow> P m ?S"
  proof (induct m)
    case 0
    then show ?case
      by (simp add: \<open>P 0 S\<close>)
  next
    case (Suc m)
    then show ?case
      by (simp add: hyper_hoare_triple_def)
  qed
  then have "P m ?S" using assms(1)
    by blast
  then have "Q (sem (while_cond b C) ?S)"
    using assms(2) hyper_hoare_tripleE by blast
  then show "Q (sem (while_cond b C) S)"
    by (metis unroll_while_sem)
qed








text \<open>Deriving LoopExit from NormalWhile, and ForLoop from LoopExit and Unroll\<close>

lemma while_desugared_easy:
  assumes "\<And>n. \<Turnstile> {I n} Assume b;; C {I (Suc n)}"
      and "\<Turnstile> { natural_partition I } Assume (lnot b) { Q }"
    shows "\<Turnstile> {I 0} while_cond b C { Q }"
  by (metis assms(1) assms(2) seq_rule while_cond_def while_rule)


corollary loop_exit:
  assumes "entails P (holds_forall (lnot b))"
  shows "\<Turnstile> {P} while_cond b C {P}"
proof -
  have "\<Turnstile> {(if (0::nat) = 0 then P else emp)} while_cond b C {P}"
  proof (rule while_desugared_easy[of "\<lambda>(n::nat). if n = 0 then P else emp" b C P])
    show "\<Turnstile> {natural_partition (\<lambda>(n::nat). if n = 0 then P else emp)} Assume (lnot b) {P}"
    proof (rule hyper_hoare_tripleI)
      fix S assume asm0: "natural_partition (\<lambda>(n::nat). if n = 0 then P else emp) S"
      then obtain F where "S = (\<Union>(n::nat). F n)" "\<And>(n::nat). (\<lambda>(n::nat). if n = 0 then P else emp) n (F n)"
        using natural_partitionE by blast
      then have "\<And>n. F (Suc n) = {}"
        by (metis (mono_tags, lifting) emp_def old.nat.distinct(2))
      moreover have "S = F 0"
      proof
        show "S \<subseteq> F 0"
        proof
          fix x assume "x \<in> S"
          then obtain n where "x \<in> F n"
            using \<open>S = \<Union> (range F)\<close> by blast
          then show "x \<in> F 0"
            by (metis calculation empty_iff gr0_implies_Suc zero_less_iff_neq_zero)
        qed
        show "F 0 \<subseteq> S"
          using \<open>S = \<Union> (range F)\<close> by blast
      qed
      ultimately have "P S"
        using \<open>\<And>n. (if n = 0 then P else emp) (F n)\<close> by presburger
      then show "P (sem (Assume (lnot b)) S)"
        by (metis assms entailsE sem_assume_low_exp(1))
    qed
    fix n :: nat
    show "\<Turnstile> {(if n = 0 then P else emp)} Assume b ;; C {if Suc n = 0 then P else emp}"
    proof (rule hyper_hoare_tripleI)
      fix S assume asm0: "(if n = 0 then P else emp) S"
      then show "(if Suc n = 0 then P else emp) (sem (Assume b ;; C) S)"
        by (metis (mono_tags, lifting) assms emp_def entailsE holds_forall_empty lnot_involution nat.distinct(1) sem_assume_low_exp_seq(2))
    qed
  qed
  then show ?thesis
    by fastforce
qed

corollary for_loop:
  assumes "\<And>n. n < m \<Longrightarrow> \<Turnstile> {P n} if_then b C {P (Suc n)}"
      and "entails (P m) (holds_forall (lnot b))"
    shows "\<Turnstile> {P 0} while_cond b C {P m}"
  using assms(1)
proof (rule while_unroll)
  show "\<Turnstile> {P m} while_cond b C {P m}"
    using assms(2) loop_exit by blast
qed


end