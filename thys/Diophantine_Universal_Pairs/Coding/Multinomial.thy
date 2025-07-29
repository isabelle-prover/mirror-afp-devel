theory Multinomial
  imports Main "HOL-Library.Disjoint_Sets"
begin

text \<open>The factorial of a list of natural numbers is the product of all factorials\<close>
fun mfact' :: "nat list \<Rightarrow> nat" where
  "mfact' [] = 1" |
  "mfact' (i # is) = (fact i :: nat) * mfact' is"

definition mfact :: "nat list \<Rightarrow> nat" where 
  "mfact i = (\<Prod>s<length i. fact (i ! s) :: nat)"

lemma mfact_Nil[simp]: "mfact [] = 1" 
  by (simp add: mfact_def)

lemma mfact_Cons[simp]: "mfact (i # is) = fact i * mfact is"
proof -
  have "(\<Prod>s<length is + 1. fact ((i # is) ! s)) =
    fact i * (\<Prod>s<length is. fact (is ! s))" proof -
    have "(\<Prod>s<length is + 1. fact ((i # is) ! s)) =
      (\<Prod>s<Suc (length is). fact ((i # is) ! s))" by auto
    also have "... = fact ((i # is) ! 0) *
      (\<Prod>s<length is. fact ((i # is) ! (Suc s)))"
      by (rule prod.lessThan_Suc_shift)
    also have "... = fact i * (\<Prod>s<length is. fact (is ! s))" by auto
    finally show ?thesis .
  qed
  thus ?thesis unfolding mfact_def by auto
qed

lemma mfact'_equiv: "mfact' = mfact" proof -
  have "mfact' xs = mfact xs" for xs by (induction xs; auto)
  thus ?thesis by auto
qed

text \<open>The "multi-power" of a list of natural numbers.\<close>
fun mpow' :: "'a::comm_semiring_1 list \<Rightarrow> nat list \<Rightarrow> 'a" where
  "mpow' [] ns = 1" |
  "mpow' ns [] = 1" |
  "mpow' (x # xs) (n # ns) = x ^ n * mpow' xs ns"

definition mpow :: "'a::comm_semiring_1 list \<Rightarrow> nat list \<Rightarrow> 'a" where 
  "mpow xs ns = (\<Prod>i<min (length xs) (length ns). (xs ! i) ^ (ns ! i))"

lemma mpow_Nil_any[simp]: "mpow [] ns = 1"
  by (simp add: mpow_def)

lemma mpow_any_Nil[simp]: "mpow xs [] = 1"
  by (simp add: mpow_def)

lemma mpow_Cons[simp]: "mpow (x # xs) (n # ns) = (x ^ n) * (mpow xs ns)"
proof -
  let ?l = "min (length xs) (length ns)"
  have "(\<Prod>i<?l. (x # xs) ! i ^ (n # ns) ! i) * (x # xs) ! ?l ^ (n # ns) ! ?l =
    x ^ n * (\<Prod>i<?l. xs ! i ^ ns ! i)" proof cases
    assume "?l = 0"
    thus ?thesis by auto
  next
    assume "?l \<noteq> 0"
    hence 0: "Suc (?l - 1) = ?l" by auto
    have "(\<Prod>i<?l. (x # xs) ! i ^ (n # ns) ! i) * (x # xs) ! ?l ^ (n # ns) ! ?l =
      (\<Prod>i<(Suc (?l - 1)). (x # xs) ! i ^ (n # ns) ! i) *
      (x # xs) ! ?l ^ (n # ns) ! ?l"
      unfolding 0 by auto
    also have "... = (x # xs) ! 0 ^ (n # ns) ! 0 *
      (\<Prod>i<(?l - 1). (x # xs) ! (Suc i) ^ (n # ns) ! (Suc i)) *
      (x # xs) ! ?l ^ (n # ns) ! ?l" unfolding prod.lessThan_Suc_shift by auto
    also have "... = x ^ n *
      (\<Prod>i<(?l - 1). xs ! i ^ ns ! i) * (x # xs) ! ?l ^ (n # ns) ! ?l" by auto
    also have "... = x ^ n *
      (\<Prod>i<(?l - 1). xs ! i ^ ns ! i) *
      (x # xs) ! (Suc (?l - 1)) ^ (n # ns) ! (Suc (?l - 1))" unfolding 0 by auto
    also have "... = x ^ n *
      ((\<Prod>i<(?l - 1). xs ! i ^ ns ! i) *
      (x # xs) ! (Suc (?l - 1)) ^ (n # ns) ! (Suc (?l - 1)))"
      by (simp add: algebra_simps)
    also have "... = x ^ n * (\<Prod>i<(Suc (?l - 1)). xs ! i ^ ns ! i)"
      unfolding prod.atMost_Suc[symmetric] by auto
    also have "... = x ^ n * (\<Prod>i<?l. xs ! i ^ ns ! i)" unfolding 0 by auto
    finally show ?thesis .
  qed
  thus ?thesis unfolding mpow_def by auto
qed

lemma mpow'_equiv: "mpow' = mpow" proof -
  have "mpow' (xs :: ('a::comm_semiring_1 list)) ns = mpow xs ns" for xs ns
    by (induction xs ns rule: mpow'.induct; auto)
  thus ?thesis by auto
qed

lemma multinomial'_dvd: "mfact ks dvd fact (sum_list ks)"
proof (induction ks)
  case Nil
  show ?case by auto
next
  case (Cons k ks)
  hence "mfact ks dvd fact (sum_list ks)" .
  hence "fact k * mfact ks dvd (fact k :: nat) * fact (sum_list ks)" by auto
  also have "... dvd fact (k + sum_list ks)" by (rule Binomial.fact_fact_dvd_fact)
  finally have "fact k * mfact ks dvd fact (k + sum_list ks)" .
  thus ?case by auto
qed

lemma mchoose_dvd: "sum_list ks \<le> n \<Longrightarrow>
  mfact ks * fact (n - sum_list ks) dvd fact n"
  using multinomial'_dvd[of "(n - sum_list ks) # ks"] by auto

lemma mchoose_le:
  "sum_list ks \<le> n \<Longrightarrow> mfact ks * fact (n - sum_list ks) \<le> fact n"
using mchoose_dvd by (simp add: dvd_imp_le)

text \<open>The multinomial coefficient.\<close>
definition multinomial' :: "nat list \<Rightarrow> nat" where
  "multinomial' ks = fact (sum_list ks) div mfact ks"

lemma multinomial'_Nil[simp]: "multinomial' [] = 1"
  unfolding multinomial'_def by auto

lemma multinomial'_Cons[simp]: "multinomial' (k # ks) =
  ((k + sum_list ks) choose k) * multinomial' ks"
  unfolding multinomial'_def
  using Rings.algebraic_semidom_class.div_mult_div_if_dvd[
    of "mfact ks" "fact (sum_list ks)"
    "fact k * fact (k + sum_list ks - k)" "fact (k + sum_list ks)",
    OF multinomial'_dvd Binomial.choose_dvd[OF Nat.le_add1]
  ]
  by (simp add: algebra_simps binomial_fact')

definition multinomial :: "nat \<Rightarrow> nat list \<Rightarrow> nat" (infixl "mchoose" 65) where
  "n mchoose ks = multinomial' ((n - sum_list ks) # ks)"

lemma sum_exists:
  fixes n :: nat
  assumes 0: "inj f"
  shows "(\<Sum>s | \<exists>m\<le>n. s = f m. v s) = (\<Sum>m\<le>n. v (f m))"
proof (induction n)
  case 0
  thus ?case by auto
next
  case (Suc n)
  have "(\<Sum>s | \<exists>m\<le>Suc n. s = f m. v s) =
    (\<Sum>s | (\<exists>m\<le>n. s = f m) \<or> s = f (Suc n). v s)" by (metis le_Suc_eq)
  also have "... = sum v ({s. (\<exists>m\<le>n. s = f m)} \<union> {f (Suc n)})"
    by (simp add: Collect_disj_eq)
  also have "... = sum v {s. (\<exists>m\<le>n. s = f m)} + sum v {f (Suc n)}"
  proof (rule sum.union_disjoint)
    show "finite {s. \<exists>m\<le>n. s = f m}" by auto
    show "finite {f (Suc n)}" by auto
    show "{s. \<exists>m\<le>n. s = f m} \<inter> {f (Suc n)} = {}" using 0 injD by fastforce
  qed
  also have "... = (\<Sum>s | \<exists>m\<le>n. s = f m. v s) + v (f (Suc n))" by auto
  also have "... = (\<Sum>m\<le>n. v (f m)) + v (f (Suc n))" unfolding Suc by blast
  also have "... = (\<Sum>m\<le>(Suc n). v (f m))" by auto
  finally show ?case by auto
qed

text \<open>
  The proof is by induction on \<open>xs\<close>, and using the standard
  binomial theorem (@{thm Binomial.binomial_ring})
  See the Wikipedia article
  (@{url "https://en.wikipedia.org/wiki/Multinomial_theorem"}) for reference.\<close>
theorem multinomial_ring:
  fixes xs :: "'a::comm_semiring_1 list"
  shows "(sum_list xs)^n = (\<Sum>ks | length ks = length xs \<and> sum_list ks = n.
    of_nat (multinomial' ks) * mpow xs ks)"
    (is "_ = (\<Sum>ks\<in>?indices xs n. ?v xs ks)")
proof (induction xs arbitrary: n)
  case Nil
  show ?case proof (cases n)
    case 0
    hence "?indices [] n = {[]}" by auto
    thus ?thesis using 0 by auto
  next
    case (Suc n')
    hence 1: "?indices [] n = {}" by auto
    thus ?thesis unfolding 1 using Suc by auto
  qed
next
  case (Cons x xs')
  have 2: "?indices (x # xs') n = \<Union> {s. \<exists>m\<le>n. s = (#) (n - m) ` ?indices xs' m}"
    (is "_ = \<Union> ?S" is "_ = \<Union> {s. ?P s}")
  proof
    have "length ks = Suc (length xs') \<and> sum_list ks = n \<Longrightarrow>
      \<exists>s. (\<exists>m\<le>n. s = (#) (n - m) ` ?indices xs' m) \<and> ks \<in> s" for ks proof -
      assume 3: "length ks = Suc (length xs') \<and> sum_list ks = n"
      have "\<exists>m\<le>n. ks \<in> (#) (n - m) ` ?indices xs' m" proof (cases ks)
        case Nil
        thus ?thesis using 3 by auto
      next
        case (Cons k ks')
        let ?m = "n - k"
        have "ks \<in> (#) (n - ?m) ` ?indices xs' ?m" using 3 Cons by auto
        moreover have "?m \<le> n" by auto
        ultimately show ?thesis by blast
      qed
      thus "\<exists>s. (\<exists>m\<le>n. s = (#) (n - m) ` ?indices xs' m) \<and> ks \<in> s" by blast
    qed
    thus "?indices (x # xs') n \<subseteq> \<Union> ?S" by auto
    show "\<Union> ?S \<subseteq> ?indices (x # xs') n" by auto
  qed
  have 4: "disjoint ?S" proof
    fix s t
    assume "s \<in> ?S"
    hence "?P s" by blast
    from this obtain m where
      m_bound: "m \<le> n" and
      s_def: "s = (#) (n - m) ` ?indices xs' m"
      by blast
    assume "t \<in> ?S"
    hence "?P t" by blast
    from this obtain l where
      l_bound: "l \<le> n" and
      t_def: "t = (#) (n - l) ` ?indices xs' l"
      by blast
    have 5: "ks \<in> s \<Longrightarrow> ks \<in> t \<Longrightarrow> s = t" for ks proof -
      assume "ks \<in> s"
      from this obtain ks'1 where ks_def_1: "ks = (n - m) # ks'1" and
        "ks'1 \<in> ?indices xs' m" unfolding s_def by blast
      assume "ks \<in> t"
      from this obtain ks'2 where ks_def_2: "ks = (n - l) # ks'2" and
        "ks'2 \<in> ?indices xs' l" unfolding t_def by blast
      from m_bound l_bound ks_def_1 ks_def_2 have "m = l" by auto
      thus ?thesis unfolding s_def t_def by auto
    qed
    assume "s \<noteq> t"
    thus "disjnt s t" unfolding disjnt_iff using 5 by blast
  qed
  have 5: "\<forall>s\<in>?S. finite s" proof
    fix s
    assume "s \<in> ?S"
    hence "?P s" by blast
    from this obtain m where
      s_def: "s = (#) (n - m) ` ?indices xs' m" by blast
    have "?indices xs' m \<subseteq> {ks. set ks \<subseteq> {..m} \<and> length ks = length xs'}"
      using member_le_sum_list by auto
    moreover have "finite {ks. set ks \<subseteq> {..m} \<and> length ks = length xs'}"
      using List.finite_lists_length_eq by auto
    ultimately have "finite (?indices xs' m)"
      using Finite_Set.finite_subset by auto
    thus "finite s" unfolding s_def by auto
  qed
  have "(\<Sum>ks\<in>?indices (x # xs') n. ?v (x # xs') ks) =
    (\<Sum>ks\<in>\<Union> ?S. ?v (x # xs') ks)" unfolding 2 by blast
  also have "... = (\<Sum>s | ?P s. \<Sum>ks\<in>s. ?v (x # xs') ks)"
    using sum.Union_disjoint_sets[of "?S"] 4 5 by auto
  also have "... = (\<Sum>m\<le>n. \<Sum>ks\<in>((#) (n - m) ` ?indices xs' m).
    ?v (x # xs') ks)" (is ?G) proof cases
    assume xs'_def: "xs' = []"
    hence 6: "?indices [] m = (if m = 0 then {[]} else {})" for m by auto
    have "(\<Sum>s | \<exists>m\<le>n. s = (#) (n - m) ` ?indices xs' m.
      \<Sum>ks\<in>s. ?v (x # xs') ks) =
      (\<Sum>s | \<exists>m\<le>n. s = (#) (n - m) ` ?indices [] m. \<Sum>ks\<in>s. ?v [x] ks)"
      using xs'_def by auto
    also have "... =
      (\<Sum>s | s = (#) n ` ?indices [] 0 \<or>
      (\<exists>m\<le>n. m \<noteq> 0 \<and> s = (#) (n - m) ` ?indices [] m). \<Sum>ks\<in>s. ?v [x] ks)"
      by (metis (no_types, lifting) Collect_cong diff_zero le0)
    also have "... =
      (\<Sum>s | s = (#) n ` {[]} \<or>
      (\<exists>m\<le>n. m \<noteq> 0 \<and> s = (#) (n - m) ` {}). \<Sum>ks\<in>s. ?v [x] ks)"
      unfolding 6 by (simp; metis)
    also have "... =
      (\<Sum>s | s = {[n]} \<or> (n \<noteq> 0 \<and> s = {}). \<Sum>ks\<in>s. ?v [x] ks)"
      by (metis (no_types, lifting) dual_order.refl image_empty
      image_insert le_zero_eq)
    also have "... =
      sum (\<lambda> s. \<Sum>ks\<in>s. ?v [x] ks) ({s . s = {[n]}} \<union> {s . n \<noteq> 0 \<and> s = {}})"
      by (rule sum.cong; auto)
    also have "... = ?v [x] [n]" by auto
    finally have 7: "(\<Sum>s | \<exists>m\<le>n. s = (#) (n - m) ` ?indices xs' m.
      \<Sum>ks\<in>s. ?v (x # xs') ks) = ?v [x] [n]" .
    have "(\<Sum>m\<le>n. \<Sum>ks\<in>((#) (n - m) ` ?indices xs' m). ?v (x # xs') ks) =
      (\<Sum>m\<le>n. \<Sum>ks\<in>((#) (n - m) ` ?indices [] m). ?v [x] ks)"
      using xs'_def by auto
    also have "... = (if n = 0
      then (\<Sum>ks\<in>((#) (n - 0) ` ?indices [] 0). ?v [x] ks)
      else (\<Sum>m\<le>Suc (n - 1). \<Sum>ks\<in>((#) (n - m) ` ?indices [] m). ?v [x] ks))"
      by auto
    also have "... = (if n = 0
      then (\<Sum>ks\<in>((#) (n - 0) ` ?indices [] 0). ?v [x] ks)
      else (\<Sum>ks\<in>((#) (n - 0) ` ?indices [] 0). ?v [x] ks) +
      (\<Sum>m\<le>(n - 1). \<Sum>ks\<in>((#) (n - Suc m) ` ?indices [] (Suc m)). ?v [x] ks))"
      unfolding sum.atMost_Suc_shift by auto
    also have "... = (if n = 0
      then (\<Sum>ks\<in>((#) (n - 0) ` {[]}). ?v [x] ks)
      else (\<Sum>ks\<in>((#) (n - 0) ` {[]}). ?v [x] ks) +
      (\<Sum>m\<le>(n - 1). \<Sum>ks\<in>((#) (n - Suc m) ` {}). ?v [x] ks))"
      unfolding 6 by auto
    also have "... = ?v [x] [n]" by auto
    finally have 8: "(\<Sum>m\<le>n. \<Sum>ks\<in>((#) (n - m) ` ?indices xs' m).
      ?v (x # xs') ks) = ?v [x] [n]" .
    show ?G unfolding 7 8 by simp
  next
    assume xs'_non_empty: "xs' \<noteq> []"
    have indices_non_empty: "?indices xs' m \<noteq> {}" for m proof -
      let ?indices_instance = "m # List.replicate (length xs' - 1) 0"
      have "?indices_instance \<in> ?indices xs' m"
        using xs'_non_empty by auto
      thus ?thesis by blast
    qed
    show ?G proof (rule sum_exists)
      show "inj (\<lambda>m. (#) (n - m) ` ?indices xs' m)" proof
        fix m1 m2
        assume 9: "(#) (n - m1) ` ?indices xs' m1 = (#) (n - m2) ` ?indices xs' m2"
        from indices_non_empty obtain indices_instance_1
          where "indices_instance_1 \<in> ?indices xs' m1" by blast
        hence 10: "(n - m1) # indices_instance_1 \<in> (#) (n - m1) ` ?indices xs' m1"
          by blast
        from indices_non_empty obtain indices_instance_2
          where "indices_instance_2 \<in> ?indices xs' m2" by blast
        hence 11: "(n - m2) # indices_instance_2 \<in> (#) (n - m2) ` ?indices xs' m2"
          by blast
        from 9 10 11 show "m1 = m2" by auto
      qed
    qed
  qed
  also have "... = (\<Sum>m\<le>n. \<Sum>ks\<in>?indices xs' m. ?v (x # xs') ((n - m) # ks))"
    by (rule sum.cong; simp add: sum.reindex)
  also have "...
    = (\<Sum>m\<le>n. \<Sum>ks\<in>?indices xs' m. of_nat ((n choose (n - m)) * multinomial' ks) *
    (x ^ (n - m) * mpow xs' ks))" using Cons by auto
  also have "... = (\<Sum>m\<le>n. \<Sum>ks\<in>?indices xs' m.
    (of_nat (n choose (n - m)) * x ^ (n - m)) *
    (of_nat (multinomial' ks) * mpow xs' ks))" by (simp add: algebra_simps)
  also have "... =
    (\<Sum>m\<le>n. of_nat (n choose (n - m)) * x ^ (n - m) *
    (\<Sum>ks\<in>?indices xs' m. of_nat (multinomial' ks) * mpow xs' ks))"
    by (simp add: sum_distrib_left)
  also have "... = (\<Sum>m\<le>n. of_nat (n choose (n - m)) * x ^ (n - m) *
    sum_list xs' ^ m)" using Cons by auto
  also have "... = (\<Sum>m\<le>n. of_nat (n choose m) * sum_list xs' ^ m * x ^ (n - m))"
    apply (rule sum.cong)
    apply simp
    subgoal for m
      apply (simp add: Binomial.binomial_symmetric[of m n] algebra_simps)
      done
    done
  also have "... = (sum_list xs' + x)^n"
    by (rule Binomial.binomial_ring[symmetric])
  also have "... = (sum_list (x # xs'))^n" by (simp add: algebra_simps)
  finally have "(\<Sum>ks\<in>?indices (x # xs') n. ?v (x # xs') ks) =
    (sum_list (x # xs'))^n" .
  thus ?case by auto
qed

text \<open>This version of the multinomial theorem is also useful.\<close>
corollary multinomial_ring_alt:
  fixes xs :: "'a::comm_semiring_1 list"
  shows "(1 + sum_list xs)^n = (\<Sum>ks | length ks = length xs \<and> sum_list ks \<le> n.
    of_nat (n mchoose ks) * mpow xs ks)"
proof -
  have "(1 + sum_list xs)^n = (sum_list (1 # xs))^n" by auto
  also have "... = (\<Sum>ks | length ks = 1 + length xs \<and> sum_list ks = n.
    of_nat (multinomial' ks) * mpow (1 # xs) ks)"
    unfolding multinomial_ring by auto
  also have "... = (\<Sum>ks | length ks = length xs \<and> sum_list ks \<le> n.
    of_nat (n mchoose ks) * mpow xs ks)"
  proof (rule sum.reindex_cong[of tl, symmetric])
    show "inj_on tl {ks. length ks = 1 + length xs \<and> sum_list ks = n}"
      unfolding inj_on_def
      by (smt (verit, del_insts) One_nat_def add.commute add_left_cancel
        list.collapse list.size(3) mem_Collect_eq nat.simps(3) plus_nat.simps(2)
        sum_list.Cons)
    show "{ks. length ks = length xs \<and> sum_list ks \<le> n} =
      tl ` {ks. length ks = 1 + length xs \<and> sum_list ks = n}"
      unfolding image_Collect
      apply (rule Collect_cong)
      subgoal for ks
        apply standard  
        subgoal 
          by (metis One_nat_def add.commute less_eqE list.sel(3) list.size(4) sum_list.Cons)
        subgoal 
          by (metis Suc_eq_plus1 add.commute add_diff_cancel_left' le_add2 length_0_conv length_tl
              list.collapse nat.simps(3) sum_list.Cons)
        done
      done
    fix ks
    assume 0: "ks \<in> {ks. length ks = 1 + length xs \<and> sum_list ks = n}"
    from 0 obtain k ks' where ks_def: "ks = k # ks'"
      by (simp; metis Suc_length_conv)
    hence "n - sum_list ks' = k" using 0 by auto
    thus "of_nat (n mchoose tl ks) * mpow xs (tl ks) =
      of_nat (multinomial' ks) * mpow (1 # xs) ks"
      unfolding ks_def multinomial_def by simp
  qed
  finally show ?thesis .
qed

end