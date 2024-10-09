section \<open>Concrete bounds for Chebyshev's prime counting functions\<close>
theory Chebyshev_Prime_Exhaust
imports
  "HOL-Decision_Procs.Approximation"
  "HOL-Library.Code_Target_Numeral"
  "Prime_Number_Theorem.Prime_Counting_Functions"
begin

text \<open>
  The well-known Prime Number Theorem states that $\psi(x) \sim \theta(x) \sim (x)$, i.e.\ 
  that both $\psi(x)$ and $\vartheta(x)$ are bounded by $(1 \pm \varepsilon) x$
  for sufficiently large $x$ for any $\varepsilon > 0$. However, these are asymptotic bounds
  without giving any concrete information on how $\psi$ and $\vartheta$ behave for small $x$,
  or even how big $x$ must be until these bound shold.

  To complement this, we shall prove some concrete, non-asymptotic bounds. Concretely:

    \<^item> $\psi(x) \geq 0.9x$ if $x\geq 41$

    \<^item> $\theta(x) \geq 0.82x$ if $x\geq 97$

    \<^item> $\theta(x) \leq \psi(x) \leq 1.2x$ if $x\geq 0$

  \noindent Our formalisation loosely follows a blog entry by A.W.\ Walker:
   \<^url>\<open>https://awwalker.com/2017/02/05/notes-on-the-chebyshev-theorem/\<close>
\<close>

subsection \<open>Brute-force checking of bounds for \<open>\<psi>\<close> and \<open>\<theta>\<close>\<close>

subsubsection \<open>Computing powers of a number\<close>

function powers_below_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "powers_below_aux ub n acc = (if acc = 0 \<or> n \<le> 1 \<or> acc > ub then [] else
     acc # powers_below_aux ub n (acc * n))"
  by auto
termination
  by (relation "Wellfounded.measure (\<lambda>(ub, n, acc). 1 + ub - acc)")
     (auto intro!: diff_less_mono2)

lemmas [simp del] = powers_below_aux.simps

lemma set_powers_below_aux:
  assumes "acc > 0" "n > 1"
  shows   "set (powers_below_aux ub n acc) = range (\<lambda>i. acc * n ^ i) \<inter> {..ub}"
  using assms
proof (induction ub n acc rule: powers_below_aux.induct)
  case (1 ub n acc)
  show ?case
  proof (cases "acc > ub")
    case True
    have "range (\<lambda>i. acc * n ^ i) \<inter> {..ub} = {}"
    proof (intro equalityI subsetI)
      fix k assume "k \<in> range (\<lambda>i. acc * n ^ i) \<inter> {..ub}"
      then obtain i where "acc * n ^ i \<le> ub"
        by auto
      also have "ub < acc * n ^ 0"
        using True by simp
      finally have "n ^ i < n ^ 0"
        using \<open>acc > 0\<close> by (subst (asm) mult_less_cancel1) auto
      hence "i < 0"
        by (subst (asm) power_strict_increasing_iff) (use \<open>n > 1\<close> in auto)
      thus "k \<in> {}"
        by simp
    qed auto
    thus ?thesis
      using True by (auto simp: powers_below_aux.simps)
  next
    case False
    have "set (powers_below_aux ub n acc) = insert acc (set (powers_below_aux ub n (acc * n)))"
      using False "1.prems" by (subst powers_below_aux.simps) auto
    also have "set (powers_below_aux ub n (acc * n)) = range (\<lambda>i. acc * n ^ Suc i) \<inter> {..ub}"
      by (subst "1.IH") (use "1.prems" False in \<open>auto simp: mult_ac\<close>)
    also have "insert acc (range (\<lambda>i. acc * n ^ Suc i) \<inter> {..ub}) =
               range (\<lambda>i. acc * n ^ i) \<inter> {..ub}" (is "insert acc ?lhs = ?rhs")
    proof (intro equalityI subsetI)
      fix x assume "x \<in> insert acc ?lhs"
      thus "x \<in> ?rhs" using False
        by (auto intro: rev_image_eqI[of 0] rev_image_eqI[of "Suc i" for i])
    next
      fix x assume "x \<in> ?rhs"
      then obtain i where i: "x = acc * n ^ i" and le: "acc * n ^ i \<le> ub"
        by auto
      show "x \<in> insert acc ?lhs"
      proof (cases "i = 0")
        case False
        hence "x \<in> ?lhs"
          by (intro IntI rev_image_eqI[of "i-1"]) (use i le in auto)
        thus ?thesis
          by blast
      qed (use i le in auto)
    qed
    finally show ?thesis .
  qed
qed

definition powers_below :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "powers_below ub n = powers_below_aux ub n n"

lemma set_powers_below:
  assumes "n > 1"
  shows   "set (powers_below ub n) = (\<lambda>i. n ^ i) ` {1..} \<inter> {..ub}"
proof -
  have "set (powers_below ub n) = range (\<lambda>i. n * n ^ i) \<inter> {..ub}"
    unfolding powers_below_def
    by (rule set_powers_below_aux) (use assms in auto)
  also have "range (\<lambda>i. n * n ^ i) = (\<lambda>i. n ^ i) ` Suc ` UNIV"
    by (simp add: image_image o_def)
  also have "bij_betw Suc UNIV {1..}"
    by (rule bij_betwI[of _ _ _ "\<lambda>i. i - 1"]) auto
  hence "Suc ` UNIV = {1..}"
    by (simp add: bij_betw_def)
  finally show ?thesis .
qed

lemma distinct_powers_below_aux:
  assumes "n > 1" "acc > 0"
  shows   "distinct (powers_below_aux ub n acc)"
  using assms
  by (induction ub n acc rule: powers_below_aux.induct; subst powers_below_aux.simps)
     (auto simp: set_powers_below_aux)

lemma distinct_powers_below: "n > 1 \<Longrightarrow> distinct (powers_below ub n)"
  unfolding powers_below_def by (rule distinct_powers_below_aux) auto

lemma hd_powers_below_aux:
  assumes "acc \<le> ub" "n > 1" "acc > 0"
  shows   "hd (powers_below_aux ub n acc) = acc"
  by (subst powers_below_aux.simps) (use assms in auto)

lemma hd_powers_below:
  assumes "n \<le> ub" "n > 1"
  shows   "hd (powers_below ub n) = n"
  unfolding powers_below_def by (subst hd_powers_below_aux) (use assms in auto)


subsubsection \<open>Computing prime powers\<close>


definition prime_powers_upto :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "prime_powers_upto n =
     sort_key fst (concat (map (\<lambda>p. map (\<lambda>k. (k, p)) (powers_below n p)) (primes_upto n)))"

lemma map_key_sort_key: "map f (sort_key f xs) = sort (map f xs)"
proof -
  have [simp]: "map f (insort_key f x xs) = insort (f x) (map f xs)" for x xs
    by (induction xs) auto
  have [simp]: "map f (foldr (insort_key f) xs acc) =
        foldr insort (map f xs) (map f acc)" for acc
    by (induction xs arbitrary: acc) auto
  show ?thesis
    unfolding sort_key_def by simp
qed

lemma distinct_prime_powers_upto:
  "distinct (map fst (prime_powers_upto n))"
proof -
  have inj: "inj_on (powers_below n) {p. prime p \<and> p \<le> n}"
  proof
    fix p q assume pq: "p \<in> {p. prime p \<and> p \<le> n}" "q \<in> {p. prime p \<and> p \<le> n}"
    assume eq: "powers_below n p = powers_below n q"
    from eq have "hd (powers_below n p) = hd (powers_below n q)"
      by simp
    thus "p = q"
      using pq by (simp add: hd_powers_below prime_gt_Suc_0_nat)
  qed

  have "distinct (concat (map (powers_below n) (primes_upto n)))"
  proof (rule distinct_concat, goal_cases)
    case 1
    thus ?case
      unfolding distinct_map using inj
      by (simp add: set_primes_upto conj_commute)
  next
    case (2 ys)
    thus ?case
      by (auto simp: distinct_powers_below set_primes_upto prime_gt_Suc_0_nat)
  next
    case (3 ys zs)
    thus ?case
      by (auto simp: set_primes_upto set_powers_below prime_gt_Suc_0_nat prime_power_inj'')
  qed
  thus ?thesis
    by (simp add: prime_powers_upto_def map_key_sort_key map_concat o_def)
qed

lemma sorted_prime_powers_upto:
  "sorted (map fst (prime_powers_upto n))"
  by (simp add: prime_powers_upto_def)

lemma set_prime_powers_upto:
  "set (prime_powers_upto n) = {(q, aprimedivisor q) |q. primepow q \<and> q \<le> n}"
proof -
  have "set (prime_powers_upto n) = 
         (\<Union>p\<in>{p. p \<le> n \<and> prime p}. (\<lambda>x. (x, p)) ` ((\<lambda>i. p ^ i) ` {1..} \<inter> {..n}))"
    by (simp add: prime_powers_upto_def set_primes_upto set_powers_below prime_gt_Suc_0_nat)
  also have "\<dots> = {(q, aprimedivisor q) |q. primepow q \<and> q \<le> n}"
    (is "?lhs = ?rhs")
  proof (intro equalityI subsetI)
    fix qp assume qp: "qp \<in> ?lhs"
    then obtain q p where [simp]: "qp = (q, p)"
      by (cases qp)
    from qp obtain i where i: "prime p" "p \<le> n" "p ^ i \<le> n" "q = p ^ i" "i \<ge> 1"
      by auto
    show "qp \<in> ?rhs"
      using i by (auto simp: aprimedivisor_prime_power)
  next
    fix qp assume qp: "qp \<in> ?rhs"
    then obtain q p where [simp]: "qp = (q, p)"
      by (cases qp)
    from qp have "primepow q"
      by auto
    then obtain p' i where i: "prime p'" "q = p' ^ i" "i > 0"
      by (auto simp: primepow_def)
    have [simp]: "p' = p"
      using qp i by (auto simp: aprimedivisor_prime_power)
    have "p ^ 1 \<le> p ^ i"
      by (rule power_increasing) (use i prime_gt_0_nat[of p] in auto)
    also have "\<dots> \<le> n"
      using i qp by simp
    finally have "p \<le> n"
      by simp
    with i qp show "qp \<in> ?lhs"
      by auto
  qed
  finally show ?thesis .
qed


subsubsection \<open>A generic checking function\<close>

locale chebyshev_check =
  fixes f :: "nat \<Rightarrow> real"
    and F :: "nat \<Rightarrow> 'a \<Rightarrow> float"
    and A :: "nat set"
    and plus :: "nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float"
    and rel :: "real \<Rightarrow> real \<Rightarrow> bool"
    and P :: "nat \<Rightarrow> real \<Rightarrow> bool"
    and num :: "'a \<Rightarrow> nat"
  assumes plus: "\<And>prec. rel X x \<Longrightarrow> rel Y y \<Longrightarrow> rel (plus prec X Y) (x + y)"
  assumes P_rel: "\<And>x y k. P k x \<Longrightarrow> rel x y \<Longrightarrow> P k y"
  assumes rel_0: "rel 0 0"
  assumes A: "0 \<notin> A"
begin

definition S where "S n = (\<Sum>k\<in>A\<inter>{..n}. f k)"
definition S' where "S' n = (\<Sum>k\<in>A\<inter>{..<n}. f k)"

context
  fixes prec :: nat
begin

function check_aux :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> bool" where
  "check_aux ps lb ub acc n = (if n > ub then True else
     (let (acc', ps') =
        (if ps \<noteq> [] \<and> num (hd ps) = n then
           (plus prec acc (F prec (hd ps)), tl ps)
         else (acc, ps))
      in (n < lb \<or> P n (real_of_float acc')) \<and> check_aux ps' lb ub acc' (n+1)))"
  by auto
termination
  by (relation "Wellfounded.measure (\<lambda>(_, _, ub, _, n). Suc ub - n)")
     (auto split: if_splits)

definition check :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "check xs lb ub =
     check_aux xs lb ub 0 (if xs = [] then lb else min lb (num (hd xs)))"

lemmas [simp del] = check_aux.simps

lemma check_aux_correct:
  assumes "sorted (map num ps)" "distinct (map num ps)"
  assumes "\<And>p. p \<le> ub \<Longrightarrow> p \<in> num ` set ps \<longleftrightarrow> p \<in> A \<and> p \<ge> n"
  assumes "\<And>x. x \<in> set ps \<Longrightarrow> rel (real_of_float (F prec x)) (f (num x))"
  assumes "rel (real_of_float acc) (S' n)"
  assumes "check_aux ps lb ub acc n"
  assumes "k \<in> {max lb n..ub}"
  shows   "P k (S k)"
  using assms
proof (induction ps lb ub acc n rule: check_aux.induct)
  case (1 ps lb ub acc n)
  hence "n \<le> ub"
    by auto
  define ps' where "ps' = (if ps = [] \<or> num (hd ps) \<noteq> n then ps else tl ps)"
  define acc' where "acc' = (if ps = [] \<or> num (hd ps) \<noteq> n then acc else plus prec acc (F prec (hd ps)))"

  have acc': "rel (real_of_float acc') (S n)"
  proof (cases "n \<in> A")
    case False
    hence "acc' = acc" using "1.prems"(3)[of n] \<open>n \<le> ub\<close>
      by (cases ps) (auto simp: acc'_def)
    hence "rel (real_of_float acc') (S' n)"
      using "1.prems"(5) by simp
    also from False have "A \<inter> {..<n} = A \<inter> {..n}"
      using nless_le by blast
    hence "S' n = S n"
      by (simp add: S_def S'_def)
    finally show ?thesis .
  next
    case True
    hence "n \<in> num ` set ps" "n > 0"
      using "1.prems"(3)[of n] \<open>n \<le> ub\<close> A by (auto intro: Nat.gr0I)
    have *: "num p \<ge> n" if "p \<in> set ps" for p
      using "1.prems"(3)[of "num p"] that \<open>n \<le> ub\<close>
      by (cases "num p \<le> ub") auto
    from \<open>n \<in> num ` set ps\<close> obtain x
      where ps_eq: "ps = x # ps'" "num x = n"
      using \<open>sorted (map num ps)\<close> \<open>distinct (map num ps)\<close> *
      by (cases ps) (fastforce simp: ps'_def)+
    have "acc' = plus prec acc (F prec x)"
      using ps_eq by (auto simp: acc'_def)
    also have "rel (real_of_float \<dots>) (S' n + f (num x))"
      by (intro plus "1.prems" \<open>n > 0\<close>) (auto simp: ps_eq)
    also have "\<dots> = sum f (insert n (A \<inter> {..<n}))"
      unfolding S'_def by (subst sum.insert) (auto simp: ps_eq)
    also have "insert n (A \<inter> {..<n}) = A \<inter> {..n}"
      using True by auto
    also have "sum f \<dots> = S n"
      by (simp add: S_def)
    finally show ?thesis .
  qed

  show ?case
  proof (cases "n = k")
    case True
    have "P k (real_of_float acc')"
      using "1.prems"(6,7)
      by (subst (asm) check_aux.simps) (use True in \<open>auto simp: acc'_def\<close>)
    moreover have "rel (real_of_float acc') (S n)"
      by fact
    ultimately show ?thesis
      using True P_rel by simp
  next
    case False
    show ?thesis
    proof (rule "1.IH"[of "(acc', ps')", OF _ _ refl])
      show "sorted (map num ps')"
        using \<open>sorted (map num ps)\<close>
        by (auto simp: ps'_def sorted_tl map_tl)
      show "distinct (map num ps')"
        using \<open>distinct (map num ps)\<close>
        by (auto simp: ps'_def distinct_tl map_tl)
      show "(p \<in> num ` set ps') = (p \<in> A \<and> n + 1 \<le> p)" if p: "p \<le> ub" for p
      proof (cases "n \<in> A")
        case False
        hence "n \<notin> num ` set ps"
          using "1.prems"(3)[of n] \<open>n \<le> ub\<close> by auto
        hence [simp]: "ps' = ps"
          by (auto simp: ps'_def)
        show ?thesis using "1.prems"(3)[of p] p False
          by (cases "n = p") auto
      next
        case True
        hence "n \<in> num ` set ps"
          using "1.prems"(3)[of n] \<open>n \<le> ub\<close> by auto
        have *: "num p \<ge> n" if "p \<in> set ps" for p
          using "1.prems"(3)[of "num p"] that \<open>n \<le> ub\<close>
          by (cases "num p \<le> ub") auto
        from \<open>n \<in> num ` set ps\<close> obtain x
          where ps_eq: "ps = x # ps'" "num x = n"
          using \<open>sorted (map num ps)\<close> \<open>distinct (map num ps)\<close> *
          by (cases ps) (fastforce simp: ps'_def)+
        show ?thesis
          by (cases "p = n")
             (use "1.prems"(3)[of p] p \<open>distinct (map num ps)\<close> in \<open>auto simp: ps_eq\<close>)
      qed
    next
      have "rel (real_of_float acc') (S n)"
        by fact
      also have "S n = S' (n + 1)"
        unfolding S_def S'_def by (simp add: lessThan_Suc_atMost)
      finally show "rel (real_of_float acc') (S' (n + 1))" .
    next
      show "check_aux ps' lb ub acc' (n + 1)"
        using "1.prems"(6,7)
        by (subst (asm) check_aux.simps) (auto simp: acc'_def ps'_def)
    next
      show "k \<in> {max lb (n+1)..ub}"
        using "1.prems" False by auto
    next
      show "rel (real_of_float (F prec x)) (f (num x))"
        if "x \<in> set ps'" for x
        using "1.prems"(4)[of x] that
        by (cases ps) (auto simp: ps'_def split: if_splits)
    qed (use \<open>n \<le> ub\<close> in \<open>auto simp: acc'_def ps'_def\<close>)
  qed
qed

lemma check_correct:
  assumes "sorted (map num ps)" "distinct (map num ps)"
  assumes "\<And>p. p \<le> ub \<Longrightarrow> p \<in> num ` set ps \<longleftrightarrow> p \<in> A"
  assumes "\<And>x. x \<in> set ps \<Longrightarrow> rel (real_of_float (F prec x)) (f (num x))"
  assumes "check ps lb ub"
  assumes "k \<in> {lb..ub}"
  shows   "P k (S k)"
proof (rule check_aux_correct)
  define n where "n = (if ps = [] then lb else min lb (num (hd ps)))"
  have "n \<le> ub"
    using assms by (auto simp: n_def)
  show "sorted (map num ps)" "distinct (map num ps)"
    by fact+
  show "check_aux ps lb ub 0 n"
    using assms unfolding check_def n_def by simp
  show "k \<in> {max lb n..ub}"
    using assms by (auto simp: n_def)
  show "p \<in> num ` set ps \<longleftrightarrow> p \<in> A \<and> n \<le> p" if "p \<le> ub" for p
    using assms(3)[of p] that \<open>sorted (map num ps)\<close>
    by (cases ps) (auto simp: n_def)

  have "A \<inter> {..<n} = {}"
  proof (intro equalityI subsetI)
    fix p assume p: "p \<in> A \<inter> {..<n}"
    hence "p \<in> num ` set ps"
      using assms(3)[of p] \<open>n \<le> ub\<close> by auto
    hence False
      using p \<open>sorted (map num ps)\<close> by (cases ps) (auto simp: n_def)
    thus "p \<in> {}" ..
  qed auto
  thus "rel (real_of_float 0) (S' n)"
    by (simp add: S'_def rel_0)
qed (use assms in auto)

end

end


subsubsection \<open>The \<open>\<theta>\<close> function\<close>

context
begin

interpretation primes_theta: chebyshev_check
  "\<lambda>n. ln (real n)"
  "\<lambda>prec n. the (lb_ln prec (Float (int n) 0))"
  "{p. prime p}"
  "float_plus_down"
  "(\<le>)"
  "\<lambda>k x. x \<ge> c * (real k + 1)"
  "\<lambda>n. n"
  for c :: real
proof
  show "real_of_float (float_plus_down prec X Y) \<le> x + y"
    if "real_of_float X \<le> x" "real_of_float Y \<le> y"
    for x y :: real and X Y :: float and prec :: nat
    using that by (simp add: float_plus_down_le)
qed auto


definition check_theta_lower_aux
  where "check_theta_lower_aux = primes_theta.check_aux"

definition check_theta_lower where
  "check_theta_lower c prec lb ub =
     primes_theta.check c prec (primes_upto ub) lb ub"

lemma check_theta_lower_aux_code [code]:
  "check_theta_lower_aux c prec ps lb ub acc n =
     (if ub < n then True else let (acc', ps') =
            if ps \<noteq> [] \<and> hd ps = n
            then (float_plus_down prec acc (the (lb_ln prec (Float (int (hd ps)) 0))), tl ps)
            else (acc, ps)
      in (n < lb \<or> c * (real n + 1) \<le> real_of_float acc') \<and>
         check_theta_lower_aux c prec ps' lb
          ub acc' (n + 1))"
  unfolding check_theta_lower_aux_def
  by (rule primes_theta.check_aux.simps)

lemma check_theta_lower_code [code]:
  "check_theta_lower c prec lb ub = (let ps = primes_upto ub in
     check_theta_lower_aux c prec ps lb ub 0
       (if ps = [] then lb else min lb (hd ps)))"
  unfolding check_theta_lower_def primes_theta.check_def check_theta_lower_aux_def
  by (simp add: Let_def)

lemma check_theta_lower_correct:
  assumes "check_theta_lower c prec lb ub"
  shows   "\<forall>x\<in>{real lb..real ub}. primes_theta x \<ge> c * x"
proof
  fix x assume x: "x \<in> {real lb..real ub}"
  define k where "k = nat \<lfloor>x\<rfloor>"
  show "c * x \<le> primes_theta x"
  proof (cases "c \<ge> 0")
    case False
    hence "c * x \<le> 0"
      using x by (auto intro: mult_nonpos_nonneg)
    also have "0 \<le> primes_theta x"
      by (rule \<theta>_nonneg)
    finally show ?thesis .
  next
    case True
    hence "c * x \<le> c * (real k + 1)"
      using x by (intro mult_left_mono) (auto simp: k_def)
    also have "c * (real k + 1) \<le> primes_theta.S k"
    proof (rule primes_theta.check_correct)
      show "sorted (map (\<lambda>n. n) (primes_upto ub))"
           "distinct (map (\<lambda>n. n) (primes_upto ub))"
        by (simp_all add: sorted_primes_upto distinct_primes_upto)
      show "k \<in> {lb..ub}"
        using x by (auto simp: k_def le_nat_iff le_floor_iff nat_le_iff floor_le_iff)
      show "primes_theta.check c prec (primes_upto ub) lb ub"
        using assms by (simp add: check_theta_lower_def)
    next
      fix p assume "p \<le> ub"
      thus "p \<in> (\<lambda>n. n) ` set (primes_upto ub) \<longleftrightarrow> p \<in> {p. prime p}"
        by (auto simp: set_primes_upto)
    next
      fix n
      assume n: "n \<in> set (primes_upto ub)"
      hence "n > 0"
        by (auto simp: set_primes_upto prime_gt_0_nat)
      define x where "x = the (lb_ln prec (Float (int n) 0))"
      have "lb_ln prec (Float (int n) 0) \<noteq> None"
        using \<open>n > 0\<close> by (subst lb_ln.simps) auto
      hence "lb_ln prec (Float (int n) 0) = Some x"
        by (cases "lb_ln prec (Float (int n) 0)") (auto simp: x_def)
      from lb_lnD[OF this] show "real_of_float x \<le> ln (real n)"
        by simp
    qed
    also have "primes_theta.S k = primes_theta k"
      unfolding primes_theta.S_def primes_theta_def prime_sum_upto_def
      by (intro sum.cong) auto
    also have "primes_theta k = primes_theta x"
      unfolding k_def by simp
    finally show "c * x \<le> primes_theta x" .
  qed
qed

end




context
begin

interpretation primes_theta: chebyshev_check
  "\<lambda>n. ln (real n)"
  "\<lambda>prec n. the (ub_ln prec (Float (int n) 0))"
  "{p. prime p}"
  "float_plus_up"
  "(\<ge>)"
  "\<lambda>k x. x \<le> c * real k"
  "\<lambda>n. n"
  for c :: real
proof
  show "real_of_float (float_plus_up prec X Y) \<ge> x + y"
    if "real_of_float X \<ge> x" "real_of_float Y \<ge> y"
    for x y :: real and X Y :: float and prec :: nat
    using that by (simp add: float_plus_up_le)
qed auto


definition check_theta_upper_aux
  where "check_theta_upper_aux = primes_theta.check_aux"

definition check_theta_upper where
  "check_theta_upper c prec lb ub =
     primes_theta.check c prec (primes_upto ub) lb ub"

lemma check_theta_upper_aux_code [code]:
  "check_theta_upper_aux c prec ps lb ub acc n =
     (if ub < n then True else let (acc', ps') =
            if ps \<noteq> [] \<and> hd ps = n
            then (float_plus_up prec acc (the (ub_ln prec (Float (int (hd ps)) 0))), tl ps)
            else (acc, ps)
      in (n < lb \<or> c * real n \<ge> real_of_float acc') \<and>
         check_theta_upper_aux c prec ps' lb
          ub acc' (n + 1))"
  unfolding check_theta_upper_aux_def
  by (rule primes_theta.check_aux.simps)

lemma check_theta_upper_code [code]:
  "check_theta_upper c prec lb ub = (let ps = primes_upto ub in
     check_theta_upper_aux c prec ps lb ub 0
       (if ps = [] then lb else min lb (hd ps)))"
  unfolding check_theta_upper_def primes_theta.check_def check_theta_upper_aux_def
  by (simp add: Let_def)

lemma check_theta_upper_correct:
  assumes "check_theta_upper c prec lb ub" "c \<ge> 0"
  shows   "\<forall>x\<in>{real lb..real ub}. primes_theta x \<le> c * x"
proof
  fix x assume x: "x \<in> {real lb..real ub}"
  define k where "k = nat \<lfloor>x\<rfloor>"
  have "primes_theta.S k \<le> c * real k"
  proof (rule primes_theta.check_correct)
    show "sorted (map (\<lambda>n. n) (primes_upto ub))"
         "distinct (map (\<lambda>n. n) (primes_upto ub))"
      by (simp_all add: sorted_primes_upto distinct_primes_upto)
    show "k \<in> {lb..ub}"
      using x by (auto simp: k_def le_nat_iff le_floor_iff nat_le_iff floor_le_iff)
    show "primes_theta.check c prec (primes_upto ub) lb ub"
      using assms by (simp add: check_theta_upper_def)
  next
    fix p assume "p \<le> ub"
    thus "p \<in> (\<lambda>n. n) ` set (primes_upto ub) \<longleftrightarrow> p \<in> {p. prime p}"
      by (auto simp: set_primes_upto)
  next
    fix n
    assume n: "n \<in> set (primes_upto ub)"
    hence "n > 0"
      by (auto simp: set_primes_upto prime_gt_0_nat)
    define x where "x = the (ub_ln prec (Float (int n) 0))"
    have "ub_ln prec (Float (int n) 0) \<noteq> None"
      using \<open>n > 0\<close> by (subst ub_ln.simps) auto
    hence "ub_ln prec (Float (int n) 0) = Some x"
      by (cases "ub_ln prec (Float (int n) 0)") (auto simp: x_def)
    from ub_lnD[OF this] show "real_of_float x \<ge> ln (real n)"
      by simp
  qed
  also have "primes_theta.S k = primes_theta k"
    unfolding primes_theta.S_def primes_theta_def prime_sum_upto_def
    by (intro sum.cong) auto
  also have "primes_theta k = primes_theta x"
    unfolding k_def by simp
  also have "c * real k \<le> c * x"
    using \<open>c \<ge> 0\<close> x by (intro mult_left_mono) (auto simp: k_def)
  finally show "primes_theta x \<le> c * x" .
qed

end


subsubsection \<open>The \<open>\<psi>\<close> function\<close>

context
begin

interpretation primes_psi: chebyshev_check
  "\<lambda>n. ln (real (aprimedivisor n))"
  "\<lambda>prec x. the (lb_ln prec (Float (int (snd x)) 0))"
  "{p. primepow p}"
  "float_plus_down"
  "(\<le>)"
  "\<lambda>k x. x \<ge> c * (real k + 1)"
  "fst"
  for c :: real
proof
  show "real_of_float (float_plus_down prec X Y) \<le> x + y"
    if "real_of_float X \<le> x" "real_of_float Y \<le> y"
    for x y :: real and X Y :: float and prec :: nat
    using that by (simp add: float_plus_down_le)
qed auto


definition check_psi_lower_aux
  where "check_psi_lower_aux = primes_psi.check_aux"

definition check_psi_lower where
  "check_psi_lower c prec lb ub =
     primes_psi.check c prec (prime_powers_upto ub) lb ub"

lemma check_psi_lower_aux_code [code]:
  "check_psi_lower_aux c prec ps lb ub acc n =
     (if ub < n then True else let (acc', ps') =
            if ps \<noteq> [] \<and> fst (hd ps) = n
            then (float_plus_down prec acc (the (lb_ln prec (Float (int (snd (hd ps))) 0))), tl ps)
            else (acc, ps)
      in (n < lb \<or> c * (real n + 1) \<le> real_of_float acc') \<and>
         check_psi_lower_aux c prec ps' lb
          ub acc' (n + 1))"
  unfolding check_psi_lower_aux_def
  by (rule primes_psi.check_aux.simps)

lemma check_psi_lower_code [code]:
  "check_psi_lower c prec lb ub = (let ps = prime_powers_upto ub in
     check_psi_lower_aux c prec ps lb ub 0
       (if ps = [] then lb else min lb (fst (hd ps))))"
  unfolding check_psi_lower_def primes_psi.check_def check_psi_lower_aux_def
  by (simp add: Let_def)

lemma check_psi_lower_correct:
  assumes "check_psi_lower c prec lb ub"
  shows   "\<forall>x\<in>{real lb..real ub}. primes_psi x \<ge> c * x"
proof
  fix x assume x: "x \<in> {real lb..real ub}"
  define k where "k = nat \<lfloor>x\<rfloor>"
  show "c * x \<le> primes_psi x"
  proof (cases "c \<ge> 0")
    case False
    hence "c * x \<le> 0"
      using x by (auto intro: mult_nonpos_nonneg)
    also have "0 \<le> primes_psi x"
      by (rule \<psi>_nonneg)
    finally show ?thesis .
  next
    case True
    hence "c * x \<le> c * (real k + 1)"
      using x by (intro mult_left_mono) (auto simp: k_def)
    also have "c * (real k + 1) \<le> primes_psi.S k"
    proof (rule primes_psi.check_correct)
      show "sorted (map fst (prime_powers_upto ub))"
           "distinct (map fst (prime_powers_upto ub))"
        by (simp_all add: sorted_prime_powers_upto distinct_prime_powers_upto)
      show "k \<in> {lb..ub}"
        using x by (auto simp: k_def le_nat_iff le_floor_iff nat_le_iff floor_le_iff)
      show "primes_psi.check c prec (prime_powers_upto ub) lb ub"
        using assms by (simp add: check_psi_lower_def)
    next
      fix p assume "p \<le> ub"
      thus "p \<in> fst ` set (prime_powers_upto ub) \<longleftrightarrow> p \<in> {p. primepow p}"
        by (force simp: set_prime_powers_upto)
    next
      fix y
      assume y: "y \<in> set (prime_powers_upto ub)"
      hence "snd y > 0"
        by (auto simp: set_prime_powers_upto intro!: aprimedivisor_pos_nat primepow_gt_Suc_0)
      define x where "x = the (lb_ln prec (Float (int (snd y)) 0))"
      have "lb_ln prec (Float (int (snd y)) 0) \<noteq> None"
        using \<open>snd y > 0\<close> by (subst lb_ln.simps) auto
      hence "lb_ln prec (Float (int (snd y)) 0) = Some x"
        by (cases "lb_ln prec (Float (int (snd y)) 0)") (auto simp: x_def)
      from lb_lnD[OF this] show "real_of_float x \<le> ln (real (aprimedivisor (fst y)))"
        using y by (auto simp: set_prime_powers_upto)
    qed
    also have "primes_psi.S k = primes_psi k"
      unfolding primes_psi.S_def primes_psi_def sum_upto_def
      by (intro sum.mono_neutral_cong_left) (auto simp: primepow_gt_0_nat mangoldt_def)
    also have "primes_psi k = primes_psi x"
      unfolding k_def by simp
    finally show "c * x \<le> primes_psi x" .
  qed
qed

end


context
begin

interpretation primes_psi: chebyshev_check
  "\<lambda>n. ln (real (aprimedivisor n))"
  "\<lambda>prec x. the (ub_ln prec (Float (int (snd x)) 0))"
  "{p. primepow p}"
  "float_plus_up"
  "(\<ge>)"
  "\<lambda>k x. x \<le> c * real k"
  "fst"
  for c :: real
proof
  show "real_of_float (float_plus_up prec X Y) \<ge> x + y"
    if "real_of_float X \<ge> x" "real_of_float Y \<ge> y"
    for x y :: real and X Y :: float and prec :: nat
    using that by (simp add: float_plus_up_le)
qed auto


definition check_psi_upper_aux
  where "check_psi_upper_aux = primes_psi.check_aux"

definition check_psi_upper where
  "check_psi_upper c prec lb ub =
     primes_psi.check c prec (prime_powers_upto ub) lb ub"

lemma check_psi_upper_aux_code [code]:
  "check_psi_upper_aux c prec ps lb ub acc n =
     (if ub < n then True else let (acc', ps') =
            if ps \<noteq> [] \<and> fst (hd ps) = n
            then (float_plus_up prec acc (the (ub_ln prec (Float (int (snd (hd ps))) 0))), tl ps)
            else (acc, ps)
      in (n < lb \<or> c * real n \<ge> real_of_float acc') \<and>
         check_psi_upper_aux c prec ps' lb
          ub acc' (n + 1))"
  unfolding check_psi_upper_aux_def
  by (rule primes_psi.check_aux.simps)

lemma check_psi_upper_code [code]:
  "check_psi_upper c prec lb ub = (let ps = prime_powers_upto ub in
     check_psi_upper_aux c prec ps lb ub 0
       (if ps = [] then lb else min lb (fst (hd ps))))"
  unfolding check_psi_upper_def primes_psi.check_def check_psi_upper_aux_def
  by (simp add: Let_def)

lemma check_psi_upper_correct:
  assumes "check_psi_upper c prec lb ub" "c \<ge> 0"
  shows   "\<forall>x\<in>{real lb..real ub}. primes_psi x \<le> c * x"
proof
  fix x assume x: "x \<in> {real lb..real ub}"
  define k where "k = nat \<lfloor>x\<rfloor>"
  have "primes_psi.S k \<le> c * real k"
  proof (rule primes_psi.check_correct)
    show "sorted (map fst (prime_powers_upto ub))"
         "distinct (map fst (prime_powers_upto ub))"
      by (simp_all add: sorted_prime_powers_upto distinct_prime_powers_upto)
    show "k \<in> {lb..ub}"
      using x by (auto simp: k_def le_nat_iff le_floor_iff nat_le_iff floor_le_iff)
    show "primes_psi.check c prec (prime_powers_upto ub) lb ub"
      using assms by (simp add: check_psi_upper_def)
  next
    fix p assume "p \<le> ub"
    thus "p \<in> fst ` set (prime_powers_upto ub) \<longleftrightarrow> p \<in> {p. primepow p}"
      by (force simp: set_prime_powers_upto)
  next
    fix y
    assume y: "y \<in> set (prime_powers_upto ub)"
    hence "snd y > 0"
      by (auto simp: set_prime_powers_upto intro!: aprimedivisor_pos_nat primepow_gt_Suc_0)
    define x where "x = the (ub_ln prec (Float (int (snd y)) 0))"
    have "ub_ln prec (Float (int (snd y)) 0) \<noteq> None"
      using \<open>snd y > 0\<close> by (subst ub_ln.simps) auto
    hence "ub_ln prec (Float (int (snd y)) 0) = Some x"
      by (cases "ub_ln prec (Float (int (snd y)) 0)") (auto simp: x_def)
    from ub_lnD[OF this] show "real_of_float x \<ge> ln (real (aprimedivisor (fst y)))"
      using y by (auto simp: set_prime_powers_upto)
  qed
  also have "primes_psi.S k = primes_psi k"
    unfolding primes_psi.S_def primes_psi_def sum_upto_def
    by (intro sum.mono_neutral_cong_left) (auto simp: primepow_gt_0_nat mangoldt_def)
  also have "primes_psi k = primes_psi x"
    unfolding k_def by simp
  also have "c * real k \<le> c * x"
    using x assms by (intro mult_left_mono) (auto simp: k_def)
  finally show "primes_psi x \<le> c * x" .
qed

end

end