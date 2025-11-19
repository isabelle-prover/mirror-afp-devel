theory Lucas_Sequences
  imports Main HOL.Parity
begin

section \<open>Lucas Sequences\<close>

fun \<psi> :: "int \<Rightarrow> nat \<Rightarrow> int" where
"\<psi> A 0 = 0"|
"\<psi> A (Suc 0) = 1"|
"\<psi> A (Suc (Suc n)) = A * (\<psi> A (Suc n)) - (\<psi> A n)"

fun \<chi> :: "int \<Rightarrow> nat \<Rightarrow> int" where
"\<chi> A 0 = 2"|
"\<chi> A (Suc 0) = A"|
"\<chi> A (Suc (Suc n)) = A * (\<chi> A (Suc n)) - (\<chi> A n)"

subsection \<open>Elementary properties\<close>

theorem \<psi>_induct [consumes 0, case_names 0 1 sucsuc]:
  "P 0 \<Longrightarrow> P 1 \<Longrightarrow> (\<And>n. P (n + 1) \<Longrightarrow> P n \<Longrightarrow> P (n + 2)) \<Longrightarrow> P (n::nat)"
  apply (induct rule: \<psi>.induct)
  by simp_all

theorem \<psi>_induct_strict [consumes 0, case_names 0 1 2 sucsuc]:
  "P 0 \<Longrightarrow> P 1 \<Longrightarrow> P 2 \<Longrightarrow> (\<And>n. n>0 \<Longrightarrow> P (n + 1) \<Longrightarrow> P n \<Longrightarrow> P (n + 2)) \<Longrightarrow>  P (n::nat)"
  apply (induct rule: \<chi>.induct)
  apply simp
  apply (metis One_nat_def)
  by (metis One_nat_def Suc_1 Suc_eq_plus1 add_2_eq_Suc' bot_nat_0.not_eq_extremum)

lemma lem0: "n\<ge>2 \<Longrightarrow> \<exists>m. n = Suc (Suc m)"
  by (simp add: nat_le_iff_add)

lemma \<psi>_reverse:
  assumes "n\<ge>1"
  shows "\<psi> A (n-1) = A * (\<psi> A n) - (\<psi> A (n+1))"
proof -
  obtain m where "Suc (Suc m) = n+1"
    by (metis Suc_eq_plus1 add_eq_if assms not_one_le_zero)
  then show ?thesis by auto
qed

text \<open>Strict monotonicity\<close>
lemma lucas_strict_monotonicity: "A>1 \<Longrightarrow> \<psi> A (Suc n) > \<psi> A n \<and> \<psi> A (Suc n) > 0"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc have "A*\<psi> A (Suc n)>(\<psi> A n+\<psi> A (Suc n))" 
    proof -
      from Suc have b1:"A*\<psi> A (Suc n)\<ge>2*\<psi> A (Suc n)"
        by simp
      from Suc have b2:"2*\<psi> A (Suc n)>\<psi> A n+\<psi> A (Suc n)"
        by simp
      from b1 b2 show ?thesis
        using less_le_trans by blast
    qed
  from this and Suc show ?case
    by auto
qed

lemma lucas_monotone1:
  fixes A
  assumes "A>1"
  shows "n\<ge>2 \<longrightarrow> \<psi> A n \<ge> A"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note HR = this
  consider (0) "n=0" | (1) "n=1" | (2)"n\<ge>2" by fastforce
  then show ?case
  proof cases
    case 0
    then show ?thesis by simp
  next
    case 1
    then show ?thesis by simp
  next
    case 2
    then show ?thesis using HR lucas_strict_monotonicity[of "A" "n"] assms by simp
  qed
qed

lemma lucas_monotone2:
  fixes A n m
  assumes "A>1"
  shows "\<psi> A n \<le> \<psi> A (n+m)"
proof (induction m)
  case 0
  then show ?case using assms by auto
next
  case (Suc m)
  then show ?case using lucas_strict_monotonicity[of A "n+m"] assms by auto
qed

lemma lucas_monotone3:
  fixes A n
  assumes "A > 1"
  shows "\<psi> A n \<ge> int n"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case using lucas_strict_monotonicity[of A n] assms by auto
qed

lemma lucas_monotone4:
  fixes A n m
  assumes "A>1" and "n \<le> m"
  shows "\<psi> A n \<le> \<psi> A m"
proof -
  obtain k where "m = n + k" using assms less_eqE by blast
  thus ?thesis using lucas_monotone2[of A n k]  assms by auto
qed


(* Exponential growth *)
lemma lucas_exp_growth_lt:
  fixes A::int and n::nat
  assumes "A>1"
  shows "\<psi> A (Suc (Suc (Suc n))) < A^(n+2)"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  note t = this
  have " \<psi> A m \<ge> 0" for m
  proof (cases m)
    case 0
    then show ?thesis by auto
  next
    case (Suc nat)
    then show ?thesis using assms lucas_strict_monotonicity[of A nat] by auto
  qed
  then have maj1 : "\<And>m. m>0 \<Longrightarrow>  \<psi> A (Suc (Suc m)) \<le> A * \<psi> A (Suc m)"
    by (simp add: lucas_strict_monotonicity)
  have triv : "A^(Suc n +2) = A* A^(n+2)" by auto
  have maj2 : "\<psi> A (Suc (Suc (Suc (Suc n))))
    \<le> A * \<psi> A (Suc (Suc (Suc n)))"
    apply (rule maj1[of "Suc (Suc n)"]) by auto
  have maj3 : "A * \<psi> A (Suc (Suc (Suc n))) < A* A^(n+2)"
    using t assms by auto
  have maj4 : "\<psi> A (Suc (Suc (Suc (Suc n)))) < A* A^(n+2)"
    using maj2 maj3 by auto
then show ?case using maj4 triv by auto
qed

lemma lucas_exp_growth_le:
  fixes A::int and n::nat
  assumes "A>1"
  shows "\<psi> A (Suc (Suc n)) \<le> A^(n+1)"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  note t = this
  have " \<psi> A m \<ge> 0" for m
  proof (cases m)
    case 0
    then show ?thesis by auto
  next
    case (Suc nat)
    then show ?thesis using assms lucas_strict_monotonicity[of A nat] by auto
  qed
  then have maj1 : "\<And>m. m>0 \<Longrightarrow>  \<psi> A (Suc (Suc m)) \<le> A * \<psi> A (Suc m)"
    by (simp add: lucas_strict_monotonicity)
  have triv : "A^(Suc n +2) = A* A^(n+2)" by auto
  have maj2 : "\<psi> A (Suc  (Suc (Suc n)))
    \<le> A * \<psi> A (Suc (Suc n))"
    apply (rule maj1[of "Suc n"]) by auto
  have maj3 : "A * \<psi> A  (Suc (Suc n)) \<le> A* A^(n+1)"
    using t assms by auto
  have maj4 : "\<psi> A (Suc (Suc (Suc n))) \<le> A* A^(n+1)"
    using maj2 maj3 by auto
then show ?case using maj4 triv by auto
qed

lemma lucas_exp_growth_gt:
  fixes A::int and n::nat
  assumes "A>1"
  shows "\<psi> A (Suc (Suc n)) > (A-1)^(n+1)"
proof (induction n rule: \<psi>_induct)
  case 0
  then show ?case by auto
next
  case 1
  have "1 - 2*A < -1" using assms by auto
  then have m1:  "A*A - 2*A + 1 < A*A - 1" by auto
  moreover have m2: "(A-1)^(1+1) = A*A - 2 * A + 1"
    apply simp
    by (smt (verit, ccfv_SIG) mult_cancel_left2 square_diff_square_factored)
  moreover have "\<psi> A (Suc (Suc 1)) = A*A - 1" by auto
  then show ?case using m1 m2 by auto
next
  case (sucsuc n)
  note t = this
  have m1: "\<And>m. \<psi> A (m+1) \<ge>  \<psi> A m "
    using assms lucas_strict_monotonicity[of A m]
    by (metis Suc_eq_plus1_left add.commute lucas_strict_monotonicity not_le_imp_less not_less_iff_gr_or_eq)
  have m2: "\<psi> A (Suc (Suc (n+1))) \<ge>  \<psi> A (Suc (Suc n))"
    using m1[of "Suc (Suc n)"] by auto
  then have m3: "\<psi> A (Suc (Suc (n+1))) - \<psi> A (Suc (Suc (n)))\<ge> 0"
    by auto
  have m4: "\<And>m. m \<ge> 0 \<Longrightarrow> m + (A-1) * \<psi> A (Suc (Suc (n+1))) \<ge> (A-1) * \<psi> A (Suc (Suc (n+1)))"
    by auto
  have "A*\<psi> A (Suc (Suc (n+1))) - \<psi> A (Suc (Suc n)) \<ge> (A-1) * \<psi> A (Suc (Suc (n+1)))"
    using m4[of "\<psi> A (Suc (Suc (n+1))) - \<psi> A (Suc (Suc (n)))"]
    by (smt (z3) left_diff_distrib' m3 mult_cancel_right1)
  then have m5: "\<psi> A (Suc (Suc (n+2))) \<ge> (A-1) * \<psi> A (Suc (Suc (n+1)))"
    by auto
  have triv: "\<And>m k. m\<ge>k \<Longrightarrow> (A-1)*m \<ge> (A-1)*k"
    using assms by auto
  have "(A-1) * \<psi> A (Suc (Suc (n+1))) \<ge> (A-1) * (A-1) ^ (n + 1 + 1)"
   using triv[of "\<psi> A (Suc (Suc (n+1)))" "(A-1) ^(n + 1 + 1)"] t assms by auto
  then have m6: "\<psi> A (Suc (Suc (n+2))) \<ge> (A-1)*(A - 1) ^ (n + 1 + 1)"
    using m5 by auto 
  then have m7: "(A-1)*(A - 1) ^ (n + 1 + 1) = (A-1)^(n+2+1)"
    by auto
  then show ?case using m6 m7
    by (smt (verit, best) assms m5 mult_strict_left_mono t(1))
qed

(* Symmetry in A *)
lemma lucas_symmetry_A:
  fixes A::int and n::nat
  assumes "A \<ge> 2"
  shows "(\<psi> A n) = (if (odd n) then \<psi> (-A) n else - \<psi> (-A) n)"
proof -
  consider (0) "n=0" | (1) "n=1" | (suc) "n\<ge>2" by fastforce
  then show ?thesis
  proof cases
    case 0
    then show ?thesis by simp
  next
    case 1
    then show ?thesis by simp
  next
    case suc
    then show ?thesis
    proof (induction n rule: full_nat_induct)
      case (1 n)
      then show ?case
        using assms lem0[of n] "1.prems"
        using le_Suc_eq by auto
      qed
  qed
qed

lemma lucas_symmetry_A2: "-\<psi> A n = (-1::int)^n * \<psi> (-A) n"
proof(induction n rule: \<psi>_induct)
  case 0
  then show ?case by simp
next
  case 1
  then show ?case by simp
next
  case (sucsuc n)
  then show ?case 
    by (auto simp add: algebra_simps)
qed

lemma lucas_symmetry_A_abs: assumes "abs A > 1" shows "abs (\<psi> A n) = \<psi> (abs A) n"
proof (cases "n=0")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis using lucas_strict_monotonicity[of "abs A" "n-1"] lucas_symmetry_A2[of "A" n] assms
    by (smt (z3) One_nat_def Suc_pred lucas_symmetry_A not_gr_zero)
qed

(* Special behavior for A=2 *)
lemma lucas_A_eq_2:
  fixes  n::nat
  shows "(\<psi> 2 n) = (int n)"
proof -
  consider (0) "n=0" | (1) "n=1" | (suc) "n\<ge>2" by fastforce
  then show ?thesis
  proof cases
    case 0
      then show ?thesis by simp
    next
      case 1
      then show ?thesis by simp
    next
      case suc
      then show ?thesis
      proof (induction n rule: full_nat_induct)
        case (1 n)
        then show ?case
          using lem0[of n]
          using "1.prems" \<psi>.simps(2) eq_numeral_Suc le_Suc_eq le_simps(1) lessI numeral_Bit0
                of_nat_0
          by fastforce     
      qed
   qed
 qed

(* Behavior modulo N *)
lemma lucas_periodic_modN:
  fixes N::int
  assumes "N > 0"
  shows "\<exists>T\<ge>1. \<forall>n. (\<psi> A (T + n)) mod N = (\<psi> A n) mod N"
proof -
  define f where "f \<equiv> (\<lambda>r. ((\<psi> A r) mod N, (\<psi> A (r+1)) mod N))"
  then have 0: "f ` {1..(nat(N^2)+1)} \<subseteq> ({0..(N-1)} \<times> {0..(N-1)})"
    using pos_mod_bound pos_mod_sign assms
    by auto
  have "finite ({0..(N-1)} \<times> {0..(N-1)})"
    by auto
  then have 1: "card(f ` {1..(nat(N^2)+1)}) \<le> card (({0..(N-1)} \<times> {0..(N-1)}))"
    using 0 Finite_Set.card_mono
    by blast
  have "card ({0..(N-1)} \<times> {0..(N-1)}) = nat(N^2)"
    apply simp
    by (smt (verit, del_insts) assms nat_power_eq power2_eq_square)
  then have 2: "card(f ` {1..(nat(N^2)+1)}) < card({1..(nat(N^2)+1)})"
    using 0 1
    by auto
  then have "\<not> inj_on f {1..(nat(N^2)+1)}"
    using Finite_Set.pigeonhole
    by blast
  then have 3: "\<exists>r\<in>{1..(nat(N^2)+1)}. \<exists>s\<in>{1..(nat(N^2)+1)}. (f r = f s) \<and> r \<noteq> s"
    using inj_on_def
    by blast
  then obtain r s where def_rs:"(f r = f s) \<and> r \<noteq> s" by auto
  define b a where def_b: "b \<equiv> max r s" and def_a: "a \<equiv> min r s"
  then have prop_ab:"f a = f b \<and> a < b"
    using def_rs
    by (simp add: max_def min_def)
  have prop_rec_desc: "\<forall>k. k\<le>a \<longrightarrow> f (b-k) = f(a-k)"
  proof
    fix k
    show "k\<le>a \<longrightarrow> f (b-k) = f(a-k)"
    proof (induction k)
      case 0
      then show ?case using prop_ab by simp
    next
      case (Suc k)
      then show ?case
      (* Distinguishing whethe 0=a-k is reached or not *)
      proof (cases "k=a")
        case True
        then show ?thesis by auto
      next
        case False
        assume HR: "k \<le> a \<longrightarrow> f (b - k) = f (a - k)"
        assume "k\<noteq>a"
        have "Suc k \<le> a \<Longrightarrow> f (b - Suc k) = f (a - Suc k)"
        proof -
          assume k_small_a: "(Suc k) \<le> a"
          (* Trivial inequalities that simplify lemma applications later *)
          then have k_small: "a-k \<ge> 1" "b-k \<ge> 1" using prop_ab by auto
          have "k\<le>a" using k_small_a by simp
          (* Beginning of calculations *)
          then have eg1: "(\<psi> A (a-k)) mod N = (\<psi> A (b-k)) mod N \<and> \<psi> A (a-k+1) mod N = (\<psi> A (b-k+1)) mod N"
            using HR f_def by force
          have eg2: "\<psi> A (a-k-1) = A * \<psi> A (a-k) - \<psi> A (a-k+1) \<and> \<psi> A (b-k-1) = A * \<psi> A (b-k) - \<psi> A (b-k+1)"
            using k_small \<psi>_reverse[of "a-k" "A"] \<psi>_reverse[of "b-k" "A"]
            by auto
          then have "(\<psi> A (a-k-1)) mod N = (A * \<psi> A (a-k) - \<psi> A (a-k+1)) mod N"
            by presburger
          also have "... = (A * \<psi> A (b-k) - \<psi> A (b-k+1)) mod N"
            using eg1 by (metis mod_diff_cong mod_mult_cong)
          finally have eg3: "(\<psi> A (a-k-1)) mod N = (\<psi> A (b-k-1)) mod N" 
            using eg2 by presburger
          then show  "f (b - Suc k) = f (a - Suc k)" using eg1 k_small
            by (smt (z3) diff_Suc_eq_diff_pred diff_commute f_def le_add_diff_inverse2)
        qed
        then show ?thesis by (rule impI)
      qed
    qed
  qed
  define T where def_T: "T \<equiv> b-a"
  then have T1: "T\<ge>1" using prop_ab
    by (simp add: Suc_leI)
  have "f T = f 0" using prop_rec_desc def_T by auto
  then have 0: "(\<psi> A T) mod N = (\<psi> A 0) mod N \<and> (\<psi> A (T+1)) mod N = (\<psi> A 1) mod N"
    using f_def by simp
  have "\<forall>k. (\<psi> A (T+k)) mod N = (\<psi> A k) mod N"
  proof
    fix k
    show "(\<psi> A (T+k)) mod N = (\<psi> A k) mod N" using 0
    proof (induction k rule:\<psi>_induct)
    case 0
      then show ?case by simp
    next
      case 1
      then show ?case by simp
    next
      case (sucsuc n)
      then have n:"\<psi> A (T+n) mod N = \<psi> A (n) mod N"
        using sucsuc.IH(1) sucsuc.prems by simp
      then have n1:"\<psi> A (T+(Suc n)) mod N = \<psi> A (Suc n) mod N"
        using sucsuc.IH(1) sucsuc.prems by simp
      have "\<psi> A (T+(Suc (Suc n))) mod N = (A * \<psi> A (Suc (T + n)) - \<psi> A (T + n)) mod N"
        by simp
      also have "... = (A * \<psi> A (Suc (T + n)) mod N - \<psi> A (T + n) mod N) mod N"
        by (metis mod_diff_eq)
      also have "... = (A * \<psi> A (Suc (n)) mod N - \<psi> A (n) mod N) mod N"
        using n n1 by (metis add_Suc_right mod_mult_cong)
      also have "... = (A * \<psi> A (Suc (n)) - \<psi> A (n)) mod N"
        by (metis mod_diff_eq)
      finally have "\<psi> A (T+(Suc (Suc n))) mod N = \<psi> A ((Suc (Suc n))) mod N" by simp
      then show ?case using add_2_eq_Suc' by presburger
    qed
  qed
  then show ?thesis using T1 by auto
qed

(* Lemma 3.1, sublemma 8 *)
lemma lucas_modN:
  fixes N::int
  assumes "N>0" 
  shows "\<forall>n. \<exists>k\<ge>n. \<psi> A k mod N = 0"
proof
  fix n
  have "\<exists>T\<ge>1. \<forall>n. (\<psi> A (T + n)) mod N = (\<psi> A n) mod N"
    using lucas_periodic_modN assms
    by blast
  then obtain T where def_T: "\<forall>n. (\<psi> A (T+n)) mod N = (\<psi> A n) mod N \<and> T\<ge>1"
    by auto
  have 0: "\<forall>k. (\<psi> A (T * k)) mod N = 0"
  proof
    fix k
    show "(\<psi> A (T * k)) mod N = 0"
    proof (induction k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      then show ?case using def_T by simp
    qed
  qed
  define K where def_K : "K \<equiv> T * n"
  then have 1: "K\<ge>n" using def_T by auto
  have "(\<psi> A K) mod N = 0" using 0 def_K by auto
  then show "\<exists>k\<ge>n. \<psi> A k mod N = 0" using 1 by auto
qed

(* Parity *)
lemma lucas_parity:
  fixes A::int and B::nat
  assumes "even A"
  shows "even (\<psi> A B) = even B"
proof(induction B rule: \<psi>_induct)
  case 0
  then show ?case
    by simp
next
  case 1
  then show ?case
    by simp
next
  case (sucsuc n)
  then show ?case 
    by (auto simp add: assms)
qed

corollary lucas_parity2:
  fixes A::int and B::nat
  assumes "even A"
  shows "even (\<psi> A B - int B)"
  by (simp add: assms lucas_parity)


(* Monotonicity in A *)
lemma lucas_monotone_A:
  assumes "1<A" "A\<le>A'"
  shows "\<psi> A n \<le> \<psi> A' n"
proof (induction n rule:\<psi>_induct)
  case 0
  then show ?case by simp
next
  case 1
  then show ?case by simp
next
  case (sucsuc n)
  note HR = this
  consider (equal) "A=A'" | (strict) "A<A'" using assms by fastforce
  then show ?case
  proof cases
    case equal
    then show ?thesis by simp
  next
    case strict
    have "\<psi> A n \<ge> 0"
    proof (cases "n=0")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis using lucas_strict_monotonicity[of "A" "n-1"] assms by auto
    qed
    then have "\<psi> A (n + 2) = A * \<psi> A (n+1) - \<psi> A n" by simp
    also have "... \<le> A * \<psi> A (n+1)" using \<open>\<psi> A n \<ge> 0\<close> by simp
    also have "... \<le> (A' - 1) * \<psi> A (n+1)" using \<open>A<A'\<close> assms(1) lucas_strict_monotonicity by auto
    also have "... \<le> (A' - 1) * \<psi> A' (n+1)" using assms HR by simp
    also have "... \<le> A' * \<psi> A' (n+1) - \<psi> A' n" using lucas_strict_monotonicity[of "A'" "n"] assms Suc_eq_plus1 int_distrib(3) by fastforce
    finally have "\<psi> A (n + 2) \<le> \<psi> A' (n+2)" by simp
    then show ?thesis by simp
  qed
qed

(* Lemma 3.5 *)
lemma lucas_congruence:
  fixes A::int and B::int and n::int
  assumes "n=n \<and> A mod n = B mod n"
  shows "(\<psi> A m) mod n = (\<psi> B m) mod n"
proof (induction m rule: \<psi>_induct)
  case 0
  then show ?case by auto
next
  case 1
  then show ?case by auto
next
  case (sucsuc m)
  note t = this
  have e1: "(A * \<psi> A (m + 1)) mod n = (B * \<psi> B (m + 1)) mod n"
    using assms mod_mult_cong sucsuc.IH(1) by blast
  then have e2: "\<And>k l. k mod n = l mod n \<Longrightarrow> (A * \<psi> A (m + 1) - k) mod n =  (B * \<psi> B (m + 1) - l) mod n"
    using mod_diff_cong by blast
  have e3: "(A * \<psi> A (m + 1) - \<psi> A m) mod n = (B * \<psi> B (m + 1) - \<psi> B m) mod n"
    using t e2[of "\<psi> A m" "\<psi> B m"] by blast
  then show ?case by auto
qed

(* Corollary 3.6 *)
corollary lucas_congruence2:
  fixes \<alpha>::int and m::nat
  shows "\<psi> \<alpha> m mod (\<alpha> - 2) = int m mod (\<alpha> - 2)"
proof -
  have fac1: "\<psi> 2 a = int a" for a
  proof (induction a rule: \<psi>_induct)
    case 0
    then show ?case by auto
  next
    case 1
    then show ?case by auto
  next
    case (sucsuc n)
  then show ?case by auto
qed
  have "\<alpha> mod (\<alpha> - 2) = 2 mod (\<alpha> -2)"
    by (smt (z3) minus_mod_self2)
  then have fac2: "\<psi> \<alpha> m mod (\<alpha> - 2) = \<psi> 2 m mod (\<alpha> - 2)"
    using lucas_congruence[of "\<alpha> - 2" \<alpha> 2 m] by auto
  then show ?thesis using fac2 fac1 by auto
qed

end
