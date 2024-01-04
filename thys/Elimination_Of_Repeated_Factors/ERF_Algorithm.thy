(*
  File:      Elimination_Of_Repeated_Factors/ERF_Algorithm.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  An executable algorithm to split a polynomial over a perfect field
  into a product of pairwise coprime, squarefree (but not necessarily irreducible)
  polynomials.

  This is useful as a preprocessing stage for full factoring algorithms,
  which typically assume the input to be squarefree.

  It can also be used to compute the radical of a polynomial, i.e. the
  product of its prime factors.

  Note that, most notably, perfect fields cover both fields of characteristic 0
  (where the algorithm is trivial) and finite fields (i.e. Galois fields).
*)
theory ERF_Algorithm
imports
  ERF_Perfect_Field_Factorization
begin


section \<open>Elimination of Repeated Factors Algorithm\<close>

text \<open>This file contains the elimnation of repeated factors (ERF) algorithm for polynomials over 
perfect fields.
This algorithm does not only work over fields with characteristic $0$ like the classical Yun Algorithm
but also for example over finite fields with prime characteristic (i.e.\ $\mathbb{F}_q[x]$ for $q=p^n$, 
$n\in\mathbb{N}$ and $p$ prime). 
Intuitively, the ERF algorithm proceeds similarly to the classical Yun algorithm, taking the gcd 
of the polynomial and its derivative and thus eliminating repeated factors iteratively.
However, if we work over finite characteristic, prime factors with exponent divisible by the 
characteristic $p$ are cancelled out since $p\equiv 0$.
Therefore, we separate prime factors with exponent divisible by the characteristic from the rest
and treat them seperately in the ERF algorithm.\<close>

text \<open>Since we use the \<open>gcd\<close>, we need the additional type constraint \<open>field_gcd\<close>.\<close>
context
assumes "SORT_CONSTRAINT('e::{perfect_field, field_gcd})"
begin

text \<open>The funtion \<open>ERF_step\<close> describes the main body of the ERF algorithm. 
Let us walk through the algorithm step by step. 
\begin{itemize}
\item A polynomial of degree $0$ is constant and thus there is nothing to do.
\item We only consider the monic part of our polynomial $f$ using the \<^const>\<open>normalize\<close> function.
\item $u$ is the gcd of the monic $f$ and its derivative. 
\item $u=1$ iff $f$ is already square-free. If the characteristic is zero, this property is already 
fulfilled. Otherwise we continue and denote the (prime) characteristic by $p$. 
\item If $u\neq 1$, we split $f$ in a part $v$ and $w$. $v$ is already square-free and contains all
prime factors with exponent not divisible by $p$.
\item $w$ contains all prime factors with exponent divisible by $p$. Thus we can take the $p$-th 
root of $w$ (by using the inverse Frobenius homomorphism \<^const>\<open>inv_frob_poly\<close>) 
and obtain $z$ (which we will further reduce in an iterative step).
\end{itemize}\<close>

definition ERF_step ::"'e poly \<Rightarrow> _" where
  "ERF_step f = (if degree f = 0 then None else (let
     f_mono = normalize f;
     u = gcd f_mono (pderiv f_mono);
     n = degree f
  in (if u = 1 then None else let
    v = f_mono div u;
    w = u div gcd u (v^n);
    z = inv_frob_poly w
    in Some (v, z)
  )
))"

lemma ERF_step_0 [simp]: "ERF_step 0 = None"
  unfolding ERF_step_def by auto

lemma ERF_step_const: "degree f = 0 \<Longrightarrow> ERF_step f = None"
  unfolding ERF_step_def by auto

text \<open>For the correctness proof of the \<^const>\<open>ERF_step\<close> algorithm, we need to show that $u$, $v$ and $w$ have
the correct form.\<close>

text \<open>Let $f = \prod _i f_i^{e_i}$ where we assume $f$ to be monic and $f_i$ are the prime factors with
exponents $e_i$. Let furthermore $P_1 = \{f_i.\ p \nmid e_i\}$ and $P_2 = \{f_i.\ p \mid e_i\}$.
Then we have $$u = \prod_{f_i\in P_1} f_i^{e_i-1} \cdot \prod _{f_i\in P_2} f_i^{e_i} $$.\<close>

lemma u_characterization :
  fixes f::"'e poly"
  assumes "degree f \<noteq> 0" 
  and u_def: "u = gcd (normalize f) (pderiv (normalize f))"
  shows "u = (let fm' = normalize f in
                (\<Prod>fj\<in>prime_factors fm'. let ej = multiplicity fj fm' in 
                (if CHAR('e) dvd ej then  fj ^ ej else fj ^(ej-1))))" (is ?u)
    and "u = (let fm' = normalize f; P1 = {f\<in>prime_factors fm'. \<not> CHAR('e) dvd multiplicity f fm'};
               P2 = {f\<in>prime_factors fm'. CHAR('e) dvd multiplicity f fm'} in 
              (\<Prod>fj\<in>P1. fj^(multiplicity fj fm' -1)) * (\<Prod>fj\<in>P2. fj^(multiplicity fj fm')))"
(is ?u')
proof -
  define p where "p = CHAR('e)"
  \<comment> \<open>Here we import the lemmas on the factorization of polynomials over a finite field\<close>
  interpret perfect_field_poly_factorization "TYPE('e)" f p
  proof 
    show "degree f \<noteq> 0" using assms by auto
  qed (auto simp add: p_def)
  
  have "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    if "pderiv fm = 0"
  proof -
    have "u = fm" unfolding u_def \<open>pderiv fm = 0\<close> using fm_def that by auto
    moreover have "fm = (\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else 
      fj ^(ej-1)))"
      using pderiv0_p_dvd_count[OF _ that] unfolding Let_def f_fac prod_mset_multiplicity
      by (intro prod.cong) (simp add:fac_set_def fac_def, auto)
    ultimately show ?thesis by auto
  qed

  moreover have "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    if "pderiv fm \<noteq> 0"
  unfolding u_def fm_def[symmetric] proof (subst gcd_eq_factorial', goal_cases)
    case 3
    let ?prod_pow = "(\<Prod>p\<in>prime_factors fm \<inter> prime_factors (pderiv fm).
        p ^ min (multiplicity p fm) (multiplicity p (pderiv fm)))"
    have norm: "normalize ?prod_pow = ?prod_pow" by (intro normalize_prod_monics)
      (metis Int_iff dvd_0_left_iff in_prime_factors_iff monic_normalize normalize_prime)
    have subset: "prime_factors fm \<inter> prime_factors (pderiv fm) \<subseteq> fac_set" 
      unfolding fac_set_def by auto
    show ?case unfolding norm proof (subst prod.mono_neutral_left[OF _ subset], goal_cases)
      case 2
      have "i \<in># prime_factorization (pderiv fm)"  if "i \<in> fac_set" "ei = count fac i"
           "i ^ min ei (multiplicity i (pderiv fm)) \<noteq> 1" for i ei
      proof (intro prime_factorsI)
        have "min ei (multiplicity i (pderiv fm)) \<noteq> 0" using that(3) by (metis power_0)
        then have "multiplicity i (pderiv fm) \<ge> 1" by simp
        then show "i dvd pderiv fm"
          using not_dvd_imp_multiplicity_0 by fastforce
        show "pderiv fm \<noteq> 0" "prime i" using \<open>pderiv fm \<noteq> 0\<close> \<open>i \<in> fac_set\<close> 
          unfolding fac_set_def by auto
      qed
      then show ?case  using mult_fm unfolding fac_set_def Let_def using ex_def by fastforce
    next
      case 3
      have "x ^ min (multiplicity x fm) (multiplicity x (pderiv fm)) = x ^ multiplicity x fm" 
        if "x \<in> fac_set" "p dvd multiplicity x fm" for x
        using \<open>pderiv fm \<noteq> 0\<close> ex_def mult_deriv that(1) that(2) by fastforce
      moreover have "x ^ min (multiplicity x fm) (multiplicity x (pderiv fm)) =
        x ^ (multiplicity x fm - Suc 0)" if "x \<in> fac_set" "\<not> p dvd multiplicity x fm" for x
        using P1_def \<open>pderiv fm \<noteq> 0\<close> ex_def mult_deriv1 that(1) that(2) by auto
      ultimately show ?case by (intro prod.cong, simp, unfold Let_def,
         auto simp add: ex_def mult_deriv[OF _ \<open>pderiv fm \<noteq> 0\<close>])
    qed (auto simp add: fac_set_def)  
  qed (auto simp add: fm_nonzero that)
  
  ultimately have u: "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    by blast
  then have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))"
    unfolding Let_def by (smt (verit) P1_def P2_def P1_P2_intersect fac_set_P1_P2 
      finites(2) finites(3) mem_Collect_eq prod.cong prod.union_disjoint)
  
  show ?u using u unfolding ex_def fm_def fac_set_def unfolding Let_def p_def by auto
  show ?u' using u' unfolding local.P1_def local.P2_def 
    unfolding p_def ex_def fm_def Let_def fac_set_def by auto
qed

text \<open>Continuing our calculations, we get: $$ v = \prod _{f_i\in P_1} f_i$$
Therefore, $v$ is already square-free and $v$'s prime factors are exactly $P_1$.\<close>

lemma v_characterization:
assumes "ERF_step f = Some (v,z)"
shows "v = (let fm = normalize f in fm div (gcd fm (pderiv fm)))" (is ?a)
and "v = \<Prod>{x\<in>prime_factors (normalize f). \<not> CHAR('e) dvd multiplicity x (normalize f)}" (is ?b)
and "prime_factors v = {x\<in>prime_factors (normalize f). \<not> CHAR('e) dvd multiplicity x (normalize f)}"(is ?c)
and "squarefree v"(is ?d)
proof -
  define p where "p = CHAR('e)"
  have [simp]: "degree f \<noteq> 0" using assms unfolding ERF_step_def by (metis not_None_eq)

(* We import the factorization lemmas and the characterization of u.*)
  interpret perfect_field_poly_factorization "TYPE('e)" f p
  proof (unfold_locales)
    show "p = CHAR('e)" by (rule p_def)
    show "degree f \<noteq> 0" by auto
  qed

  define u where "u = gcd fm (pderiv fm)"
  have u_def': "u = gcd (normalize f) (pderiv (normalize f))" unfolding u_def fm_def by auto
  have u: "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    using u_characterization[OF \<open>degree f \<noteq> 0\<close>] u_def 
    unfolding fm_def Let_def fac_set_def ex_def p_def
    by blast 
  have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))" 
    using u_characterization(2)[OF \<open>degree f \<noteq> 0\<close> u_def'] unfolding fm_def[symmetric] Let_def 
      fac_set_def[symmetric] ex_def[symmetric] p_def[symmetric]
    using P1_def P2_def ex_def by presburger

  have v_def: "v = fm div u" unfolding fm_def u_def using assms unfolding ERF_step_def 
    by (auto split: if_splits simp add: Let_def)
  then show ?a unfolding u_def fm_def Let_def by auto

  have v: "v = \<Prod>P1" 
  proof -
    have "v = ((\<Prod>fj\<in>P1. fj^(ex fj)) * (\<Prod>fj\<in>P2. fj^(ex fj))) div u" 
      unfolding v_def fm_P1_P2 by auto
    also have "\<dots> = (\<Prod>fj\<in>P1. fj^(ex fj)) div (\<Prod>fj\<in>P1. fj^(ex fj-1))" unfolding u Let_def
    by (metis (no_types, lifting) fm_nonzero div_div_div_same dvd_triv_right fm_P1_P2 mult_not_zero 
      nonzero_mult_div_cancel_right semiring_gcd_class.gcd_dvd1 u u' u_def)
    also have "\<dots> = \<Prod>P1"
    proof -
      have *: "(\<Prod>fj\<in>P1. fj^(ex fj)) = (\<Prod>P1) * (\<Prod>fj\<in>P1. fj^(ex fj-1))"
      by (smt (z3) P1_def dvd_0_right mem_Collect_eq power_eq_if prod.cong prod.distrib)
      show ?thesis unfolding * by auto
    qed
    finally show ?thesis by auto
  qed
  then show ?b unfolding P1_def fac_set_def fm_def ex_def unfolding p_def by auto

  have prime_factors_v: "prime_factors v = P1" unfolding v 
  proof (subst prime_factors_prod[OF finites(2)], goal_cases)
    case 1
    then show ?case using fac_set_P1_P2 nonzero by blast
  next
    case 2
    have prime: "prime x" if "x\<in>P1" for x using P1_def fac_set_def that by blast
    have "\<Union> (prime_factors ` P1) = P1" using prime[THEN prime_prime_factors] by auto
    then show ?case by simp
  qed
  then show ?c unfolding P1_def fac_set_def ex_def fm_def unfolding p_def by auto

  show "squarefree v" proof (subst squarefree_factorial_semiring', safe, goal_cases)
    case (2 p)
    have "0 \<notin> (\<lambda>x. x) ` P1" using prime_factors_v P1_prime_elem by fastforce
    moreover have "prime_elem p" using "2" in_prime_factors_imp_prime by blast 
    moreover have "sum (multiplicity p) P1 = 1"
      by (metis "2" finites(2) calculation(2) in_prime_factors_imp_prime multiplicity_prime 
      prime_factors_v prime_multiplicity_other sum_eq_1_iff)
    ultimately show ?case using 2 unfolding prime_factors_v unfolding v 
      by (subst prime_elem_multiplicity_prod_distrib) auto
  qed (simp add: v P1_def)
qed

text \<open>For the definition of $w$, we only want to get the prime factors in $P_2$. 
Therefore, we kick out all prime factors in $P_1$ from $f$ by calculating this gcd.
$$\gcd (u, v^{\deg f}) = \prod_{f_i\in P_1} f_i^{e_i-1} $$\<close>

lemma gcd_u_v: 
  assumes "ERF_step f = Some (v,z)"
  shows "let fm = normalize f; u = gcd fm (pderiv fm); 
  P1 = {x\<in>prime_factors fm. \<not> CHAR('e) dvd multiplicity x fm} in
gcd u (v^(degree f)) = (\<Prod>fj\<in>P1. fj ^(multiplicity fj fm -1))"
proof -
  define p where "p = CHAR('e)"
  have [simp]: "degree f \<noteq> 0" using assms unfolding ERF_step_def by (metis not_None_eq)

  \<comment> \<open>We import the lemmas on factorization, the characterizations of u and v\<close>
  interpret perfect_field_poly_factorization "TYPE('e)" f p
  proof 
    show "p = CHAR('e)" by (rule p_def)
    show "degree f \<noteq> 0" by auto
  qed

  define u where "u = gcd (normalize f) (pderiv (normalize f))"
  have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))" 
    using u_characterization(2)[OF \<open>degree f \<noteq> 0\<close> u_def] unfolding fm_def[symmetric] Let_def 
      fac_set_def[symmetric] ex_def[symmetric] p_def[symmetric]
    using P1_def P2_def ex_def by presburger
  have v: "v = \<Prod>P1" using v_characterization(2)[OF assms] unfolding P1_def fac_set_def fm_def ex_def
    using p_def by auto
  have prime_factors_v: "prime_factors v = P1" using v_characterization(3)[OF assms]
    unfolding P1_def fac_set_def ex_def fm_def using p_def by auto
  have v_def: "v = fm div u" unfolding fm_def u_def using assms unfolding ERF_step_def 
    by (auto split: if_splits simp add: Let_def)

  have "gcd u (v^(degree f)) = (\<Prod>fj\<in>P1. fj ^(multiplicity fj fm -1))" unfolding u' v 
  proof (subst gcd_mult_left_right_cancel, goal_cases)
    case 1
    then show ?case by (simp add: P1_P2_coprime prod_coprime_left)
  next
    case 2
    have nonzero1: "(\<Prod>fj\<in>P1. fj ^ (ex fj - 1)) \<noteq> 0" using ex_def by auto
    have nonzero2: "\<Prod>P1 ^ (degree f) \<noteq> 0" using prime_factors_v v v_def by fastforce
    have null: "0 \<notin> (\<lambda>fj. fj ^ (ex fj - Suc 0)) ` P1" using prime_factors_v nonzero1 by force
    have null': "0 \<notin> (\<lambda>x. x) ` P1" using prime_factors_v P1_irreducible by blast
    have P1: "prime_factors (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) \<inter> prime_factors (\<Prod>P1 ^ (degree f)) = 
      {x\<in>P1. ex x > 1}"
    proof (subst prime_factors_prod[OF finites(2) null],
           subst prime_factors_power[OF deg_f_gr_0],
           subst prime_factors_prod[OF finites(2) null'],
           unfold comp_def, safe, goal_cases)
      case (1 x xa xb) then show ?case by (metis dvd_trans in_prime_factors_iff prime_factors_v) 
    next
      case (2 x xa xb)
      then have "x = xa"
        by (metis in_prime_factors_iff prime_dvd_power prime_factors_v primes_dvd_imp_eq)
      then have "x \<in># prime_factorization (x ^ (ex x - 1))" using 2 by auto
      then show ?case
      by (metis gr0I in_prime_factors_iff not_prime_unit power_0 zero_less_diff)
    next
      case (3 x) then show ?case 
      by (smt (verit) One_nat_def Totient.prime_factors_power dvd_refl image_ident 
        in_prime_factors_iff mem_simps(8) null' prime_factors_v zero_less_diff) 
    next
      case (4 x) then show ?case
      by (metis dvd_refl in_prime_factors_iff mem_simps(8) not_prime_0 prime_factors_v) 
    qed
    have n: "ex fj \<le> degree f" if "fj\<in>P1" for fj
    proof -
      have "fj \<noteq> 0" using that unfolding P1_def by auto
      have "degree (fj ^ multiplicity fj fm) \<le> degree f" 
        using divides_degree[OF multiplicity_dvd] fm_nonzero 
        by (subst degree_normalize[of f, symmetric], unfold fm_def[symmetric]) auto
      then have "degree fj * ex fj \<le> degree f" by (subst degree_power_eq[OF \<open>fj\<noteq>0\<close>, symmetric],
        unfold ex_def) 
      then show ?thesis 
      by (metis Missing_Polynomial.is_unit_field_poly \<open>fj \<noteq> 0\<close> bot_nat_0.not_eq_extremum 
        dual_order.trans dvd_imp_le dvd_triv_right empty_iff in_prime_factors_iff 
        linordered_semiring_strict_class.mult_pos_pos prime_factorization_1 prime_factors_v 
        semiring_norm(160) set_mset_empty that)
    qed
    then have min: "min (ex x - Suc 0) (degree f) = ex x -1" if "x\<in>P1" for x using n[OF that] by auto
    have mult1: "multiplicity g (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) = ex g -1" if "g\<in>P1" for g
    proof -
      have "prime_elem g" using in_prime_factors_imp_prime prime_factors_v that by blast
      have "multiplicity g (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0)) = 
            multiplicity g (g^(ex g -1) * (\<Prod>fj\<in>P1-{g}. fj ^ (ex fj - Suc 0)))"
        by (subst prod.remove[OF finites(2) \<open>g\<in>P1\<close>], auto)
      also have "\<dots> = multiplicity g ((\<Prod>fj\<in>P1-{g}. fj ^ (ex fj - Suc 0)) * g^(ex g -1))"
        by (auto simp add: algebra_simps)
      also have "\<dots> = multiplicity g (g^(ex g -1))" 
      proof (intro multiplicity_prime_elem_times_other[OF \<open>prime_elem g\<close>], rule ccontr, safe) 
        assume ass: "g dvd (\<Prod>fj\<in>P1 - {g}. fj ^ (ex fj - Suc 0))"
        have "irreducible g" using \<open>prime_elem g\<close> by blast
        obtain a where "a\<in>P1-{g}" "g dvd a ^ (ex a -1)" 
          using irreducible_dvd_prod[OF \<open>irreducible g\<close> ass]
          by (metis dvd_1_left nat_dvd_1_iff_1)
        then have "g dvd a" by (meson \<open>prime_elem g\<close> prime_elem_dvd_power)
        then show False
        by (metis DiffD1 DiffD2 \<open>a \<in> P1 - {g}\<close> in_prime_factors_imp_prime insertI1 
          prime_factors_v primes_dvd_imp_eq that)
      qed
      also have "\<dots> = ex g -1" by (metis image_ident in_prime_factors_imp_prime 
        multiplicity_same_power not_prime_unit null' prime_factors_v that)
      finally show ?thesis by blast
    qed
    have mult2: "multiplicity g (\<Prod>P1 ^ (degree f)) = (degree f)" if "g\<in>P1" for g  
    proof -
      have "\<Prod>P1\<noteq>0" unfolding P1_def 
      using P1_def in_prime_factors_iff prime_factors_v that v by simp
      have "prime_elem g" using in_prime_factors_imp_prime prime_factors_v that by blast
      have "multiplicity g (\<Prod>P1 ^ (degree f)) = (degree f) * (multiplicity g (\<Prod>P1))" 
        by (subst prime_elem_multiplicity_power_distrib[OF \<open>prime_elem g\<close> \<open>\<Prod>P1\<noteq>0\<close>], auto)
      also have "\<dots> = (degree f) * multiplicity g (g * \<Prod>(P1-{g}))" by (metis finites(2) prod.remove that)
      also have "\<dots> = (degree f) * multiplicity g (\<Prod>(P1-{g}) * g)" by (auto simp add: algebra_simps)
      also have "\<dots> = (degree f)" 
      proof (subst multiplicity_prime_elem_times_other[OF \<open>prime_elem g\<close>]) 
        show "\<not> g dvd \<Prod>(P1 - {g})" by (metis DiffD1 DiffD2 \<open>prime_elem g\<close> 
          as_ufd.prime_elem_iff_irreducible in_prime_factors_imp_prime irreducible_dvd_prod 
          prime_factors_v primes_dvd_imp_eq singletonI that) 
        show "(degree f) * multiplicity g g = (degree f)" 
          by (auto simp add: multiplicity_prime[OF \<open>prime_elem g\<close>])
      qed
      finally show ?thesis by blast
    qed
    have split: "(\<Prod>x\<in>{x \<in> P1. Suc 0 < ex x}. x ^ (ex x - Suc 0)) =
      (\<Prod>fj\<in>P1. fj ^ (ex fj - Suc 0))" 
    proof -
      have *: "ex x \<noteq> 0" if "x\<in>P1" for x by (metis P1_ex_nonzero of_nat_0 that)
      have "Suc 0 < ex x" if "x\<in>P1" "ex x \<noteq> Suc 0" for x using *[OF that(1)] that(2) by auto
      then have union: "P1 = {x\<in>P1. 1 < ex x} \<union> {x\<in>P1. ex x = 1}" by auto
      show ?thesis by (subst (2) union, subst prod.union_disjoint) auto 
    qed
    show ?case by (subst gcd_eq_factorial'[OF nonzero1 nonzero2],subst normalize_prod_monics) 
      (auto simp add: P1 mult1 mult2 min normalize_prod_monics split, auto simp add: ex_def)
  qed
  then show ?thesis unfolding Let_def u_def P1_def fm_def ex_def fac_set_def using p_def by auto
qed

text \<open>Finally, we can calculate $$w = \prod_{f_i\in P_2} f_i^{p \cdot (e_i / p)}$$ and
$$ z = \sqrt[p]{w} = \prod_{f_i\in P_2} f_i^{e_i / p}$$\<close>

text \<open>Now, we can show the correctness of the \<^const>\<open>ERF_step\<close> function. These properties comprise:
\begin{itemize}
\item prime factors of $f$ are either in $v$ or in $z$
\item $v$ is already square-free
\item $z$ is non-zero and the $p$-th power of $z$ divides $f$ (important for the termination of 
the ERF)
\end{itemize}\<close>

lemma ERF_step_correct:
  assumes "ERF_step f = Some (v, z)"                                
  shows   "radical f = v * radical z"
          "squarefree v"
          "z ^ CHAR('e) dvd f"
          "z\<noteq>0"
          "CHAR('e) = 0 \<Longrightarrow> z = 1"
proof -
  define p where "p = CHAR('e)"

  have [simp]: "degree f \<noteq> 0" using assms unfolding ERF_step_def by (metis not_None_eq)

(*Importing the factorization lemmas, characterization of u, v and the gcd*)
  interpret perfect_field_poly_factorization "TYPE('e)" f p
  proof (unfold_locales)
    show "p = CHAR('e)" by (rule p_def)
    show "degree f \<noteq> 0" by auto
  qed

  define u where "u = gcd fm (pderiv fm)"
  define n where "n = degree f"
  define w where "w = u div (gcd u (v^n))"
  have u_def': "u = gcd (normalize f) (pderiv (normalize f))" unfolding u_def fm_def by auto

  have u: "u =(\<Prod>fj\<in>fac_set. let ej = ex fj in (if p dvd ej then  fj ^ ej else fj ^(ej-1)))"
    using u_characterization[OF \<open>degree f \<noteq> 0\<close>] u_def 
    unfolding fm_def Let_def fac_set_def ex_def p_def
    by blast 
  have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))" 
    using u_characterization(2)[OF \<open>degree f \<noteq> 0\<close> u_def'] unfolding fm_def[symmetric] Let_def 
      fac_set_def[symmetric] ex_def[symmetric] p_def[symmetric]
    using P1_def P2_def ex_def by presburger
    
  have v_def: "v = fm div u" unfolding fm_def u_def using assms unfolding ERF_step_def 
    by (auto split: if_splits simp add: Let_def)
  have v: "v = \<Prod>P1" using v_characterization(2)[OF assms] unfolding P1_def fac_set_def fm_def ex_def
    using p_def by auto

  have prime_factors_v: "prime_factors v = P1" 
    using v_characterization(3)[OF assms] unfolding P1_def fac_set_def fm_def ex_def
    using p_def by auto

  show "squarefree v" by (rule v_characterization(4)[OF assms])

  have gcd_u_v: "gcd u (v^n) = (\<Prod>fj\<in>P1. fj ^(ex fj -1))" using gcd_u_v[OF assms]
    unfolding Let_def u_def fm_def P1_def fac_set_def ex_def using p_def n_def by force
  
(*New: Show properties of w and z*)
  have w: "w = (\<Prod>fj\<in>P2. fj^(ex fj))" unfolding w_def gcd_u_v unfolding u'
  by (metis (no_types, lifting) fm_nonzero gcd_eq_0_iff gcd_u_v nonzero_mult_div_cancel_left u_def)

  have w_power: "w = (\<Prod>fj\<in>P2. fj^(ex fj div p))^p" 
  proof -
    have w: "w = (\<Prod>fj\<in>P2. fj^((ex fj div p)*p))" unfolding w P2_def by auto
    show ?thesis unfolding w by (auto simp add: power_mult prod_power_distrib[symmetric])
  qed

  have z_def: "z = inv_frob_poly w" 
    unfolding p_def w_def u_def fm_def n_def using assms unfolding ERF_step_def
    by (auto simp add: Let_def split: if_splits)

  show "CHAR('e) = 0 \<Longrightarrow> z = 1"
    by (auto simp: z_def p_def w_power)

  have z: "z = (\<Prod>x\<in>P2. x ^(ex x div p))"
    by (cases "p = 0") (auto simp: z_def p_def w_power inv_frob_poly_power')
      
  have zw: "z^CHAR('e) = w" unfolding w_power z p_def[symmetric] by auto

  show "z ^ CHAR('e) dvd f" unfolding zw w 
  by (metis (full_types) dvd_mult_right dvd_normalize_iff dvd_refl fm_P1_P2 fm_def)

  show "z\<noteq>0" by (simp add: fac_set_P1_P2 z)
  
  have prime_factors_z: "\<Prod>(prime_factors z) = \<Prod>P2" unfolding z 
  proof (subst prime_factors_prod)
    show "finite P2" by auto
    show "0 \<notin> (\<lambda>x. x ^ (ex x div p)) ` P2" using fac_set_P1_P2 by force
    have pos: "0 < ex x div p" if "x\<in>P2" for x 
    by (metis (no_types, lifting) P2_def count_prime_factorization_prime dvd_div_eq_0_iff 
        ex_def fac_set_def gr0I in_prime_factors_imp_prime mem_Collect_eq not_in_iff that)
    have "prime_factors (x ^ (ex x div p)) = {x}" if "x\<in>P2" for x 
      unfolding prime_factors_power[OF pos[OF that]] using that by (simp add: prime_prime_factors)
    then have *: "(\<Union>x\<in>P2. prime_factors (x ^ (ex x div p))) = P2" by auto
    show "\<Prod>(\<Union> ((prime_factors \<circ> (\<lambda>x. x ^ (ex x div p))) ` P2)) = \<Prod>P2" 
      unfolding comp_def * by auto
  qed

  show "radical f = v * radical z"
  proof -
    have factors: "prime_factors f = fac_set" unfolding fac_set_def fm_def by auto
    have "\<Prod>(prime_factors f) = \<Prod>P1 * \<Prod>P2" unfolding factors fac_set_P1_P2 
      by (subst prod.union_disjoint, auto)
    also have "\<dots> = v * \<Prod>(prime_factors z)" unfolding v using \<open>z\<noteq>0\<close> prime_factors_z by auto
    finally have "\<Prod>(prime_factors f) = v * \<Prod>(prime_factors z)" by auto
    then show ?thesis  unfolding radical_def using \<open>z\<noteq>0\<close> f_nonzero by auto
  qed

qed

text \<open>If the algorithm stops, then the input was already square-free or zero.\<close>
lemma ERF_step_correct_None:
  assumes "ERF_step f = None"
    shows "degree f = 0 \<or> radical f = normalize f" 
          "f\<noteq>0 \<Longrightarrow> squarefree f" 
proof -
  define p where "p = CHAR('e)"
  define fm' where "fm' = normalize f"
  define u where "u = gcd fm' (pderiv fm')"
  have or: "degree f = 0 \<or> u = 1" using assms unfolding ERF_step_def 
    by (smt (verit, best) option.simps(3) u_def fm'_def)
  have rad: "radical f = normalize f" if "u =1" "degree f\<noteq>0"
  proof -
    interpret perfect_field_poly_factorization "TYPE('e)" f p
    proof (unfold_locales)
      show "p = CHAR('e)" by (rule p_def)
      show "degree f \<noteq> 0" using that(2) by auto
    qed
    have u_def': "u = gcd (normalize f) (pderiv (normalize f))" unfolding u_def fm'_def by auto
    have u': "u = (\<Prod>fj\<in>P1. fj^(ex fj -1)) * (\<Prod>fj\<in>P2. fj^(ex fj))" 
      using u_characterization(2)[OF \<open>degree f \<noteq> 0\<close> u_def'] unfolding fm_def[symmetric] Let_def 
        fac_set_def[symmetric] ex_def[symmetric] p_def[symmetric]
      using P1_def P2_def ex_def by presburger
    have P2_1: "(\<Prod>fj\<in>P2. fj^(ex fj)) = 1"  using u' \<open>u=1\<close>
    by (smt (verit, best) class_cring.finprod_all1 dvd_def dvd_mult2 dvd_prod dvd_refl 
      dvd_triv_right ex_power_not_dvd perfect_field_poly_factorization.P2_def 
      perfect_field_poly_factorization_axioms finites(3) idom_class.unit_imp_dvd mem_Collect_eq) 
    then have "P2 = {}"
    by (smt (verit, ccfv_threshold) Collect_cong Collect_mem_eq UnCI dvd_prodI empty_iff 
      ex_power_not_dvd fac_set_P1_P2 finites(3) idom_class.unit_imp_dvd) 
    moreover have mult: "multiplicity fj fm = 1" if "fj\<in>P1" for fj
    by (metis (no_types, lifting) One_nat_def P1_ex_power_not_dvd Suc_pred 
      P2_1 \<open>u = 1\<close> algebraic_semidom_class.unit_imp_dvd dvd_prod dvd_refl 
      perfect_field_poly_factorization.ex_def perfect_field_poly_factorization_axioms finites(2) 
      gr0I is_unit_power_iff mult_1_right that u') 
    ultimately have "fm = \<Prod>P1" unfolding fm_P1_P2 \<open>(\<Prod>fj\<in>P2. fj ^ ex fj) = 1\<close> unfolding ex_def
      by (subst mult_1_right, intro prod.cong, simp) (auto simp add: mult)
    also have "\<dots> = radical f" 
    by (metis P1_P2_intersect \<open>P2 = {}\<close> f_nonzero fac_set_P1_P2 fac_set_def finites(2) finites(3) 
      fm_def one_neq_zero prime_factorization_1 prime_factorization_normalize prod.union_disjoint 
      radical_1 radical_def set_mset_empty verit_prod_simplify(2))
    finally show ?thesis unfolding fm_def by auto
  qed
  show *: "degree f = 0 \<or> radical f = normalize f" using or rad by auto
  show "squarefree f" if "f \<noteq> 0"
  proof -
    from \<open>f \<noteq> 0\<close> and * have "radical f = normalize f"
      by (metis Missing_Polynomial_Factorial.is_unit_field_poly normalize_1_iff radical_unit)
    thus "squarefree f"
      using \<open>f \<noteq> 0\<close> squarefree_normalize squarefree_radical by metis
  qed
qed

text \<open>The degree of $z$ is less than the degree of $f$. This guarantees the termination of ERF.\<close>

lemma degree_ERF_step_less [termination_simp]:
  assumes "ERF_step f = Some (v, z)"
  shows   "degree z < degree f"
proof -
  define u where "u = gcd f (pderiv (normalize f))"
  define w where "w = u div gcd u (v ^ degree f)"
  from assms have "degree f > 0"
    by (auto split: if_splits simp: Let_def u_def w_def ERF_step_def)

  have "z \<noteq> 0" 
    using assms ERF_step_correct(4) by blast
  have le: "degree z * CHAR('e) \<le> degree f" 
    using divides_degree[OF ERF_step_correct(3)[OF assms]] \<open>degree f > 0\<close>
    unfolding degree_power_eq[OF \<open>z \<noteq> 0\<close>] by auto

  show ?thesis
  proof (cases "CHAR('e) = 0")
    case True
    thus ?thesis
      using ERF_step_correct(5)[OF assms] \<open>degree f > 0\<close> by auto
  next
    case False
    hence "CHAR('e) > 1"
      by (metis CHAR_nonzero less_one nat_neq_iff of_nat_1 of_nat_CHAR zero_neq_one)
    show ?thesis
    proof (cases "degree z = 0")
      case False
      hence "degree z * 1 < degree z * CHAR('e)"
        by (intro mult_less_mono2) (use \<open>CHAR('e) > 1\<close> in auto)
      also have "\<dots> \<le> degree f"
        by (rule le)
      finally show ?thesis
        by simp
    qed (use \<open>degree f > 0\<close> in auto)
  qed
qed

lemma is_measure_degree [measure_function]: "is_measure Polynomial.degree"
  by (rule is_measure_trivial)

text \<open>Finally, we state the full ERF algorithm. We show correctness as well.\<close>
fun ERF ::"'e poly \<Rightarrow> 'e poly list" where
  "ERF f = (
     case ERF_step f of
       None \<Rightarrow> if degree f = 0 then [] else [normalize f]
     | Some (v, z) \<Rightarrow> v # ERF z)"

lemmas [simp del] = ERF.simps


lemma ERF_0 [simp]: "ERF 0 = []"
  by (auto simp add: ERF.simps)

lemma ERF_const [simp]:
  assumes "degree f = 0"
  shows   "ERF f = []"
  by (auto simp add: ERF_step_const[OF assms] assms ERF.simps)

theorem ERF_correct:
  assumes "f \<noteq> 0"
  shows   "prod_list (ERF f) = radical f"
          "g \<in> set (ERF f) \<Longrightarrow> squarefree g"
proof -
  show "prod_list (ERF f) = radical f"
  using assms proof (induction f rule: ERF.induct)
  case (1 f) then show ?case proof (cases "ERF_step f")
      case None
      have "prod_list (ERF f) = (if degree f = 0 then 1 else normalize f)"
        using None by (auto simp: ERF.simps)
      moreover have "radical f = 1" if "degree f = 0" using radical_degree0[OF that \<open>f\<noteq>0\<close>] 
        by simp
      moreover have "radical f = normalize f" if "degree f \<noteq> 0" 
        using ERF_step_correct_None[OF None] that by auto 
      ultimately show ?thesis by auto
    next
      case (Some a)
      obtain v z where vz: "(v,z) = a" by (metis surj_pair)
      then have Some': "ERF_step f = Some (v,z)" using Some by auto
      have "prod_list (ERF f) = v * prod_list(ERF z)" 
        by (auto simp add: Some' ERF.simps)
      also have "\<dots> = v * radical z" 
        by (subst 1)(auto simp add: Some vz[symmetric] ERF_step_correct(4)[OF Some'])
      also have "\<dots> = radical f" using ERF_step_correct(1)[OF Some', symmetric] by auto 
      finally show ?thesis by auto
    qed
  qed

  show "g \<in> set (ERF f) \<Longrightarrow> squarefree g"
  using assms proof (induction f rule: ERF.induct)
  case (1 f) then show ?case proof (cases "ERF_step f")
      case None
      have "set (ERF f) = (if degree f = 0 then {} else {normalize f})"
        using None by (auto simp: ERF.simps)
      moreover have "degree f \<noteq> 0" by (metis "1.prems"(1) calculation emptyE)
      moreover have "squarefree (normalize f)" if "degree f \<noteq> 0" 
        using ERF_step_correct_None(2)[OF None] that squarefree_normalize 
        "1"(3) by blast 
      ultimately show ?thesis using 1 by auto
    next
      case (Some a)
      obtain v z where vz: "(v,z) = a" by (metis surj_pair)
      then have Some': "ERF_step f = Some (v,z)" using Some by auto
      have "set (ERF f) = {v} \<union>  set (ERF z)" 
        by (auto simp add: Some' ERF.simps)
      moreover have "squarefree g" if "g\<in>{v}" using ERF_step_correct(2)[OF Some'] 
        that by auto
      moreover have "squarefree g" if "g\<in>set (ERF z)"
        using 1 ERF_step_correct(4)[OF Some'] that Some' by blast
      ultimately show ?thesis using 1(2) by blast
    qed
  qed
qed

text \<open>
  It is also easy to see that any two polynomials in the list returned
  by @{const ERF} are coprime.
\<close>
lemma ERF_pairwise_coprime: "sorted_wrt coprime (ERF p)" 
proof (cases "p = 0")
  case [simp]: False
  show ?thesis
    unfolding sorted_wrt_iff_nth_less
  proof safe
    fix i j :: nat
    assume ij: "i < j" "j < length (ERF p)"
    have "(\<Prod>k\<in>{i,j}. ERF p ! k) dvd (\<Prod>k<length (ERF p). ERF p ! k)"
      by (rule prod_dvd_prod_subset) (use ij in auto)
    also have "\<dots> = prod_list (ERF p)"
      by (simp add: prod_list_prod_nth atLeast0LessThan)
    also have "\<dots> = radical p"
      by (simp add: ERF_correct)
    finally have "ERF p ! i * ERF p ! j dvd radical p"
      using ij by simp
    hence "squarefree (ERF p ! i * ERF p ! j)"
      using False squarefree_mono by blast
    thus "coprime (ERF p ! i) (ERF p ! j)"
      by blast
  qed
qed auto
  

text \<open>
  We can also compute the radical of a polynomial with the ERF algorithm by simply
  multiplying together the individual parts we found.
\<close>
lemma radical_code [code_unfold]: "radical f = (if f = 0 then 0 else prod_list (ERF f))"
  using ERF_correct(1)[of f] by simp

text \<open>
  With this, the ERF algorithm can also serve as an executable test for the square-freeness
  of a polynomial (especially over a finite field):
\<close>
lemma squarefree_poly_code [code_unfold]:
  fixes p :: "'a :: field_gcd poly"
  shows "squarefree p \<longleftrightarrow> p \<noteq> 0 \<and> Polynomial.degree p = Polynomial.degree (radical p)"
proof
  assume *: "p \<noteq> 0 \<and> Polynomial.degree p = Polynomial.degree (radical p)"
  have "p dvd radical p"
    by (rule dvd_euclidean_size_eq_imp_dvd) (use * in \<open>auto simp: euclidean_size_poly_def\<close>)
  thus "squarefree p"
    using * squarefree_mono squarefree_radical by blast
next
  assume "squarefree p"
  have "Polynomial.degree (radical p) = Polynomial.degree (normalize (radical p))"
    by auto
  also have "normalize (radical p) = normalize p"
    using \<open>squarefree p\<close> radical_of_squarefree by blast
  finally show "p \<noteq> 0 \<and> Polynomial.degree p = Polynomial.degree (radical p)"
    using \<open>squarefree p\<close> by auto
qed  

end

end