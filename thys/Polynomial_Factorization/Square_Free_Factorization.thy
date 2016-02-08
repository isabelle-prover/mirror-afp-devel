(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Square Free Factorization\<close>

text \<open>We implemented Yun's algorithm to perform a square-free factorization of a polynomial.
We further show properties of a square-free factorization, namely that the exponents in
the square-free factorization are exactly the orders of the roots. We also show that 
factorizing the result of square-free factorization further will again result in a 
square-free factorization.\<close>

theory Square_Free_Factorization
imports 
  "../Matrix/Utility"
  Polynomial_Divisibility
  Order_Polynomial
begin

hide_const Coset.order

context
  fixes ty :: "'a :: field itself"
begin

definition square_free :: "'a poly \<Rightarrow> bool" where 
  "square_free p = (p \<noteq> 0 \<longrightarrow> (\<forall> q. degree q \<noteq> 0 \<longrightarrow> \<not> (q * q dvd p)))"

lemma square_freeI:  
  assumes "\<And> q. degree q \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> q * q dvd p \<Longrightarrow> False"
  shows "square_free p" unfolding square_free_def
proof (intro allI impI notI)
  fix q
  assume dq: "degree q \<noteq> 0" and dvd: "q * q dvd p"
  from assms[OF dq _ dvd] dq show False by (cases "q = 0", auto)
qed

definition square_free_factorization :: "'a poly \<Rightarrow> 'a \<times> ('a poly \<times> nat) list \<Rightarrow> bool" where
  "square_free_factorization p cbs \<equiv> case cbs of (c,bs) \<Rightarrow>
    (p = smult c (\<Prod>(a, i)\<in> set bs. a ^ Suc i))
  \<and> (p = 0 \<longrightarrow> c = 0 \<and> bs = [])
  \<and> (\<forall> a i. (a,i) \<in> set bs \<longrightarrow> square_free a \<and> degree a \<noteq> 0)
  \<and> (\<forall> a i b j. (a,i) \<in> set bs \<longrightarrow> (b,j) \<in> set bs \<longrightarrow> (a,i) \<noteq> (b,j) \<longrightarrow> gcd a b = 1)
  \<and> distinct bs"

lemma square_free_factorizationD: assumes "square_free_factorization p (c,bs)"
  shows "p = smult c (\<Prod>(a, i)\<in> set bs. a ^ Suc i)"
  "(a,i) \<in> set bs \<Longrightarrow> square_free a \<and> degree a \<noteq> 0"
  "(a,i) \<in> set bs \<Longrightarrow> (b,j) \<in> set bs \<Longrightarrow> (a,i) \<noteq> (b,j) \<Longrightarrow> gcd a b = 1"
  "p = 0 \<Longrightarrow> c = 0 \<and> bs = []"
  "distinct bs"
  using assms unfolding square_free_factorization_def split by blast+

lemma irreducible_dvd_pow: fixes p :: "'a poly" 
  assumes irr: "irreducible p"
  shows "p dvd q ^ Suc n \<Longrightarrow> p dvd q"
proof (induct n)
  case (Suc n)
  have "q ^ Suc (Suc n) = q * q ^ Suc n" by simp
  from irreducible_dvd_mult[OF irr Suc(2)[unfolded this]] Suc(1)
  show ?case by auto
qed simp

lemma irreducible_dvd_setprod: fixes p :: "'a poly"
  assumes irr: "irreducible p"
  and dvd: "p dvd setprod f as"
  shows "\<exists> a \<in> as. p dvd f a"
proof -
  from irr[unfolded irreducible_def] have deg: "degree p \<noteq> 0" by auto
  hence p1: "\<not> p dvd 1" unfolding dvd_def
    by (metis degree_1 div_mult_self1_is_id div_poly_less linorder_neqE_nat mult_not_zero not_less0 zero_neq_one)
  from dvd show ?thesis
  proof (induct as rule: infinite_finite_induct)
    case (insert a as)
    hence "setprod f (insert a as) = f a * setprod f as" by auto
    from irreducible_dvd_mult[OF irr insert(4)[unfolded this]]
    show ?case using insert(3) by auto
  qed (insert p1, auto)
qed

lemma dvd_mult: fixes p :: "'a poly" 
  assumes "p dvd q * r"
  and "degree p \<noteq> 0" 
shows "\<exists> s t. irreducible s \<and> p = s * t \<and> (s dvd q \<or> s dvd r)"
proof -
  from irreducible_factor[OF assms(2)] obtain s t
  where irred: "irreducible s" and p: "p = s * t" by auto
  from `p dvd q * r` p have s: "s dvd q * r" unfolding dvd_def by auto
  from irreducible_dvd_mult[OF irred s] p irred show ?thesis by auto
qed  


lemma poly_gcd_monic_factor: fixes p :: "'a poly"
  assumes "monic p"
  shows "gcd (p * q) (p * r) = p * gcd q r"
proof (rule poly_gcd_unique[OF _ _ dvd_gcd_mult])
  show "p * gcd q r dvd p * q" by simp
  show "p * gcd q r dvd p * r" by simp
  have p: "p \<noteq> 0" using assms by auto
  let ?r = "(if p * q = 0 \<and> p * r = 0 then 0 else (1 :: 'a))"
  let ?l = "coeff (p * gcd q r) (degree (p * gcd q r))"
  show "?l = ?r"
  proof (cases "q = 0 \<and> r = 0")
    case False
    hence "?r = 1" using p by auto
    from p assms have "?l = 1" by (simp add: False monic_mult poly_gcd_monic)
    thus ?thesis unfolding `?r = 1` by simp
  qed auto
qed
end

subsection \<open>Yun's factorization algorithm\<close>
context 
  fixes type :: "'a :: field_char_0 poly itself"
  and Gcd :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
begin

partial_function (tailrec) yun_factorization_main :: 
  "'a poly \<Rightarrow> 'a poly \<Rightarrow>
    nat \<Rightarrow> ('a poly \<times> nat)list \<Rightarrow> ('a poly \<times> nat)list" where
  [code]: "yun_factorization_main bn cn i sqr = (
    if bn = 1 then sqr
    else (
    let 
      dn = cn - pderiv bn;
      an = Gcd bn dn
    in yun_factorization_main (bn div an) (dn div an) (Suc i) ((an,i) # sqr)))"

definition square_free_monic_poly :: "'a poly \<Rightarrow> 'a poly" where
  "square_free_monic_poly p = (p div (Gcd p (pderiv p)))"

definition square_free_poly :: "'a poly \<Rightarrow> 'a poly" where
  "square_free_poly p = (if p = 0 then 0 else 
     square_free_monic_poly (smult (inverse (coeff p (degree p))) p))"

definition yun_monic_factorization :: "'a poly \<Rightarrow> ('a poly \<times> nat)list" where
  "yun_monic_factorization p = (let
    pp = pderiv p;
    u = Gcd p pp;
    b0 = p div u;
    c0 = pp div u
    in 
      (filter (\<lambda> (a,i). a \<noteq> 1) (yun_factorization_main b0 c0 0 [])))"

definition yun_factorization :: "'a poly \<Rightarrow> 'a \<times> ('a poly \<times> nat)list" where
  "yun_factorization p = (if p = 0
    then (0,[]) else (let 
      c = coeff p (degree p);
      q = smult (inverse c) p
    in (c, yun_monic_factorization q)))"

context
  assumes Gcd: "Gcd = gcd"
begin

context
  fixes as :: "('a poly \<times> nat) set"
  and p :: "'a poly"
  assumes p: "p = setprod (\<lambda> (a,i). a ^ Suc i) as"
  and fin: "finite as"
begin
lemma poly_exp_expand: 
  "p = (setprod (\<lambda> (a,i). a ^ i) as) * setprod (\<lambda> (a,i). a) as"
  unfolding p setprod.distrib[symmetric]
  by (rule setprod.cong, auto)

lemma pderiv_exp_setprod: 
  "pderiv p = (setprod (\<lambda> (a,i). a ^ i) as * setsum (\<lambda> (a,i). 
    setprod (\<lambda> (b,j). b) (as - {(a,i)}) * smult (of_nat (Suc i)) (pderiv a)) as)"
  unfolding p pderiv_setprod setsum_right_distrib
proof (rule setsum.cong[OF refl])
  fix x
  assume "x \<in> as"
  then obtain a i where x: "x = (a,i)" and mem: "(a,i) \<in> as" by (cases x, auto)
  let ?si = "smult (of_nat (Suc i)) :: 'a poly \<Rightarrow> 'a poly"
  show "(\<Prod>(a, i)\<in>as - {x}. a ^ Suc i) * pderiv (case x of (a, i) \<Rightarrow> a ^ Suc i) =
         (\<Prod>(a, i)\<in>as. a ^ i) *
         (case x of (a, i) \<Rightarrow> (\<Prod>(a, i)\<in>as - {(a, i)}. a) * smult (of_nat (Suc i)) (pderiv a))"
    unfolding x split pderiv_power_Suc
  proof -
    let ?prod = "\<Prod>(a, i)\<in>as - {(a, i)}. a ^ Suc i"
    let ?l = "?prod * (?si (a ^ i) * pderiv a)"
    let ?r = "(\<Prod>(a, i)\<in>as. a ^ i) * ((\<Prod>(a, i)\<in>as - {(a, i)}. a) * ?si (pderiv a))"
    have "?r = a ^ i * ((\<Prod>(a, i)\<in>as - {(a, i)}. a ^ i) * (\<Prod>(a, i)\<in>as - {(a, i)}. a) * ?si (pderiv a))"
      unfolding setprod.remove[OF fin mem] by (simp add: ac_simps)
    also have "(\<Prod>(a, i)\<in>as - {(a, i)}. a ^ i) * (\<Prod>(a, i)\<in>as - {(a, i)}. a) 
      = ?prod" unfolding setprod.distrib[symmetric]
      by (rule setprod.cong[OF refl], auto)
    finally show "?l = ?r"
      by (simp add: ac_simps)
  qed
qed

context
  assumes as_distinct: "\<And> a i b j. (a,i) \<in> as \<Longrightarrow> (b,j) \<in> as \<Longrightarrow> (a,i) \<noteq> (b,j) \<Longrightarrow> a \<noteq> b"
  and as_irred: "\<And> a i. (a,i) \<in> as \<Longrightarrow> irreducible a"
  and as_monic: "\<And> a i. (a,i) \<in> as \<Longrightarrow> monic a"
begin

private lemma monic_gen: assumes "bs \<subseteq> as"
  shows "monic (\<Prod> (a, i) \<in> bs. a)"
  by (rule monic_setprod, insert assms as_monic, auto)

private lemma nonzero_gen: assumes "bs \<subseteq> as"
  shows "(\<Prod> (a, i) \<in> bs. a) \<noteq> 0"
  using monic_gen[OF assms] by auto

private lemma monic_prod: "monic ((\<Prod>(a, i)\<in>as. a ^ i))"
  by (rule monic_setprod, insert as_monic, auto intro: monic_power)

private lemma coprime_generic: assumes bs: "bs \<subseteq> as"
  and f: "\<And> a i. (a,i) \<in> bs \<Longrightarrow> f i > 0"
  shows "coprime (\<Prod>(a, i) \<in> bs. a)
     (\<Sum>(a, i)\<in> bs. (\<Prod>(b, j)\<in> bs - {(a, i)} . b) * smult (of_nat (f i)) (pderiv a))"
  (is "coprime ?single ?onederiv")
proof -
  have single: "?single \<noteq> 0" by (rule nonzero_gen[OF bs])
  show ?thesis
  proof (rule poly_gcd_unique)
    fix k
    assume dvd: "k dvd ?single" "k dvd ?onederiv"
    note bs_monic = as_monic[OF set_mp[OF bs]]
    from dvd(1) single have k: "k \<noteq> 0" by auto
    show "k dvd 1"
    proof (cases "degree k = 0")
      case True
      with k obtain c where kc: "k = [: c :]" by (metis degree_0_id)
      with k have "c \<noteq> 0" by auto
      thus "k dvd 1" unfolding dvd_def kc
        by (intro exI[of _ "[: 1/c :]"], auto simp: one_poly_def)
    next
      case False
      from irreducible_factor[OF this]
      obtain p q where k: "k = p * q" and p: "irreducible p" by auto
      from k dvd have dvd: "p dvd ?single" "p dvd ?onederiv" unfolding dvd_def by auto
      from irreducible_dvd_setprod[OF p dvd(1)] obtain a i where ai: "(a,i) \<in> bs" and pa: "p dvd a"
        by force
      then obtain q where a: "a = p * q" unfolding dvd_def by auto
      from p[unfolded irreducible_def] have p0: "degree p \<noteq> 0" by auto
      from irreducible_dvd_smult[OF p0 as_irred pa] ai bs
        obtain c where c: "c \<noteq> 0" and ap: "a = smult c p" by auto
      hence ap': "p = smult (1/c) a" by auto
      let ?setprod = "\<lambda> a i. (\<Prod>(b, j)\<in>bs - {(a, i)}. b) * smult (of_nat (f i)) (pderiv a)"
      let ?setprod' = "\<lambda> aa ii a i. (\<Prod>(b, j)\<in>bs - {(a, i),(aa,ii)}. b) * smult (of_nat (f i)) (pderiv a)"
      def factor \<equiv> "setsum (\<lambda> (b,j). ?setprod' a i b j ) (bs - {(a,i)})"
      def fac \<equiv> "q * factor"
      from fin finite_subset[OF bs] have fin: "finite bs" by auto
      have "?onederiv = ?setprod a i + setsum (\<lambda> (b,j). ?setprod b j) (bs - {(a,i)})"
        by (subst setsum.remove[OF fin ai], auto)
      also have "setsum (\<lambda> (b,j). ?setprod b j) (bs - {(a,i)})
        = a * factor"
        unfolding factor_def setsum_right_distrib
      proof (rule setsum.cong[OF refl])
        fix bj
        assume mem: "bj \<in> bs - {(a,i)}"
        obtain b j where bj: "bj = (b,j)" by force
        from mem bj ai have ai: "(a,i) \<in> bs - {(b,j)}" by auto
        have id: "bs - {(b, j)} - {(a, i)} = bs - {(b,j),(a,i)}" by auto
        show "(\<lambda> (b,j). ?setprod b j) bj = a * (\<lambda> (b,j). ?setprod' a i b j) bj"
          unfolding bj split
          by (subst setprod.remove[OF _ ai], insert fin, auto simp: id ac_simps)
      qed
      finally have "?onederiv = ?setprod a i + p * fac" unfolding fac_def a by simp
      from dvd(2)[unfolded this] have "p dvd ?setprod a i" by algebra
      from irreducible_dvd_mult[OF p this]
      have False
      proof
        assume "p dvd (\<Prod>(b, j)\<in>bs - {(a, i)}. b)" 
        from irreducible_dvd_setprod[OF p this] obtain b j where bj': "(b,j) \<in> bs - {(a,i)}"
          and pb: "p dvd b" by auto
        hence bj: "(b,j) \<in> bs" by auto
        from as_irred bj bs have "irreducible b" by auto
        from irreducible_dvd_smult[OF p0 this pb] obtain d where d: "d \<noteq> 0" 
          and b: "b = smult d p" by auto
        with ap c have id: "smult (c/d) b = a" and deg: "degree a = degree b" by auto
        from coeff_smult[of "c/d" b "degree b", unfolded id] deg bs_monic[OF ai] bs_monic[OF bj]
        have "c / d = 1" by simp
        from id[unfolded this] have "a = b" by simp
        with as_distinct[OF set_mp[OF bs ai] set_mp[OF bs bj]] bj'
        show False by auto
      next
        from f[OF ai] obtain k where fi: "f i = Suc k" by (cases "f i", auto)
        assume "p dvd smult (of_nat (f i)) (pderiv a)"
        hence "p dvd (pderiv a)" unfolding fi using dvd_smult_cancel of_nat_eq_0_iff by blast
        from this[unfolded ap] have "p dvd pderiv p" using c
          by (metis `p dvd pderiv a` ap' dvd_trans dvd_triv_right mult.left_neutral pderiv_smult smult_dvd_cancel)
        with not_dvd_pderiv[OF p0] show False by auto
      qed
      thus "k dvd 1" by simp
    qed
  qed (insert `?single \<noteq> 0`, auto)
qed

private lemma pderiv_exp_gcd: 
  "gcd p (pderiv p) = (\<Prod>(a, i)\<in>as. a ^ i)" (is "_ = ?prod")
proof -
  let ?sum = "(\<Sum>(a, i)\<in>as. (\<Prod>(b, j)\<in>as - {(a, i)}. b) * smult (of_nat (Suc i)) (pderiv a))"
  let ?single = "(\<Prod>(a, i)\<in>as. a)"
  let ?setprod = "\<lambda> a i. (\<Prod>(b, j)\<in>as - {(a, i)}. b) * smult (of_nat (Suc i)) (pderiv a)"
  let ?onederiv = "\<Sum>(a, i)\<in>as. ?setprod a i"
  have pp: "pderiv p = ?prod * ?sum" by (rule pderiv_exp_setprod)
  have p: "p = ?prod * ?single" by (rule poly_exp_expand)
  have monic: "monic ?prod" by (rule monic_prod)
  have gcd: "gcd ?single ?onederiv = 1" 
    by (rule coprime_generic, auto)
  show ?thesis unfolding pp unfolding p unfolding poly_gcd_monic_factor[OF monic] gcd by simp
qed

private lemma p_div_gcd_p_pderiv: "p div (gcd p (pderiv p)) = (\<Prod>(a, i)\<in>as. a)"
  unfolding pderiv_exp_gcd unfolding poly_exp_expand
  by (rule div_mult_self1_is_id, insert monic_prod, auto)

private fun A B C D :: "nat \<Rightarrow> 'a poly" where
  "A n = gcd (B n) (D n)"
| "B 0 = p div (gcd p (pderiv p))"
| "B (Suc n) = B n div A n"
| "C 0 = pderiv p div (gcd p (pderiv p))"
| "C (Suc n) = D n div A n"
| "D n = C n - pderiv (B n)"

private lemma A_B_C_D: "A n = (\<Prod> (a, i) \<in> as \<inter> UNIV \<times> {n}. a)"
  "B n = (\<Prod> (a, i) \<in> as - UNIV \<times> {0 ..< n}. a)"
  "C n = (\<Sum>(a, i)\<in>as - UNIV \<times> {0 ..< n}. 
    (\<Prod>(b, j)\<in>as - UNIV \<times> {0 ..< n} - {(a, i)}. b) * smult (of_nat (Suc i - n)) (pderiv a))"
  "D n = (\<Prod> (a, i) \<in> as \<inter> UNIV \<times> {n}. a) * 
    (\<Sum> (a,i)\<in>as - UNIV \<times> {0 ..< Suc n}. 
      (\<Prod>(b, j)\<in> as - UNIV \<times> {0 ..< Suc n} - {(a, i)}. b) * (smult (of_nat (i - n)) (pderiv a)))"
proof (induct n and n and n and n rule: A_B_C_D.induct)
  case (1 n) (* A *)
  note Bn = 1(1)
  note Dn = 1(2)
  have "(\<Prod>(a, i)\<in>as - UNIV \<times> {0..< n}. a) = (\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a) * (\<Prod>(a, i)\<in>as - UNIV \<times> {0..<Suc n}. a)"
    by (subst setprod.union_disjoint[symmetric], auto, insert fin, auto intro: setprod.cong)
  note Bn' = Bn[unfolded this]
  let ?an = "(\<Prod> (a, i) \<in> as \<inter> UNIV \<times> {n}. a)"
  let ?bn = "(\<Prod>(a, i)\<in>as - UNIV \<times> {0..<Suc n}. a)"
  show "A n = ?an" unfolding A.simps
  proof (rule poly_gcd_unique)
    have monB1: "monic (B n)" unfolding Bn by (rule monic_gen, auto)
    hence "B n \<noteq> 0" by auto
    let ?dn = "(\<Sum> (a,i)\<in>as - UNIV \<times> {0 ..< Suc n}. 
        (\<Prod>(b, j)\<in> as - UNIV \<times> {0 ..< Suc n} - {(a, i)}. b) * (smult (of_nat (i - n)) (pderiv a)))"
    have Dn: "D n = ?an * ?dn" unfolding Dn by auto
    show dvd1: "?an dvd B n" unfolding Bn' dvd_def by blast
    show dvd2: "?an dvd D n" unfolding Dn dvd_def by blast
    {
      fix k
      assume "k dvd B n" "k dvd D n"
      from dvd_gcd_mult[OF this[unfolded Bn' Dn]]
      have "k dvd ?an * (gcd ?bn ?dn)" .
      also have "gcd ?bn ?dn = 1"
        by (rule coprime_generic, auto)
      finally show "k dvd ?an" by simp
    }
    have mon: "monic ?an"
      by (rule monic_gen, auto)
    show "coeff ?an (degree ?an) = (if B n = 0 \<and> D n = 0 then 0 else 1)" 
      unfolding mon using `B n \<noteq> 0` by auto
  qed
next
  case 2 (* B 0 *)
  have as: "as - UNIV \<times> {0..<0} = as" by auto
  show ?case unfolding B.simps as p_div_gcd_p_pderiv by auto
next
  case (3 n) (* B n *)
  have id: "(\<Prod>(a, i)\<in>as - UNIV \<times> {0..< n}. a) = (\<Prod>(a, i)\<in>as - UNIV \<times> {0..<Suc n}. a) * (\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a)"
    by (subst setprod.union_disjoint[symmetric], auto, insert fin, auto intro: setprod.cong)
  show ?case unfolding B.simps 3 id
    by (subst div_mult_self2_is_id[OF nonzero_gen], auto)
next
  case 4 (* C 0 *)
  have as: "as - UNIV \<times> {0..<0} = as" "\<And> i. Suc i - 0 = Suc i" by auto
  show ?case unfolding C.simps pderiv_exp_gcd unfolding pderiv_exp_setprod as
    by (rule div_mult_self1_is_id, insert monic_prod, auto)
next
  case (5 n) (* C n *)
  show ?case unfolding C.simps 5
    by (subst div_mult_self1_is_id, rule nonzero_gen, auto)
next
  case (6 n) (* D n *)
  let ?f = "\<lambda> (a,i). (\<Prod>(b, j)\<in>as - UNIV \<times> {0 ..< n} - {(a, i)}. b) * (smult (of_nat (i - n)) (pderiv a))"
  have "D n = (\<Sum> (a,i)\<in>as - UNIV \<times> {0 ..< n}. (\<Prod>(b, j)\<in>as - UNIV \<times> {0 ..< n} - {(a, i)}. b) * 
    (smult (of_nat (Suc i - n)) (pderiv a) - pderiv a))"
    unfolding D.simps 6 pderiv_setprod setsum_subtractf[symmetric] right_diff_distrib
    by (rule setsum.cong, auto)
  also have "\<dots> = setsum ?f (as - UNIV \<times> {0 ..< n})"
  proof (rule setsum.cong[OF refl])
    fix x
    assume "x \<in> as - UNIV \<times> {0 ..< n}"
    then obtain a i where x: "x = (a,i)" and i: "Suc i > n" by (cases x, auto)
    hence id: "Suc i - n = Suc (i - n)" by arith
    have id: "of_nat (Suc i - n) = of_nat (i - n) + (1 :: 'a)" unfolding id by simp
    have id: "smult (of_nat (Suc i - n)) (pderiv a) - pderiv a = smult (of_nat (i - n)) (pderiv a)" 
      unfolding id smult_add_left by auto
    have cong: "\<And> x y z :: 'a poly. x = y \<Longrightarrow> x * z = y * z" by auto
    show "(case x of
          (a, i) \<Rightarrow>
            (\<Prod>(b, j)\<in>as - UNIV \<times> {0..<n} - {(a, i)}. b) *
            (smult (of_nat (Suc i - n)) (pderiv a) - pderiv a)) =
         (case x of
          (a, i) \<Rightarrow> (\<Prod>(b, j)\<in>as - UNIV \<times> {0..<n} - {(a, i)}. b) * smult (of_nat (i - n)) (pderiv a))"
      unfolding x split id
      by (rule cong, auto)
  qed
  also have "\<dots> = setsum ?f (as - UNIV \<times> {0 ..< Suc n}) + setsum ?f (as \<inter> UNIV \<times> {n})"
    by (subst setsum.union_disjoint[symmetric], insert fin, auto intro: setsum.cong)
  also have "setsum ?f (as \<inter> UNIV \<times> {n}) = 0"
    by (rule setsum.neutral, auto)
  finally have id: "D n = setsum ?f (as - UNIV \<times> {0 ..< Suc n})" by simp
  show ?case unfolding id setsum_right_distrib
  proof (rule setsum.cong[OF refl])
    fix x
    assume mem: "x \<in> as - UNIV \<times> {0 ..< Suc n}"
    obtain a i where x: "x = (a,i)" by force
    with mem have i: "i > n" by auto
    have cong: "\<And> x y z v :: 'a poly. x = y * v \<Longrightarrow> x * z = y * (v * z)" by auto
    show "(case x of
          (a, i) \<Rightarrow> (\<Prod>(b, j)\<in>as - UNIV \<times> {0..<n} - {(a, i)}. b) * smult (of_nat (i - n)) (pderiv a)) =
         (\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a) *
         (case x of (a, i) \<Rightarrow>
            (\<Prod>(b, j)\<in>as - UNIV \<times> {0..<Suc n} - {(a, i)}. b) * smult (of_nat (i - n)) (pderiv a))"
      unfolding x split
      by (rule cong, subst setprod.union_disjoint[symmetric], insert fin, (auto)[3],
        rule setprod.cong, insert i, auto) 
  qed
qed

private lemmas A = A_B_C_D(1)
private lemmas B = A_B_C_D(2)

private lemmas ABCD_simps = A.simps B.simps C.simps D.simps
declare ABCD_simps[simp del]

private lemma setprod_A: 
  "(\<Prod>i = 0..< n. A i ^ Suc i) = (\<Prod>(a, i)\<in> as \<inter> UNIV \<times> {0 ..< n}. a ^ Suc i)"
proof (induct n)
  case (Suc n)
  have id: "{0 ..< Suc n} = insert n {0 ..< n}" by auto
  have id2: "as \<inter> UNIV \<times> {0 ..< Suc n} = as \<inter> UNIV \<times> {n} \<union> as \<inter> UNIV \<times> {0 ..< n}" by auto
  have cong: "\<And> x y z. x = y \<Longrightarrow> x * z = y * z" by auto
  show ?case unfolding id2 unfolding id 
  proof (subst setprod.insert; (subst setprod.union_disjoint)?; (unfold Suc)?; 
    (unfold A, rule cong)?)
    show "(\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a) ^ Suc n = (\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {n}. a ^ Suc i)"
      unfolding setprod_power_distrib
      by (rule setprod.cong, auto)
  qed (insert fin, auto)
qed simp

private lemma setprod_A_is_p_unknown: assumes "\<And> a i. (a,i) \<in> as \<Longrightarrow> i < n"
  shows "p = (\<Prod>i = 0..< n. A i ^ Suc i)"
proof -
  have "p = (\<Prod>(a, i)\<in>as. a ^ Suc i)" by (rule p)
  also have "\<dots> = (\<Prod>i = 0..< n. A i ^ Suc i)" unfolding setprod_A
    by (rule setprod.cong, insert assms, auto)
  finally show ?thesis .
qed

private definition bound :: nat where
  "bound = Suc (Max (snd ` as))"

private lemma bound: assumes m: "m \<ge> bound"
  shows "B m = 1"
proof -
  let ?set = "as - UNIV \<times> {0..<m}"
  {
    fix a i
    assume ai: "(a,i) \<in> ?set"
    hence "i \<in> snd ` as" by force
    from Max_ge[OF _ this] fin have "i \<le> Max (snd ` as)" by auto
    with ai m[unfolded bound_def] have False by auto
  }
  hence id: "?set = {}" by force
  show "B m = 1" unfolding B id by simp
qed

lemma gcd_A_A: assumes "i \<noteq> j"
  shows "gcd (A i) (A j) = 1"
proof (rule poly_gcd_unique)
  fix k  
  assume dvd: "k dvd A i" "k dvd A j"
  have Ai: "A i \<noteq> 0" unfolding A
    by (rule nonzero_gen, auto)
  with dvd have k: "k \<noteq> 0" by auto
  show "k dvd 1"
  proof (cases "degree k = 0")
    case True
    then obtain c where kc: "k = [: c :]" by (metis degree_0_id)
    with k have "1 = k * [: 1/c :]" by (simp add: one_poly_def)
    thus ?thesis unfolding dvd_def by blast
  next
    case False
    from irreducible_monic_factor[OF this]
    obtain q r where k: "k = q * r" and q: "irreducible q" and mq: "monic q" by auto
    with dvd have dvd: "q dvd A i" "q dvd A j" unfolding dvd_def by auto
    from q have q0: "degree q \<noteq> 0" unfolding irreducible_def by auto
    from irreducible_dvd_setprod[OF q dvd(1)[unfolded A]]
      obtain a where ai: "(a,i) \<in> as" and qa: "q dvd a" by auto
    from irreducible_dvd_setprod[OF q dvd(2)[unfolded A]]
      obtain b where bj: "(b,j) \<in> as" and qb: "q dvd b" by auto
    from as_distinct[OF ai bj] assms have neq: "a \<noteq> b" by auto
    from irreducible_dvd_smult[OF q0 as_irred[OF ai] qa]
      irreducible_dvd_smult[OF q0 as_irred[OF bj] qb]
    obtain c d where "c \<noteq> 0" "d \<noteq> 0" "a = smult c q" "b = smult d q" by auto
    hence ab: "a = smult (c / d) b" and "c / d \<noteq> 0" by auto
    with as_monic[OF bj] as_monic[OF ai] arg_cong[OF ab, of "\<lambda> p. coeff p (degree p)"] 
    have "a = b" unfolding coeff_smult degree_smult_eq by auto
    with neq show ?thesis by auto
  qed
qed (auto simp: nonzero_gen A)

lemma A_monic: "monic (A i)"
  unfolding A by (rule monic_gen, auto)

lemma A_square_free: "square_free (A i)"
proof (rule square_freeI)
  fix q k
  have mon: "monic (A i)" by (rule A_monic)
  hence Ai: "A i \<noteq> 0" by auto
  assume q: "degree q \<noteq> 0" and dvd: "q * q dvd A i"
  from irreducible_monic_factor[OF q] obtain r s where q: "q = r * s" and 
    irr: "irreducible r" and mr: "monic r" by auto
  from dvd[unfolded q] have dvd2: "r * r dvd A i" and dvd1: "r dvd A i" unfolding dvd_def by auto
  from irreducible_dvd_setprod[OF irr dvd1[unfolded A]] 
    obtain a where ai: "(a,i) \<in> as" and ra: "r dvd a" by auto
  let ?rem = "(\<Prod>(a, i)\<in>as \<inter> UNIV \<times> {i} - {(a,i)}. a)"
  have a: "irreducible a" by (rule as_irred[OF ai])
  from irreducible_dvd_smult[OF _ a ra] irr[unfolded irreducible_def] 
    obtain c where ar: "a = smult c r"  and "c \<noteq> 0" by auto
  with mr as_monic[OF ai] arg_cong[OF ar, of "\<lambda> p. coeff p (degree p)"] 
  have "a = r" unfolding coeff_smult degree_smult_eq by auto 
  with dvd2 have dvd: "a * a dvd A i" by simp
  have id: "A i = a * ?rem" unfolding A
    by (subst setprod.remove[of _ "(a,i)"], insert ai fin, auto)
  with dvd have "a dvd ?rem" using a id Ai by auto
  from irreducible_dvd_setprod[OF a this] obtain b where bi: "(b,i) \<in> as" 
    and neq: "b \<noteq> a" and ab: "a dvd b" by auto
  from as_irred[OF bi] have b: "irreducible b" . 
  from irreducible_dvd_smult[OF _ b ab] a[unfolded irreducible_def]
  obtain c where "c \<noteq> 0" and ba: "b = smult c a" by auto
  with as_monic[OF bi] as_monic[OF ai] arg_cong[OF ba, of "\<lambda> p. coeff p (degree p)"] 
  have "a = b" unfolding coeff_smult degree_smult_eq by auto
  with neq show False by auto
qed


private lemma setprod_A_is_p_B_bound: assumes "B n = 1"
  shows "p = (\<Prod>i = 0..< n. A i ^ Suc i)"
proof (rule setprod_A_is_p_unknown)
  fix a i
  assume ai: "(a,i) \<in> as"
  let ?rem = "(\<Prod>(a, i)\<in>as - UNIV \<times> {0..<n} - {(a,i)}. a)"
  have rem: "?rem \<noteq> 0"
    by (rule nonzero_gen, auto)
  have "irreducible a" using as_irred[OF ai] .
  hence a: "a \<noteq> 0" "degree a \<noteq> 0" unfolding irreducible_def by auto
  show "i < n"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "i \<ge> n" by auto
    with ai have mem: "(a,i) \<in> as - UNIV \<times> {0 ..< n}" by auto
    have "0 = degree (\<Prod>(a, i)\<in>as - UNIV \<times> {0..<n}. a)" using assms unfolding B by simp
    also have "\<dots> = degree (a * ?rem)"
      by (subst setprod.remove[OF _ mem], insert fin, auto)
    also have "\<dots> = degree a + degree ?rem"
      by (rule degree_mult_eq[OF a(1) rem])
    finally show False using a(2) by auto
  qed
qed

lemma square_free_monic_poly_context: "(poly (square_free_monic_poly p) x = 0) = (poly p x = 0)"
proof -
  show ?thesis unfolding square_free_monic_poly_def unfolding Gcd p_div_gcd_p_pderiv
    unfolding p poly_setprod setprod_zero_iff[OF fin] by force
qed

lemma yun_factorization_main: assumes "yun_factorization_main (B n) (C n) n bs = cs"
  "set bs = {(A i, i) | i. i < n}" "distinct (map snd bs)"
  shows "\<exists> m. set cs = {(A i, i) | i. i < m} \<and> B m = 1 \<and> distinct (map snd cs)"
proof -
  let ?meas = "\<lambda> n. bound - n"
  show ?thesis using assms 
  proof (induct n arbitrary: bs rule: wf_induct[OF wf_measure[of ?meas]])
    case (1 n)
    note IH = 1(1)[rule_format]
    have res: "yun_factorization_main (B n) (C n) n bs = cs" by fact
    note res = res[unfolded yun_factorization_main.simps[of "B n"]]
    have bs: "set bs = {(A i, i) |i. i < n}" "distinct (map snd bs)" by fact+
    show ?case
    proof (cases "B n = 1")
      case True
      with res have "bs = cs" by auto
      with True bs show ?thesis by auto
    next
      case False note Bn = this
      with bound[of n] have "\<not> bound \<le> n" by auto
      hence "(Suc n, n) \<in> measure ?meas" by auto
      note IH = IH[OF this]
      from Bn res[unfolded Let_def Gcd, folded D.simps C.simps B.simps A.simps] 
      have res: "yun_factorization_main (B (Suc n)) (C (Suc n)) (Suc n) ((A n, n) # bs) = cs"
        by (simp add: Gcd)
      note IH = IH[OF this]
      {
        fix i 
        assume "i < Suc n" "\<not> i < n"
        hence "i = n" by arith
        hence "A i = A n" by simp
      } note missing = this
      have "set ((A n, n) # bs) = {(A i, i) |i. i < Suc n}"
        unfolding list.simps bs by (auto, insert missing)
      note IH = IH[OF this]
      from bs have "distinct (map snd ((A n, n) # bs))" by auto
      note IH = IH[OF this]
      show ?thesis by (rule IH)
    qed
  qed
qed

lemma yun_monic_factorization_res: assumes res: "yun_monic_factorization p = bs"
  shows "\<exists> m. set bs = {(A i, i) | i. i < m \<and> A i \<noteq> 1} \<and> B m = 1 \<and> distinct (map snd bs)"
proof -
  from res[unfolded yun_monic_factorization_def Let_def, 
    unfolded Gcd, folded B.simps C.simps, folded Gcd]
  obtain cs where yun: "yun_factorization_main (B 0) (C 0) 0 [] = cs" and bs: "bs = filter (\<lambda> (a,i). a \<noteq> 1) cs" 
    by auto
  from yun_factorization_main[OF yun] show ?thesis unfolding bs
    by (auto simp: distinct_map_filter)
qed                                                    

lemma yun_monic_factorization_context: assumes yun: "yun_monic_factorization p = bs"
  shows "square_free_factorization p (1,bs)" "(b,i) \<in> set bs \<Longrightarrow> monic b"
proof -
  from yun_monic_factorization_res[OF yun]
  obtain m where bs: "set bs = {(A i, i) | i. i < m \<and> A i \<noteq> 1}" and B: "B m = 1" 
    and dist: "distinct (map snd bs)" by auto
  have id: "{0 ..< m} = {i. i < m \<and> A i = 1} \<union> {i. i < m \<and> A i \<noteq> 1}" (is "_ = ?ignore \<union> _") by auto
  have "p = (\<Prod>i = 0..<m. A i ^ Suc i)"
    by (rule setprod_A_is_p_B_bound[OF B])
  also have "\<dots> = setprod (\<lambda> i. A i ^ Suc i) {i. i < m \<and> A i \<noteq> 1}"
    unfolding id 
    by (subst setprod.union_disjoint, (force+)[3],
    subst setprod.neutral[of ?ignore], auto)
  also have "\<dots> = (\<Prod>(a, i)\<in> set bs. a ^ Suc i)" unfolding bs
    by (rule setprod.reindex_cong[of snd], auto simp: inj_on_def, force)
  finally have 1: "p = (\<Prod>(a, i)\<in> set bs. a ^ Suc i)" .
  {
    fix a i
    assume "(a,i) \<in> set bs"
    hence A: "a = A i" "A i \<noteq> 1" unfolding bs by auto
    with A_square_free[of i] A_monic[of i] have "square_free a \<and> degree a \<noteq> 0" "monic a"
      by (auto simp: monic_degree_0)
  } note 2 = this
  {
    fix a i b j
    assume ai: "(a,i) \<in> set bs" and bj: "(b,j) \<in> set bs" and neq: "(a,i) \<noteq> (b,j)"
    hence a: "a = A i" and b: "b = A j" unfolding bs by auto
    from neq dist ai bj have neq: "i \<noteq> j" using a b by blast
    from gcd_A_A[OF neq] have "gcd a b = 1" unfolding a b .
  } note 3 = this
  have "monic p" unfolding p 
    by (rule monic_setprod, insert as_monic, auto intro: monic_power monic_mult)
  hence 4: "p \<noteq> 0" by auto
  from dist have 5: "distinct bs" unfolding distinct_map ..
  show "square_free_factorization p (1,bs)" unfolding square_free_factorization_def using 1 2 3 4 5
    by auto
  show "(b,i) \<in> set bs \<Longrightarrow> monic b" using 2 by auto
qed
end
end
end
end

lemma square_free_monic_poly: assumes monic: "monic p"
  shows "(poly (square_free_monic_poly gcd p) x = 0) = (poly p x = 0)"
proof -
  from monic_irreducible_factorization[OF monic]
  obtain as f where fin: "finite as" and p: "p = (\<Prod>a\<in>as. a ^ Suc (f a))" 
    and as: "as \<subseteq> {q. irreducible q \<and> monic q}"
    by auto
  def cs \<equiv> "{(a, f a) | a. a \<in> as}"
  have fin': "finite cs" unfolding cs_def using fin by auto
  {
    fix a i
    assume "(a,i) \<in> cs"
    hence "irreducible a" "monic a" unfolding cs_def using as by auto
  } note irr = this
  have disj: "\<And>a i b j. (a, i) \<in> cs \<Longrightarrow> (b, j) \<in> cs \<Longrightarrow> (a, i) \<noteq> (b, j) \<Longrightarrow> a \<noteq> b" unfolding cs_def by auto
  have p: "p = (\<Prod>(a, i)\<in>cs. a ^ Suc i)" unfolding p cs_def
    by (rule setprod.reindex_cong, auto, auto simp: inj_on_def)
  show ?thesis  
    by (rule square_free_monic_poly_context[OF refl p fin' disj irr])
qed

lemma square_free_poly: 
  "(poly (square_free_poly gcd p) x = 0) = (poly p x = 0)"
proof (cases "p = 0")
  case True
  thus ?thesis unfolding square_free_poly_def by auto
next
  case False
  let ?c = "coeff p (degree p)"
  let ?ic = "inverse ?c"
  have id: "square_free_poly gcd p = square_free_monic_poly gcd (smult ?ic p)"
    unfolding square_free_poly_def using False by auto
  from False have mon: "monic (smult ?ic p)" and ic: "?ic \<noteq> 0" by auto
  show ?thesis unfolding id square_free_monic_poly[OF mon]
    using ic by simp
qed  


lemma yun_monic_factorization: assumes res: "yun_monic_factorization gcd p = bs"
  and monic: "monic p"
  shows "square_free_factorization p (1,bs)" "(b,i) \<in> set bs \<Longrightarrow> monic b"
proof -
  from monic_irreducible_factorization[OF monic]
  obtain as f where fin: "finite as" and p: "p = (\<Prod>a\<in>as. a ^ Suc (f a))" 
    and as: "as \<subseteq> {q. irreducible q \<and> monic q}"
    by auto
  def cs \<equiv> "{(a, f a) | a. a \<in> as}"
  have fin': "finite cs" unfolding cs_def using fin by auto
  {
    fix a i
    assume "(a,i) \<in> cs"
    hence "irreducible a" "monic a" unfolding cs_def using as by auto
  } note irr = this
  have disj: "\<And>a i b j. (a, i) \<in> cs \<Longrightarrow> (b, j) \<in> cs \<Longrightarrow> (a, i) \<noteq> (b, j) \<Longrightarrow> a \<noteq> b" unfolding cs_def by auto
  have p: "p = (\<Prod>(a, i)\<in>cs. a ^ Suc i)" unfolding p cs_def
    by (rule setprod.reindex_cong, auto, auto simp: inj_on_def)
  note yun = yun_monic_factorization_context[OF refl p fin' disj irr res]
  show "square_free_factorization p (1,bs)" by (rule yun(1))
  show "(b,i) \<in> set bs \<Longrightarrow> monic b" by (rule yun(2))
qed

lemma square_free_factorization_smult: assumes c: "c \<noteq> 0"
  and sf: "square_free_factorization p (d,bs)"
  shows "square_free_factorization (smult c p) (c * d, bs)"
proof -
  from sf[unfolded square_free_factorization_def split]
  have p: "p = smult d (\<Prod>(a, i)\<in>set bs. a ^ Suc i)"
    and eq: "p = 0 \<longrightarrow> d = 0 \<and> bs = []" by blast+
  from eq c have eq: "smult c p = 0 \<longrightarrow> c * d = 0 \<and> bs = []" by auto
  from p have p: "smult c p = smult (c * d) (\<Prod>(a, i)\<in>set bs. a ^ Suc i)" by auto
  from eq p sf show ?thesis unfolding square_free_factorization_def by blast
qed

lemma yun_factorization: assumes res: "yun_factorization gcd p = c_bs"
  shows "square_free_factorization p c_bs" "(b,i) \<in> set (snd c_bs) \<Longrightarrow> monic b"
proof -
  note res = res[unfolded yun_factorization_def Let_def]
  have "square_free_factorization p c_bs \<and> ((b,i) \<in> set (snd c_bs) \<longrightarrow> monic b)"
  proof (cases "p = 0")
    case True
    with res have "c_bs = (0, [])" by auto    
    thus ?thesis unfolding True by (auto simp: square_free_factorization_def)
  next
    case False
    let ?c = "coeff p (degree p)"
    let ?ic = "inverse ?c"
    obtain c bs where cbs: "c_bs = (c,bs)" by force
    with False res
    have c: "c = ?c" "?c \<noteq> 0" and fact: "yun_monic_factorization gcd (smult ?ic p) = bs" by auto
    from False have mon: "monic (smult ?ic p)" by auto
    from yun_monic_factorization[OF fact mon]
    have sff: "square_free_factorization (smult ?ic p) (1, bs)" "(b, i) \<in> set bs \<Longrightarrow> monic b" .
    have id: "smult ?c (smult ?ic p) = p" using False by auto
    from square_free_factorization_smult[OF c(2) sff(1), unfolded id] sff
    show ?thesis unfolding cbs c by simp
  qed
  thus "square_free_factorization p c_bs" "(b,i) \<in> set (snd c_bs) \<Longrightarrow> monic b" by blast+
qed

lemma square_free_factorization_order_root_mem: 
  assumes sff: "square_free_factorization p (c,bs)"
    and p: "p \<noteq> 0"
    and ai: "(a,i) \<in> set bs" and rt: "poly a x = 0"
  shows "order x p = Suc i"
proof -
  note sff = square_free_factorizationD[OF sff]
  let ?prod = "(\<Prod>(a, i)\<in>set bs. a ^ Suc i)"
  from sff have pf: "p = smult c ?prod" by blast
  with p have c: "c \<noteq> 0" by auto
  have ord: "order x p = order x ?prod" unfolding pf 
    using order_smult[OF c] by auto
  def q \<equiv> "[: -x, 1 :]"
  have q0: "q \<noteq> 0" unfolding q_def by auto
  have iq: "irreducible q" by (rule linear_irreducible, auto simp: q_def)
  from rt have qa: "q dvd a" unfolding q_def poly_eq_0_iff_dvd .
  then obtain b where aqb: "a = q * b" unfolding dvd_def by auto
  from sff(2)[OF ai] have sq: "square_free a" and mon: "degree a \<noteq> 0" by auto
  let ?rem = "(\<Prod>(a, i)\<in>set bs - {(a,i)}. a ^ Suc i)"
  have p0: "?prod \<noteq> 0" using p pf by auto
  have "?prod = a ^ Suc i * ?rem"
    by (subst setprod.remove[OF _ ai], auto)
  also have "a ^ Suc i = q ^ Suc i * b ^ Suc i" unfolding aqb by (simp add: field_simps)
  finally have id: "?prod = q ^ Suc i * (b ^ Suc i * ?rem)" by simp
  hence dvd: "q ^ Suc i dvd ?prod" by auto
  {
    assume "q ^ Suc (Suc i) dvd ?prod"
    hence "q dvd ?prod div q ^ Suc i"
      by (metis dvd dvd_0_left_iff dvd_div_iff_mult p0 power_Suc)
    also have "?prod div q ^ Suc i = b ^ Suc i * ?rem"
      unfolding id by (rule div_mult_self1_is_id, insert q0, auto)
    finally have "q dvd b \<or> q dvd ?rem"
      using irreducible_dvd_mult[OF iq] irreducible_dvd_pow[OF iq] by blast
    hence False
    proof
      assume "q dvd b"
      with aqb have "q * q dvd a" by auto
      with sq[unfolded square_free_def] mon iq show False
        unfolding irreducible_def by auto
    next
      assume "q dvd ?rem"
      from irreducible_dvd_setprod[OF iq this]
      obtain b j where bj: "(b,j) \<in> set bs" and neq: "(a,i) \<noteq> (b,j)" and dvd: "q dvd b ^ Suc j" by auto
      from irreducible_dvd_pow[OF iq dvd] have qb: "q dvd b" .
      from sff(3)[OF ai bj neq] have gcd: "gcd a b = 1" .
      from qb qa have "q dvd gcd a b" by simp
      from dvd_imp_degree_le[OF this[unfolded gcd]] iq q0 show False unfolding irreducible_def
        by auto
    qed
  }
  hence ndvd: "\<not> q ^ Suc (Suc i) dvd ?prod" by blast
  with dvd have "order x ?prod = Suc i" unfolding q_def
    by (rule order_unique_lemma[symmetric])
  thus ?thesis unfolding ord .
qed

lemma square_free_factorization_order_root_no_mem: 
  assumes sff: "square_free_factorization p (c,bs)"
    and p: "p \<noteq> 0"
    and no_root: "\<And> a i. (a,i) \<in> set bs \<Longrightarrow> poly a x \<noteq> 0"
  shows "order x p = 0"
proof (rule ccontr)
  assume o0: "order x p \<noteq> 0"
  with order_root[of p x] p have 0: "poly p x = 0" by auto
  note sff = square_free_factorizationD[OF sff]
  let ?prod = "(\<Prod>(a, i)\<in>set bs. a ^ Suc i)"
  from sff have pf: "p = smult c ?prod" by blast
  with p have c: "c \<noteq> 0" by auto
  with 0 have 0: "poly ?prod x = 0" unfolding pf by auto
  def q \<equiv> "[: -x, 1 :]"
  from 0 have dvd: "q dvd ?prod" unfolding poly_eq_0_iff_dvd by (simp add: q_def)  
  have q0: "q \<noteq> 0" unfolding q_def by auto
  have iq: "irreducible q" by (rule linear_irreducible, auto simp: q_def)
  from irreducible_dvd_setprod[OF iq dvd]
  obtain a i where ai: "(a,i) \<in> set bs" and dvd: "q dvd a ^ Suc i" by auto
  from irreducible_dvd_pow[OF iq dvd] have dvd: "q dvd a" .
  hence "poly a x = 0" unfolding q_def by (simp add: poly_eq_0_iff_dvd q_def)
  with no_root[OF ai] show False by simp
qed

lemma square_free_factorization_order_root: 
  assumes sff: "square_free_factorization p (c,bs)"
    and p: "p \<noteq> 0"
  shows "order x p = i \<longleftrightarrow> (i = 0 \<and> (\<forall> a j. (a,j) \<in> set bs \<longrightarrow> poly a x \<noteq> 0) 
    \<or> (\<exists> a j. (a,j) \<in> set bs \<and> poly a x = 0 \<and> i = Suc j))" (is "?l = (?r1 \<or> ?r2)")
proof -
  note mem = square_free_factorization_order_root_mem[OF sff p]
  note no_mem = square_free_factorization_order_root_no_mem[OF sff p]
  show ?thesis
  proof
    assume "?r1 \<or> ?r2"
    thus ?l
    proof
      assume ?r2
      then obtain a j where aj: "(a,j) \<in> set bs" "poly a x = 0" and i: "i = Suc j" by auto
      from mem[OF aj] i show ?l by simp
    next
      assume ?r1 
      with no_mem[of x] show ?l by auto
    qed
  next
    assume ?l
    show "?r1 \<or> ?r2"
    proof (cases "\<exists>a j. (a, j) \<in> set bs \<and> poly a x = 0")
      case True
      then obtain a j where "(a, j) \<in> set bs" "poly a x = 0" by auto
      with mem[OF this] `?l`
      have ?r2 by auto
      thus ?thesis ..
    next
      case False
      with no_mem[of x] `?l` have ?r1 by auto
      thus ?thesis ..
    qed
  qed
qed

lemma square_free_factorization_root: 
  assumes sff: "square_free_factorization p (c,bs)"
    and p: "p \<noteq> 0"
  shows "{x. poly p x = 0} = {x. \<exists> a i. (a,i) \<in> set bs \<and> poly a x = 0}" 
  using square_free_factorization_order_root[OF sff p] p
  unfolding order_root by auto

lemma square_free_factor: assumes "p \<noteq> 0"
  and dvd: "a dvd p"
  and sf: "square_free p"
  shows "square_free a"
proof (intro square_freeI)
  fix q
  assume q: "degree q \<noteq> 0" and "q * q dvd a"
  hence "q * q dvd p" using dvd unfolding dvd_def by (auto simp: field_simps)
  with sf[unfolded square_free_def] q `p \<noteq> 0` show False by auto
qed

lemma square_free_factorization_factor: 
  assumes sff: "square_free_factorization p (c, bs1 @ (a,i) # bs2)"
  and r: "degree r \<noteq> 0" and s: "degree s \<noteq> 0"
  and a: "a = r * s"
  shows "square_free_factorization p (c, bs1 @ ((r,i) # (s,i) # bs2))"
proof -
  note sff = square_free_factorizationD[OF sff]
  let ?all = "set (bs1 @ (a,i) # bs2)"
  let ?rem = "(set bs1 \<union> set bs2)"
  let ?new = "bs1 @ ((r,i) # (s,i) # bs2)"
  from sff(2)[of a i] have sfa: "square_free a" and a0: "a \<noteq> 0" by auto
  {
    fix b j
    assume rem: "(b,j) \<in> ?rem" and ars: "b \<in> {a,r,s}"
    from sff(2)[of b j] rem have db: "degree b \<noteq> 0" by auto
    from ars have "b dvd a" unfolding a by auto
    with db have "b dvd gcd a b" by simp
    hence "degree (gcd a b) \<ge> degree b" using db 
      by (metis degree_0 dvd_imp_degree_le poly_gcd_zero_iff)
    with db have "gcd a b \<noteq> 1" by auto
    with sff(3)[of a i b j] rem have "(a,i) = (b,j)" by auto
    with sff(5) rem have False by auto
  } note no_mem = this
  {
    assume "r = s"
    hence "r * r dvd a" unfolding a by auto
    with sff(2)[of a i] r have False unfolding square_free_def by auto
  } 
  hence rs: "r \<noteq> s" by auto
  from no_mem have ai: "(a,i) \<in> ?all" "(a,i) \<notin> ?rem" by auto
  have "p = smult c (a ^ Suc i * (\<Prod>(a, i)\<in>set (bs1 @ (a, i) # bs2) - {(a,i)}. a ^ Suc i))"
    unfolding sff(1)
    by (subst setprod.remove[OF _ ai(1)], auto) 
  also have "set (bs1 @ (a, i) # bs2) - {(a,i)} = ?rem" using ai(2) by auto
  also have "a ^ Suc i = r ^ Suc i * s ^ Suc i" unfolding a by (simp add: field_simps)
  also have "\<dots> * (\<Prod>(a, i)\<in>?rem. a ^ Suc i) = r ^ Suc i * (s ^ Suc i * (\<Prod>(a, i)\<in>?rem. a ^ Suc i))" by simp
  also have "s ^ Suc i * (\<Prod>(a, i)\<in>?rem. a ^ Suc i) = (\<Prod>(a, i)\<in>insert (s,i) (?rem). a ^ Suc i)"
    by (subst setprod.insert, insert no_mem, auto)
  also have "r ^ Suc i * \<dots> = (\<Prod>(a, i)\<in>insert (r,i) (insert (s,i) ?rem). a ^ Suc i)"
    by (subst setprod.insert[of _ "(r,i)"], insert no_mem rs, auto)
  also have "insert (r,i) (insert (s,i) ?rem) = set ?new" by auto
  finally have 1: "p = smult c (setprod (\<lambda> (a,i). a ^ Suc i) (set ?new))" by simp
  from sff(4) have 4: "p \<noteq> 0" by auto
  from sff(5) no_mem rs have 5: "distinct ?new" by auto
  note sf = square_free_factor[OF a0 _ sfa]
  from sff(2) sf[of r] sf[of s] r s 
  have 2: "\<And> a i. (a,i) \<in> set ?new \<Longrightarrow> square_free a \<and> degree a \<noteq> 0"
    unfolding a by auto
  {
    let ?g = "gcd r s"
    assume no1: "?g \<noteq> 1"
    from r s rs have "monic ?g"
      by (metis poly_gcd_monic)
    with no1 have deg: "degree ?g \<noteq> 0" 
      by (simp add: monic_degree_0)
    have "?g * ?g dvd a" unfolding a 
      using mult_dvd_mono by blast
    with sfa deg sff(2)[of a i] have False unfolding square_free_def by auto
  }
  hence gcd_rs: "gcd r s = 1" "gcd s r = 1" 
    by (auto simp: poly_gcd_commute)
  {
    fix b j 
    assume bj: "(b,j) \<in> ?rem"
    from sff(3)[of b j a i] no_mem[OF bj] bj have gcd: "gcd b a = 1" by auto
    hence rs: "gcd b (r * s) = 1" and sr: "gcd b (s * r) = 1" unfolding a by (auto simp: ac_simps)
    from coprime_poly_factor[OF rs] s have br: "gcd b r = 1" by force
    from coprime_poly_factor[OF sr] r have bs: "gcd b s = 1" by force
    from br bs have "gcd r b = 1" "gcd s b = 1"
      by (auto simp: poly_gcd_commute)
    note this br bs
  } note gcd = this
  {
    fix a i b j
    assume ai: "(a,i) \<in> set ?new" and bj: "(b,j) \<in> set ?new" and diff: "(a,i) \<noteq> (b,j)"
    have "gcd a b = 1"
    proof (rule ccontr)
      assume not: "gcd a b \<noteq> 1"      
      from sff(3)[OF _ _ diff] not ai bj have "(a,i) \<notin> ?rem \<or> (b,j) \<notin> ?rem" by auto
      with gcd[of a i] gcd[of b j] not ai bj have "(a,i) \<notin> ?rem \<and> (b,j) \<notin> ?rem" by auto
      with ai bj have abrs: "{(a,i),(b,j)} \<subseteq> {(r,i),(s,i)}" by auto
      hence j: "j = i" by auto
      with diff abrs gcd_rs not show False by auto
    qed
  } note 3 = this
  show ?thesis unfolding square_free_factorization_def using 1 2 3 4 5 by blast
qed

function square_free_sample_optimization :: "'a :: field poly \<Rightarrow> ('a poly \<times> nat)list \<Rightarrow> ('a poly \<times> nat)list" where
  "square_free_sample_optimization x [] = []"
| "square_free_sample_optimization x ((a,i) # bs) = (if degree a > degree x \<and> x dvd a \<and> degree x \<noteq> 0
  then (x, i) # square_free_sample_optimization x ((a div x,i) # bs)
  else (a,i) # square_free_sample_optimization x bs)"
  by pat_completeness auto

termination by (relation "measures [(\<lambda> (_, bs). length bs), (\<lambda> (_, bs). degree (fst (hd bs)))]") 
  (auto intro: degree_div_less)

declare square_free_sample_optimization.simps[simp del]

lemma square_free_sample_optimization: assumes "square_free_factorization p (c,as @ bs)"
  shows "square_free_factorization p (c, as @ square_free_sample_optimization x bs)"
  using assms
proof (induct x bs arbitrary: as rule: square_free_sample_optimization.induct)
  case (2 x a i bs)
  note IH = 2(1-2)
  note sff = 2(3)
  let ?curr = "square_free_sample_optimization x ((a,i) # bs)"  
  note simp = square_free_sample_optimization.simps(2)[of x a i bs]
  show ?case
  proof (cases "degree a > degree x \<and> x dvd a \<and> degree x \<noteq> 0")
    case False
    hence res: "?curr = (a,i) # square_free_sample_optimization x bs" unfolding simp by auto
    from IH(2)[OF False, of "as @ [(a,i)]"] sff
    show ?thesis unfolding res by simp
  next
    case True
    let ?rec = "square_free_sample_optimization x ((a div x,i) # bs)"
    from True
    have res: "?curr = (x, i) # ?rec" unfolding simp by auto
    from True have a0: "a \<noteq> 0" by auto
    from True have a: "a = x * (a div x)" 
      by (metis dvd_div_mult_self mult.commute)
    hence "degree a = degree (x * (a div x))" by simp
    also have "\<dots> = degree x + degree (a div x)"
      by (rule degree_mult_eq, insert a a0, auto)
    finally have "degree x \<noteq> 0" "degree (a div x) \<noteq> 0" using True by auto
    from square_free_factorization_factor[OF sff this a]
    have sff: "square_free_factorization p (c, (as @ [(x, i)]) @ (a div x, i) # bs)" by auto
    from IH(1)[OF True this]
    show ?thesis unfolding res by simp
  qed
qed (simp add: square_free_sample_optimization.simps)
    
fun square_free_psamples_optimization :: "'a :: field poly list \<Rightarrow> ('a poly \<times> nat)list \<Rightarrow> ('a poly \<times> nat)list" where
  "square_free_psamples_optimization [] bs = bs"
| "square_free_psamples_optimization (x # xs) bs = 
    square_free_psamples_optimization xs (square_free_sample_optimization x bs)"

lemma square_free_psamples_optimization: 
  "square_free_factorization p (c,bs) \<Longrightarrow> 
  square_free_factorization p (c, square_free_psamples_optimization xs bs)"
proof (induct xs arbitrary: bs)
  case (Cons x xs bs)
  from square_free_sample_optimization[of p c Nil bs x]
    Cons(2) have "square_free_factorization p (c, square_free_sample_optimization x bs)" by auto
  from Cons(1)[OF this]
  show ?case by simp
qed simp

definition square_free_samples_optimization :: "'a :: field list \<Rightarrow> ('a poly \<times> nat)list \<Rightarrow> ('a poly \<times> nat)list" where
  "square_free_samples_optimization xs = square_free_psamples_optimization (map (\<lambda> x. [: -x, 1 :]) xs)"

lemma square_free_samples_optimization: 
  "square_free_factorization p (c,bs) \<Longrightarrow> 
  square_free_factorization p (c, square_free_samples_optimization xs bs)"
  unfolding square_free_samples_optimization_def by (rule square_free_psamples_optimization)

definition root_finder_optimization :: "('a :: field poly \<Rightarrow> 'a list) \<Rightarrow> ('a poly \<times> nat)list \<Rightarrow> ('a poly \<times> nat)list" where
  "root_finder_optimization root_finder bs \<equiv> let
    xs = [x. (a,_) <- bs, x <- root_finder a]
    in square_free_samples_optimization xs bs"

lemma root_finder_optimization: "square_free_factorization p (c,bs) \<Longrightarrow> 
  square_free_factorization p (c, root_finder_optimization root_finder bs)"
  unfolding root_finder_optimization_def Let_def
  by (rule square_free_samples_optimization)

(* the generic factorization algorithm. 
  it can be feed with potential polynomial factors like $x^2 + 1$,
  and with potential roots, and with an arbitrary root finding algorithm. *)
definition root_finder_samples_factorization 
  :: "('a :: field_char_0 poly \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a poly list \<Rightarrow> 'a poly \<Rightarrow> 'a \<times> ('a poly \<times> nat)list" where
  "root_finder_samples_factorization root_finder samples psamples p \<equiv> let
     (c,bs) = yun_factorization gcd p;
     cs = square_free_psamples_optimization psamples bs;
     ds = square_free_samples_optimization samples cs;
     es = root_finder_optimization root_finder ds
     in (c,es)"


lemma root_finder_samples_factorization: 
  "square_free_factorization p (root_finder_samples_factorization root_finder samples psamples p)"
proof -
  let ?sff = "square_free_factorization p"
  obtain c bs where yun: "yun_factorization gcd p = (c,bs)" by force
  from yun_factorization[OF this] have "?sff (c,bs)" by auto
  from root_finder_optimization[OF square_free_samples_optimization[OF 
     square_free_psamples_optimization[OF this]]]
  show ?thesis unfolding root_finder_samples_factorization_def Let_def yun split .
qed
end
