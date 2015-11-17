(*  Title:      IntNatAux.thy
    Author:     Roelof Oosterhuis
                2007  Rijksuniversiteit Groningen
*)

section {* Powers, prime numbers and divisibility *}

theory IntNatAux
imports 
  "~~/src/HOL/Old_Number_Theory/Factorization" 
  "~~/src/HOL/Old_Number_Theory/EvenOdd"
begin

text {* Contains lemmas about divisibility and coprimality of powers, as well as some results about parities and small powers. Most lemmas are developed for the integers as well as for the natural numbers. *}

subsection {* Auxiliary results *}

lemma make_relprime: 
  "(a \<noteq> 0 \<or> b \<noteq> 0) \<Longrightarrow> \<exists> c d. a = gcd a b*c \<and> b = gcd a b*d \<and> gcd c d = 1"
proof -
  assume ab0: "a\<noteq>0 \<or> b\<noteq>0"
  let ?g = "gcd a b"
  have "?g dvd a \<and> ?g dvd b" by auto
  then obtain c d where abcd: "a = ?g*c \<and> b = ?g*d" by (auto simp add: dvd_def)
  moreover have "gcd c d=1"
  proof -
    from abcd have "?g*gcd c d=?g" by (auto simp add: gcd_mult_distrib2)
    moreover with ab0 have "?g \<noteq> 0" by (simp add: gcd_zero)
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis by auto
qed
  
lemma factor_exists_general: "(a::nat) \<noteq> 0 \<Longrightarrow> (\<exists> ps. primel ps \<and> prod ps = a)"
proof - 
  assume a0: "a\<noteq>0"
  show ?thesis
  proof (case_tac "a=1")
    assume "a=1" hence "primel [] \<and> prod [] = a" by (auto simp add: primel_def)
    thus ?thesis by auto
  next
    assume "a\<noteq>1" with a0 have "a>Suc 0" by auto
    thus ?thesis by (rule factor_exists)
  qed
qed

lemma make_zrelprime: "(a \<noteq> 0 \<or> b \<noteq> 0) 
  \<Longrightarrow> \<exists> c d. a = zgcd a b*c \<and> b = zgcd a b*d \<and> zgcd c d=1"
proof -
  assume ab0: "a \<noteq> 0 \<or> b \<noteq> 0"
  let ?g = "zgcd a b"
  have "?g dvd a \<and> ?g dvd b" by auto
  then obtain c d where abcd: "a = ?g*c \<and> b = ?g*d" by (auto simp add: dvd_def)
  moreover have "zgcd c d = 1"
  proof -
    from abcd have "?g * zgcd c d = ?g" 
      by (auto simp add: zgcd_zmult_distrib2 zgcd_geq_zero)
    moreover with ab0 have "?g \<noteq> 0" by (auto simp add: zgcd_def gcd_zero)
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

lemma int_nat_abs_eq_abs: "int(nat\<bar>x::int\<bar>) = \<bar>x\<bar>"
  by simp

lemma prime_impl_zprime_int: "prime (a::nat) \<Longrightarrow> zprime (int a)"
proof -
  assume pra: "prime a"
  show "zprime (int a)"
  proof -
    from pra have agr1: "1 < int a" by (unfold prime_def, auto)
    moreover have "!!m. m \<ge> 0 \<and> m dvd int a \<and> m \<noteq> int a \<Longrightarrow> m=1" 
    proof -
      { fix m assume m: "m \<ge> 0 \<and> m dvd int a \<and> m \<noteq> int a"
        then obtain k::int where k: "int a = m*k" by (auto simp add: dvd_def)
        from m have "int (nat m) = m" by auto
        with k have "int a = (int (nat m)) * k" by simp
        hence "nat (int a) = nat ( (int (nat m)) * k )" by simp
        hence "a = nat ( (int (nat m)) * k )" by (simp only: nat_int)
        also have "\<dots> = (nat m) * (nat k)" by (simp add: nat_int nat_mult_distrib)
        finally have "nat m dvd a" by auto
        with pra have "nat m = a \<or> nat m = 1" by (auto simp add: prime_def)
        moreover from m have "nat m \<noteq> a" by auto
        ultimately have "nat m = 1" by auto
        hence "m = 1" by arith }
      thus "!!m. m \<ge> 0 \<and> m dvd int a \<and> m \<noteq> int a \<Longrightarrow> m=1" by auto
    qed
    ultimately show ?thesis by (auto simp add: zprime_def)
  qed
qed

lemma zprime_factor_exists: "(a::int) > 1 \<Longrightarrow> \<exists> p. zprime p \<and> p dvd a"
proof -
  assume a1: "a > 1" hence a: "int (nat a) = a" by (auto simp add: int_nat_eq)
  with a1 have "nat a > 1" by auto
  hence "\<exists> l. primel l \<and> prod l = nat a" by (simp only: factor_exists)
  then obtain l where l: "primel l \<and> prod l = nat a" by (auto)
  show ?thesis
  proof (cases l)
    case Nil with l have "nat a = 1" by auto
    with a1 show ?thesis by arith
  next
    case (Cons p ps)
    with l have "nat a = p*prod ps" and p: "prime p" by (auto simp add: primel_def)
    hence "int (nat a) = (int p)*int(prod ps)"
      by (auto simp add: int_mult)
    with a p have "zprime (int p) \<and> int p dvd a"
      by (auto simp add: prime_impl_zprime_int)
    thus ?thesis by blast
  qed
qed

lemma best_division_abs: "(x::int) > 0 \<Longrightarrow> \<exists> n. 2 * \<bar>y - n*x\<bar> \<le> x"
proof -
  assume x0: "x>0"
  then obtain b where b: "b \<ge> 0 \<and> b < x \<and> [y = b] (mod x)"
    by (blast dest: zcong_zless_unique)
  hence "x dvd (y-b)" by (simp only: zcong_def)
  then obtain m where "y-b = x*m" by (auto simp add: dvd_def)
  hence m: "b = y - m*x" by (simp only: ac_simps)
  show ?thesis
  proof (cases)
    assume "2*\<bar>b\<bar> \<le> x"
    with m show ?thesis by auto
  next
    assume "\<not> 2*\<bar>b\<bar> \<le> x"
    with b have bx: "2*b > x" by auto
    hence bx1: "2*(x-b) < x" by auto
    from b have bx2: "b-x < 0" by auto
    obtain n where "n = m+1" by simp
    hence "y - n*x = y - m*x - x" by (simp only: distrib_right mult_1_left)
    with m have n: "y - n*x = b-x" by simp
    with bx2 have pos: "-y + n*x > 0" by simp
    moreover from n bx1 have "2*(-y + n*x) < x" by simp
    ultimately have "2*\<bar>y - n*x\<bar> < x" by simp
    hence "2*\<bar>y - n*x\<bar> \<le> x" by (unfold zabs_def, auto)
    thus ?thesis by auto
  qed
qed

lemma best_odd_division_abs: "\<lbrakk> (x::int) > 0; x \<in> zOdd \<rbrakk> 
  \<Longrightarrow> \<exists> n. 2 * \<bar>y - n*x\<bar> < x"
proof -
  assume "x>0" and odd: "x \<in> zOdd"
  then obtain n where n: "2 * \<bar>y - n*x\<bar> \<le> x" by (auto dest: best_division_abs)
  moreover have "x \<noteq> 2 * \<bar>y - n*x\<bar>"
  proof (rule ccontr, clarsimp)
    assume "x = 2*\<bar>y - n*x\<bar>" 
    hence "x \<in> zEven" by (unfold zEven_def, auto)
    with odd show False by (auto simp only: odd_iff_not_even)
  qed
  ultimately have "2*\<bar>y - n*x\<bar> < x" by simp
  thus ?thesis by auto
qed
 
lemma zprime_2: "zprime 2"
  apply (auto simp add: zprime_def)
  apply (frule zdvd_imp_le, simp)
  apply (auto simp add: order_le_less dvd_def)
done

lemma zgcd1_iff_no_common_primedivisor: 
  "(zgcd a b=1) = (\<not>(\<exists> p. zprime p \<and> p dvd a \<and> p dvd b))"
proof (rule ccontr, auto)
  fix p assume ab: "zgcd a b=1" and "p dvd a" and "p dvd b" and p: "zprime p"
  hence "p dvd a \<and> p dvd b" by simp
  hence "p dvd zgcd a b" by (simp add: zgcd_greatest_iff)
  with ab p show False by (unfold zprime_def, auto)
next
  let ?g = "zgcd a b"
  assume ps: "\<forall> p. zprime p \<longrightarrow> p dvd a \<longrightarrow> \<not> p dvd b"
  assume g1: "?g \<noteq> 1"
  moreover have "?g \<noteq> 0"
  proof (rule ccontr, simp)
    assume "a = 0 \<and> b = 0"
    hence "2 dvd a \<and> 2 dvd b" by simp
    with ps show False by (auto simp add: zprime_2)
  qed
  moreover have "?g \<ge> 0" by (rule zgcd_geq_zero)
  ultimately have "?g > 1" by arith
  then obtain p where "zprime p \<and> p dvd ?g" 
    by (frule_tac a="?g" in zprime_factor_exists, auto)
  hence "zprime p \<and> p dvd a \<and> p dvd b" by (simp add: zgcd_greatest_iff)
  with ps show False by auto
qed

lemma pos_zmult_pos: "a > (0::int) \<Longrightarrow> a*b > 0 \<Longrightarrow> b > 0"
  apply (case_tac "b = 0", auto)
  apply (rule ccontr, subgoal_tac "b < 0", auto)
  apply (subgoal_tac "a*b < a*0", auto dest: zmult_zless_mono2)
done

subsection {* Parity of integers *}

lemma power_preserves_even: "n>0 \<Longrightarrow> (x^n \<in> zEven) = (x \<in> zEven)"
  apply (induct n, auto simp add: even_times_either)
  apply (case_tac "n\<noteq>0", auto dest: even_product)
done

lemma power_preserves_odd: "n>0 \<Longrightarrow> (x^n \<in> zOdd) = (x \<in> zOdd)"
  apply (induct n, auto, rule odd_mult_odd_prop, auto)
  apply (case_tac "n\<noteq>0", auto dest: odd_times_odd)
done

lemma even_plus_odd: "a \<in> zEven \<Longrightarrow> b \<in> zOdd \<Longrightarrow> a+b \<in> zOdd"
  apply (auto simp add: zEven_def zOdd_def)
  apply (rule_tac x="k+ka" in exI, auto)
done

lemma odd_plus_odd: "a \<in> zOdd \<Longrightarrow> b \<in> zOdd \<Longrightarrow> a+b \<in> zEven"
  apply (auto simp add: zEven_def zOdd_def)
  apply (rule_tac x="1+k+ka" in exI, auto)
done

lemma even_plus_odd_prop1: "a+b \<in> zOdd \<Longrightarrow> a \<in> zOdd \<Longrightarrow> b \<in> zEven"
  by (subgoal_tac "a+b - a \<in> zEven", auto dest: odd_minus_odd)

lemma even_plus_odd_prop2: "a+b \<in> zOdd \<Longrightarrow> a \<in> zEven \<Longrightarrow> b \<in> zOdd"
  by (subgoal_tac "a+b - a \<in> zOdd", auto dest: odd_minus_even)

subsection {* Powers of natural numbers *}

lemma gcd_1_power_left_distrib: "gcd a b = 1 \<Longrightarrow> gcd (a^n) b = 1"
  by (induct n, auto simp add: gcd_mult_cancel)

text {* NB: the next (identical) lemma is just added to illustrate the difference between Isar and Isabelle scripting. *}
lemma alternative_gcd_1_power_left_distrib: "gcd a b = 1 \<Longrightarrow> gcd(a^n) b = 1"
proof -
  assume ab: "gcd a b=1"
  thus "gcd (a^n) b = 1"
  proof (induct n)
    case 0
    show "gcd (a^0) b = 1" by auto
  next
    case (Suc n)
    hence "gcd (a^n) b = 1" by simp
    with ab have "gcd (a*a^n) b = 1" by (simp only: gcd_mult_cancel)
    thus "gcd (a^Suc n) b = 1" by simp
  qed
qed

lemma gcd_1_power_distrib: "gcd a b = 1 \<Longrightarrow> gcd(a^n) (b^n) = 1"
proof -
  assume "gcd a b=1"
  hence "gcd (a^n) b = 1" by (rule gcd_1_power_left_distrib)
  hence "gcd b (a^n) = 1" by (simp only: gcd_commute)
  hence "gcd (b^n) (a^n) = 1" by (rule gcd_1_power_left_distrib)
  thus "gcd (a^n) (b^n) = 1" by (simp only: gcd_commute)
qed
    
lemma gcd_power_distrib: "gcd a b ^ n = gcd (a^n) (b^n)"
proof cases
  assume "a=0 \<and> b=0"
  thus ?thesis by (auto simp add: power_0_left)
next
  let ?g = "gcd a b"
  assume "\<not> (a=0 \<and> b=0)"
  hence "a \<noteq> 0 \<or> b \<noteq> 0" by simp
  then obtain c d where abcd: "a = ?g*c \<and> b = ?g*d \<and> gcd c d=1" 
    by (frule_tac a="a" in make_relprime, auto)
  moreover have "(?g*c)^n = ?g^n * c^n \<and> (?g*d)^n = ?g^n * d^n" 
    by (simp add: power_mult_distrib)
  ultimately have "gcd (a^n) (b^n) = ?g^n * gcd (c^n) (d^n)" by (simp only: gcd_mult_distrib2)
  moreover from abcd have "gcd (c^n) (d^n) = 1" by (simp only: gcd_1_power_distrib)
  ultimately show ?thesis by simp
qed

text {* Useful lemma: if prime $p | a^n$ then $p | a$. *}

lemma prime_dvd_power: "\<lbrakk> prime p; p dvd a^n \<rbrakk> \<Longrightarrow> p dvd a"
proof (induct n)
  case 0 hence "prime p \<and> p = 1" by auto
  thus ?thesis by auto
next case (Suc n) hence IH: "prime p \<and> p dvd a^n \<Longrightarrow> p dvd a" by auto
  assume p: "prime p" and "p dvd a^Suc n"
  hence "p dvd a*a^n" by simp
  with p have "p dvd a \<or> p dvd a^n" by (simp add: prime_dvd_mult)
  with IH and p show "p dvd a" by auto
qed

lemma prime_power_dvd_cancel_right: 
  "\<lbrakk> prime p; \<not> p dvd b; p^n dvd a*b \<rbrakk> \<Longrightarrow> p^n dvd a"
proof -
  assume p: "prime p" and pb: "\<not> p dvd b" 
  hence p1: "p>1"  by (simp add: prime_def)
  have "!!a. p^n dvd a*b \<longrightarrow> p^n dvd a"
  proof (induct n)
    case 0 thus ?case by auto
  next
    case (Suc n) hence IH: "!!a. p^n dvd a*b \<longrightarrow> p^n dvd a" .
    fix a show "p^Suc n dvd a*b \<longrightarrow> p^Suc n dvd a"
    proof (auto)
      assume ppnab: "p*p^n dvd a*b" 
      hence "p dvd a*b" by (rule dvd_mult_left)
      with p have "p dvd a \<or> p dvd b" by (rule prime_dvd_mult)
      with pb have "p dvd a" by simp
      then obtain k where apk: "a = p * k" by (auto simp add: dvd_def)
      with ppnab have "p*p^n dvd p*(k*b)" by (auto simp add: ac_simps)
      with p1 have "p^n dvd k*b" by (auto dest: dvd_mult_cancel)
      with IH have "p^n dvd k" ..
      with apk show "p*p^n dvd a" by (simp add: mult_dvd_mono)
    qed
  qed
  thus "p^n dvd a*b \<Longrightarrow> p^n dvd a" ..
qed
   
text {* Helping lemma: if $n > 0$ then $a^n | b^n \Longleftrightarrow a | b$. *}

lemma nat_power_dvd_mono: "n \<noteq> 0 \<Longrightarrow> (a^n dvd b^n) = (a dvd (b::nat))"
proof 
  assume "n \<noteq> 0"
  then obtain m where mn: "n = Suc m" 
    by (frule_tac n="n" in not0_implies_Suc, auto)
  assume "a^n dvd b^n"
  then obtain k where k: "b^n = a^n * k" by (auto simp add: dvd_def)
  moreover have "gcd (a^n) ((a^n)*k) = (a^n) * gcd 1 k" by (simp add: gcd_mult_distrib2)
  ultimately have "gcd (a^n) (b^n) = a^n" by (auto simp add: gcd_commute gcd_1)
  hence "gcd a b^n = a^n" by (simp add: gcd_power_distrib)
  with mn have "a = gcd a b" by (rule_tac n="m" in power_inject_base, auto)
  moreover have "gcd a b dvd b" by (rule gcd_dvd2)
  ultimately show "a dvd b" by simp
next
  assume "a dvd b"
  then obtain k where "b = a * k" by (auto simp add: dvd_def)
  hence "b^n = a^n * k^n" by (simp only: power_mult_distrib)
  thus "a^n dvd b^n" by auto
qed
(*
lemma primel_add_prime: "\<lbrakk> primel xs; primel ys; prime p; prod xs = p * prod ys \<rbrakk> 
  \<Longrightarrow> length xs = 1 + length ys"
proof -
  assume "primel xs" and "primel ys" and "prime p" and "prod xs = p * prod ys"
  moreover hence "prod xs = prod (p#ys) \<and> primel (p#ys)" 
    by (unfold primel_def, auto)
  ultimately have "xs <~~> (p#ys)" by (simp add: factor_unique)
  hence "length xs = length (p#ys)" by (rule perm_length)
  thus ?thesis by (simp add: length_append)
qed

lemma primel_add_factor: "\<lbrakk> primel xs; primel ys; g > 1; prod xs = g * prod ys \<rbrakk> 
  \<Longrightarrow> length xs > length ys"
proof -
  assume pxs: "primel xs" and pys: "primel ys" and g1: "g > 1" 
    and prod: "prod xs = g * prod ys"
  hence "\<exists> zs. primel zs \<and> prod zs = g" by (simp only: factor_exists)
  then obtain zs where zs: "primel zs \<and> prod zs = g" by auto
  with g1 have "zs \<noteq> []" by auto
  hence lzspos: "length zs > 0" by auto
  from zs and prod have prodxyz: "prod xs = prod (zs@ys)" by (simp add: prod_append)
  from pys and zs have "primel (zs@ys)" by (simp add: primel_append)
  with pxs and prodxyz have perm: "xs <~~> (zs@ys)" by (simp add: factor_unique)
  hence "length xs = length (zs@ys)" by (rule perm_length)
  hence "length xs = length zs + length ys" by (simp add: length_append)
  with lzspos show "length xs > length ys" by auto
qed
*)
text {* Theorem: if $n>0$ and $\gcd a b=1$ and $ab=c^n$ then $\exists k: a = k^n$. Proof uses induction on the number of prime factors of $c$. *}

theorem nat_relprime_power_divisors: 
  assumes npos: "n\<noteq>0" and abcn: "a*b = c^n" and relprime: "gcd a b = 1"
  shows "\<exists> k. a = k^n"
proof -  
  from npos obtain m where mn: "n = Suc m" 
    by (frule_tac n="n" in not0_implies_Suc, auto)
  show ?thesis
  proof (case_tac "c=0")
    assume "c=0" with abcn npos mn have "a*b = 0" by (auto simp only: power_0_Suc)
    hence "a=0 \<or> b=0" by auto
    moreover
    { assume "a=0" with mn npos have "a = 0^n" by (auto simp only: power_0_Suc)
      hence ?thesis by blast }
    moreover
    { assume "b=0" with relprime have "a = 1^n" by (auto simp only: gcd_0 power_one)
      hence ?thesis by blast }
    ultimately show ?thesis by blast
  next
    assume "c\<noteq>0" then obtain xs where xs: "primel xs \<and> prod xs = c" 
      by (frule_tac a="c" in factor_exists_general, auto)
    moreover have 
      "!!a b. (primel xs \<and> a*b = (prod xs)^n \<and> gcd a b=1) \<Longrightarrow> \<exists>k. a = k^n"
    proof (induct xs)
      case Nil
      hence "a = 1^n" by simp
      thus "\<exists> k. a = k^n" ..
    next
      case (Cons p ps) 
      hence ass: "primel ps \<and> prime p \<and> a*b=p^n*(prod ps)^n \<and> gcd a b=1 " 
        and IH: "!!a b. primel ps \<and> a*b = (prod ps)^n \<and> gcd a b=1 \<Longrightarrow> \<exists> k. a = k^n" 
        by (auto simp add: primel_def power_mult_distrib)
      hence pnab: "p^n dvd a*b" and pn0: "p^n \<noteq> 0" 
        by (auto simp add: prime_def)
      moreover
      { assume pa: "p dvd a"
        have "\<not> p dvd b"
        proof (rule ccontr, simp)
          assume "p dvd b"
          with pa have "p dvd gcd a b" by (simp add: gcd_greatest_iff)
          with ass show "False" by (auto simp add: prime_def)
        qed
        with ass pnab have "p^n dvd a" by (simp add: prime_power_dvd_cancel_right)
        then obtain A where A: "a = p^n * A" by (auto simp add: dvd_def)
        with ass pn0 have "A*b = (prod ps)^n" by auto
        moreover have "gcd A b=1"
        proof -
          let ?g = "gcd A b"
          have "?g dvd A \<and> ?g dvd b" by (simp add: gcd_greatest)
          with A have "?g dvd a \<and> ?g dvd b" by (simp add: dvd_mult)
          hence "?g dvd gcd a b" by (simp only: gcd_greatest)
          with ass show "?g = 1" by auto
        qed
        moreover from IH ass have 
          "A*b = (prod ps)^n \<and> gcd A b=1 \<Longrightarrow> \<exists> k. A = k^n" by auto
        ultimately have "\<exists> k. A = k^n" by auto
        then obtain k where "A = k^n" by auto
        with A have "a = (p*k)^n" by (auto simp add: power_mult_distrib)
        hence "\<exists> k. a = k^n" by blast }
      moreover
      { assume "\<not> p dvd a" 
        moreover from ass pnab have "p^n dvd b*a \<and> prime p"
          by (auto simp only: ac_simps)
        ultimately have "p^n dvd b" by (simp add: prime_power_dvd_cancel_right)
        then obtain B where B: "b = p^n * B" by (auto simp add: dvd_def)
        with ass pn0 have "a*B = (prod ps)^n" by auto
        moreover have "gcd a B=1"
        proof -
          let ?g = "gcd a B"
          have "?g dvd a \<and> ?g dvd B" by (simp add: gcd_greatest)
          with B have "?g dvd a \<and> ?g dvd b" by (simp add: dvd_mult)
          hence "?g dvd gcd a b" by (simp only: gcd_greatest)
          with ass show "?g = 1" by auto
        qed
        moreover from IH ass have 
          "a*B = (prod ps)^n \<and> gcd a B=1 \<Longrightarrow> \<exists> k. a = k^n" by auto
        ultimately have "\<exists> k. a = k^n" by auto }
      ultimately show "\<exists> k. a = k^n" by auto
    qed
    moreover from abcn relprime have "gcd a b=1 \<and> a*b=c^n" by simp
    ultimately show ?thesis by auto
  qed
qed

subsection {* Powers of integers *} 

text {* Now turn to the case of integers. This lemma is based on its equivalent for the natural numbers. *}

corollary int_relprime_power_divisors: 
  assumes abcn: "a*b = c^n" and n: "n>1" and relprime: "zgcd a b = 1"
  shows "\<exists> k. \<bar>a\<bar> = k^n"
proof -
  let ?a1 = "nat\<bar>a\<bar>"
  let ?b1 = "nat\<bar>b\<bar>"
  let ?c1 = "nat\<bar>c\<bar>"
  from relprime have absrelprime: "gcd ?a1 ?b1 = 1" by (auto simp only: zgcd_def)
  have "\<bar>a*b\<bar> = \<bar>a\<bar>*\<bar>b\<bar>" by (simp add: abs_mult)
  with abcn have "\<bar>c\<bar>^n = \<bar>a\<bar>*\<bar>b\<bar>" by (simp add: power_abs)
  hence "int(?c1^n) = int(?a1*?b1)" by (simp only: int_nat_abs_eq_abs int_mult of_nat_power)
  hence "?a1*?b1 = ?c1^n" by (simp only: of_nat_eq_iff)
  with absrelprime and n have "\<exists> k. ?a1 = k^n" by (simp only: nat_relprime_power_divisors)
  then obtain k::nat where alpha: "?a1 = k^n" by auto
  moreover have "int ?a1 = \<bar>a\<bar>" by (simp add: int_nat_eq)
  ultimately have "\<bar>a\<bar> = int(k^n)" by simp
  hence "\<bar>a\<bar> = int(k)^n" by (simp only: of_nat_power)
  thus ?thesis by auto
qed

corollary int_triple_relprime_power_divisors: 
  "\<lbrakk> a*b*c = d^n; n > 1; zgcd a b = 1; zgcd b c = 1; zgcd c a = 1 \<rbrakk> 
  \<Longrightarrow> \<exists> k l m. \<bar>a\<bar> = k^n \<and> \<bar>b\<bar> = l^n \<and> \<bar>c\<bar> = m^n"
proof -
  assume abcd: "a*b*c = d^n" and n1: "n > 1"
    and ab: "zgcd a b = 1" and bc: "zgcd b c = 1" and ca: "zgcd c a = 1"
  hence ba: "zgcd b a = 1" and cb: "zgcd c b = 1" and ac: "zgcd a c = 1" 
    by (auto simp only: zgcd_commute)
  from ba ca have "zgcd (b*c) a = 1" by (simp only: zgcd_zmult_cancel)
  with abcd have "a*(b*c) = d^n \<and> zgcd a (b*c) = 1" by (simp add: zgcd_commute)
  with n1 have k: "\<exists> k. \<bar>a\<bar> = k^n" by (auto dest: int_relprime_power_divisors)
  from ab cb have "zgcd (a*c) b = 1" by (simp only: zgcd_zmult_cancel)
  with abcd have "b*(a*c) = d^n \<and> zgcd b (a*c) = 1" 
    by (simp add: zgcd_commute ac_simps)
  with n1 have l: "\<exists> l. \<bar>b\<bar> = l^n" by (auto dest: int_relprime_power_divisors)
  from ac bc have "zgcd (a*b) c = 1" by (simp only: zgcd_zmult_cancel)
  with abcd have "c*(a*b) = d^n \<and> zgcd c (a*b) = 1" 
    by (simp add: zgcd_commute ac_simps)
  with n1 have m: "\<exists> m. \<bar>c\<bar> = m^n" by (auto dest: int_relprime_power_divisors)
  from k l m show ?thesis by auto
qed

lemma neg_odd_power: "\<lbrakk> x \<in> zOdd; x \<ge> 0 \<rbrakk> \<Longrightarrow> (-a::int)^(nat x) = -(a^(nat x))" 
proof -
  assume "x \<in> zOdd" and "0 \<le> x"
  hence "-(a^(nat x)) = (-1)^(nat x) * a^(nat x)" by (simp add: neg_one_odd_power)
  also have "\<dots> = (-1*a)^(nat x)" by (simp only: power_mult_distrib)
  finally show ?thesis by simp
qed 

lemma neg_even_power: "\<lbrakk> x \<in> zEven; x \<ge> 0 \<rbrakk> \<Longrightarrow> (-a::int)^(nat x) = a^(nat x)"
proof -
  assume "x \<in> zEven" and "x \<ge> 0"
  hence "a^(nat x) = (-1)^(nat x) * a^(nat x)" by (simp add: neg_one_even_power)
  also have "\<dots> = (-1*a)^(nat x)" by (simp only: power_mult_distrib)
  finally show ?thesis by simp
qed

corollary int_relprime_odd_power_divisors: 
  "\<lbrakk> a*b = c^(nat x); nat x > 1; x \<in> zOdd; zgcd a b = 1 \<rbrakk> \<Longrightarrow> \<exists> k. a = k^(nat x)"
proof -
  assume "a*b = c^(nat x)" and x1: "nat x > 1" and odd: "x \<in> zOdd" and "zgcd a b=1"
  hence "\<exists> k. \<bar>a\<bar> = k^(nat x)" by (simp only: int_relprime_power_divisors)
  then obtain k where k: "\<bar>a\<bar> = k^(nat x)" by blast
  { assume "a \<noteq> k^(nat x)"
    with k have "a = -(k^(nat x))" by arith
    with x1 odd have "a = (-k)^(nat x)" by (simp add: neg_odd_power) }
  thus ?thesis by blast
qed

corollary int_triple_relprime_odd_power_divisors: 
  "\<lbrakk> a*b*c = d^(nat x); nat x>1; x\<in>zOdd; zgcd a b = 1; zgcd b c = 1; zgcd c a = 1 \<rbrakk>
  \<Longrightarrow> \<exists> k l m. a = k^(nat x) \<and> b = l^(nat x) \<and> c = m^(nat x)"
proof -
  assume abcd: "a*b*c = d^(nat x)" and x1: "nat x > 1" and odd: "x \<in> zOdd" 
    and ab: "zgcd a b = 1" and bc: "zgcd b c = 1" and ca: "zgcd c a = 1"
  hence ba: "zgcd b a = 1" and cb: "zgcd c b = 1" and ac: "zgcd a c = 1" 
    by (auto simp only: zgcd_commute)
  { from ba ca have "zgcd (b*c) a = 1" by (simp only: zgcd_zmult_cancel)
    with abcd have "a*(b*c) = d^(nat x) \<and> zgcd a (b*c) = 1" 
      by (simp add: zgcd_commute)
    with x1 odd have "\<exists> k. a = k^(nat x)" 
      by (auto dest: int_relprime_odd_power_divisors) }
  moreover
  { from ab cb have "zgcd (a*c) b = 1" by (simp only: zgcd_zmult_cancel)
    with abcd have "b*(a*c) = d^(nat x) \<and> zgcd b (a*c) = 1" 
      by (simp add: zgcd_commute ac_simps)
    with x1 odd have "\<exists> l. b = l^(nat x)" 
      by (auto dest: int_relprime_odd_power_divisors) }
  moreover
  { from ac bc have "zgcd (a*b) c = 1" by (simp only: zgcd_zmult_cancel)
    with abcd have "c*(a*b) = d^(nat x) \<and> zgcd c (a*b) = 1" 
      by (simp add: zgcd_commute ac_simps)
    with x1 odd have m: "\<exists> m. c = m^(nat x)" 
      by (auto dest: int_relprime_odd_power_divisors) }
  ultimately show ?thesis by auto
qed

lemma zgcd_1_power_left_distrib: "zgcd a b = 1 \<Longrightarrow> zgcd (a^n) b = 1"
  by (induct n, auto simp add: zgcd_zmult_cancel)

lemma zgcd_1_power_distrib: "zgcd a b = 1 \<Longrightarrow> zgcd (a^n) (b^n) = 1"
proof -
  assume "zgcd a b = 1"
  hence "zgcd (a^n) b = 1" by (rule zgcd_1_power_left_distrib)
  hence "zgcd b (a^n) = 1" by (simp only: zgcd_commute)
  hence "zgcd (b^n) (a^n) = 1" by (rule zgcd_1_power_left_distrib)
  thus "zgcd (a^n) (b^n) = 1" by (simp only: zgcd_commute)
qed

lemma zgcd_power_distrib: "zgcd a b ^ n = zgcd (a^n) (b^n)"
proof cases
  assume "a=0 \<and> b=0"
  thus ?thesis by (auto simp add: power_0_left)
next
  let ?g = "zgcd a b"
  assume "\<not> (a=0 \<and> b=0)"
  hence ab0: "a \<noteq> 0 \<or> b \<noteq> 0" by simp
  hence non0: "zgcd a b \<noteq> 0" "zgcd (a^n) (b^n) \<noteq> 0"
    by (auto simp add: zgcd_def gcd_zero power_eq_0_iff)
  moreover have "zgcd a b \<ge> 0" "zgcd (a^n) (b^n) \<ge> 0" by (simp_all add: zgcd_geq_zero)
  ultimately have "zgcd a b ^ n > 0" "zgcd (a^n) (b^n) > 0"
    unfolding less_le by simp_all
  moreover from ab0 obtain c d where abcd: "a = ?g*c \<and> b = ?g*d \<and> zgcd c d = 1"
    by (frule_tac a="a" in make_zrelprime, auto)
  moreover have "(?g*c)^n = ?g^n * c^n \<and> (?g*d)^n = ?g^n * d^n" 
    by (simp add: power_mult_distrib)
  ultimately have gabcdn: "zgcd (a^n) (b^n) = ?g^n * zgcd (c^n) (d^n)" 
    by (auto simp add: zgcd_zmult_distrib2)
  moreover from abcd have "zgcd (c^n) (d^n) = 1" by (simp only: zgcd_1_power_distrib)
  ultimately show ?thesis by auto
qed

lemma zprime_zdvd_zmult_general: "\<lbrakk> zprime p; p dvd m*n \<rbrakk> \<Longrightarrow> p dvd m \<or> p dvd n"
  apply (case_tac "m \<ge> 0", simp only: zprime_zdvd_zmult)
  apply (subgoal_tac "-m \<ge> 0 \<and> p dvd (-m)*n", subgoal_tac "p dvd -m \<or> p dvd n")
  prefer 2
  apply (rule_tac m="-m" in zprime_zdvd_zmult, auto)
done

lemma zprime_zdvd_power: "\<lbrakk> zprime p; p dvd a^n \<rbrakk> \<Longrightarrow> p dvd a"
  apply (induct n, auto)
  apply (frule_tac m="a" and n="a^n" in zprime_zdvd_zmult_general)
  apply auto
done

lemma zpower_zdvd_mono: "n \<noteq> 0 \<Longrightarrow> (a^n dvd b^n) = (a dvd (b::int))"
proof 
  assume "n \<noteq> 0"
  then obtain m where mn: "n = Suc m" 
    by (frule_tac n="n" in not0_implies_Suc, auto)
  assume "a^n dvd b^n"
  then obtain k where k: "b^n = a^n * k" by (auto simp add: dvd_def)
  moreover have "zgcd (a^n*1) (a^n*k) = \<bar>a^n\<bar> * zgcd 1 k" 
    by (rule_tac k="a^n" in zgcd_zmult_distrib2_abs)
  ultimately have "zgcd (a^n) (b^n) = \<bar>a^n\<bar>" 
    by (auto simp add: zgcd_commute zgcd_1)
  hence "zgcd a b^n = \<bar>a\<bar>^n \<and> zgcd a b \<ge> 0 \<and> \<bar>a\<bar> \<ge> 0" 
    by (simp add: zgcd_power_distrib power_abs zgcd_geq_zero)
  with mn have "\<bar>a\<bar> = zgcd a b" by (auto intro: power_inject_base [of _ m])
  moreover have "zgcd a b dvd b" by (rule zgcd_zdvd2 [of a])
  ultimately have "\<bar>a\<bar> dvd b" by simp
  thus "a dvd b" by simp
next
  assume "a dvd b"
  then obtain k where k: "b = a * k" by (auto simp add: dvd_def)
  hence "b^n = a^n * k^n" by (simp only: power_mult_distrib)
  thus "a^n dvd b^n" by auto
qed

lemma zprime_power_zdvd_cancel_right: 
  "\<lbrakk> zprime p; \<not> p dvd b; p^n dvd a*b \<rbrakk> \<Longrightarrow> p^n dvd a"
proof -
  assume p: "zprime p" and pb: "\<not> p dvd b" 
  hence p1: "p > 1" by (simp add: zprime_def)
  have "!!a. p^n dvd a*b \<longrightarrow> p^n dvd a"
  proof (induct n)
    case 0 thus ?case by auto
  next
    case (Suc n) hence IH: "!!a. p^n dvd a*b \<longrightarrow> p^n dvd a" .
    fix a show "p^Suc n dvd a*b \<longrightarrow> p^Suc n dvd a"
    proof (auto)
      assume ppnab: "p*p^n dvd a*b"
      hence "p dvd a*b" by (auto simp add: dvd_def mult.assoc)
      with p have "p dvd a \<or> p dvd b" by (rule zprime_zdvd_zmult_general)
      with pb have "p dvd a" by simp
      then obtain k where apk: "a = p*k" by (auto simp add: dvd_def)
      with ppnab have "p*p^n dvd p*(k*b)" by (auto simp add: ac_simps)
      with p1 have "p^n dvd k*b" by (auto dest: zdvd_mult_cancel)
      with IH have "p^n dvd k" ..
      with apk show "p*p^n dvd a" by (simp add: mult_dvd_mono)
    qed
  qed
  thus "p^n dvd a*b \<Longrightarrow> p^n dvd a" ..
qed

lemma zprime_power_zdvd_cancel_left: 
  "\<lbrakk> zprime p; \<not> p dvd a; p^n dvd a*b \<rbrakk> \<Longrightarrow> p^n dvd b"
  apply (subgoal_tac "p^n dvd b*a")
  apply (auto dest: zprime_power_zdvd_cancel_right)
  apply (simp add: ac_simps)
done

subsection {* Facts about small powers of integers *}

lemma zadd_power2: "((a::int)+b)^2 = a^2 + 2*a*b + b^2"
  by (simp add: eval_nat_numeral field_simps)

lemma zdiff_power2: "((a::int)-b)^2 = a^2 - 2*a*b + b^2"
  by (simp add: eval_nat_numeral field_simps)

lemma zspecial_product: "((a::int) + b) * (a - b) = a^2 - b^2"
  by (simp add: eval_nat_numeral field_simps)

lemma abs_power2_distrib: "\<bar>a^2\<bar> = \<bar>a::int\<bar>^2" 
  by (simp add: power2_eq_square abs_mult)

lemma power2_eq_iff_abs_eq: "((a::int)^2 = b^2) = (\<bar>a\<bar> = \<bar>b\<bar>)" 
proof
  assume "a^2 = b^2" 
  hence "(a+b)*(a-b) = 0" by (simp add: zspecial_product)
  hence "a=b \<or> a=-b" by auto
  thus "\<bar>a\<bar> = \<bar>b\<bar>" by auto
next
  assume "\<bar>a\<bar> = \<bar>b\<bar>"
  hence "\<bar>a\<bar>^2 = \<bar>b\<bar>^2" by simp
  thus "a^2 = b^2" by (simp only: power2_abs)
qed

lemma power2_eq1_iff: "(a::int)^2 = 1 \<Longrightarrow> \<bar>a\<bar>=1" 
  by (auto simp add: zmult_eq_1_iff power2_eq_square abs_mult)

lemma zadd_power3: "((a::int)+b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3" 
  by (simp add: eval_nat_numeral field_simps)
  
lemma zdiff_power3: "((a::int)-b)^3 = a^3 - 3*a^2*b + 3*a*b^2 - b^3"
  by (simp add: eval_nat_numeral field_simps)

lemma power3_minus: "(-a::int)^3 = -(a^3)"
proof -
  have "(3::int) \<in> zOdd \<and> (3::int) \<ge> 0" by (unfold zOdd_def, auto)
  hence "(-a)^(nat 3) = -(a^(nat 3))" by (simp only: neg_odd_power)
  thus ?thesis by simp
qed

lemma abs_power3_distrib: "\<bar>(x::int)^3\<bar> = \<bar>x\<bar>^3" 
  by (simp add: eval_nat_numeral field_simps abs_mult)

lemma cube_square: "(a::int)*a^2 = a^3" 
  by (simp add: eval_nat_numeral field_simps)

lemma quartic_square_square: "(x^2)^2 = (x::int)^4"
  by (simp add: eval_nat_numeral field_simps)

lemma power2_ge_self: "x^2 \<ge> (x::int)"
proof (cases)
  assume nonpos: "x\<le>0"
  have "0 \<le> x^2" by (rule zero_le_power2)
  with nonpos show ?thesis by (rule order_trans)
next
  assume "\<not> x \<le> 0" hence x1: "x \<ge> 1" by simp
  thus ?thesis
  proof (cases)
    assume "x = 1"
    thus ?thesis by simp
  next
    assume "\<not> x = 1" with x1 have x2: "1<x" by simp
    hence "0<x" by simp
    with x2 have "x*1 < x*x" by (rule zmult_zless_mono2)
    thus ?thesis by (simp only: power2_eq_square)
  qed
qed

end
