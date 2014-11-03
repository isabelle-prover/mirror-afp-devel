(*  Title:      Fermat4.thy
    Author:     Roelof Oosterhuis
                2007  Rijksuniversiteit Groningen
*)

section {* Pythagorean triples and Fermat's last theorem, case $n=4$ *}

theory Fermat4
imports Main IntNatAux
begin

text {* Proof of Fermat's last theorem for the case $n=4$: $$\forall x,y,z:~x^4 + y^4 = z^4 \Longrightarrow xyz=0.$$ *}

lemma nat_power2_add: "((a::nat)+b)^2 = a^2 + b^2 + 2*a*b"
  by (fact power2_sum)
(* 
NB: this lemma is quite slow, maybe use more steps *)
lemma nat_power2_diff: "a \<ge> (b::nat) \<Longrightarrow> (a-b)^2 = a^2 + b^2 - 2*a*b"
proof -
  assume a_ge_b: "a \<ge> b"
  hence a2_ge_b2: "a^2 \<ge> b^2" by (simp only: power_mono)
  from a_ge_b have ab_ge_b2: "a*b \<ge> b^2" by (simp add: power2_eq_square)
  have "b*(a-b) + (a-b)^2 = a*(a-b)" by (simp add: power2_eq_square diff_mult_distrib)
  also have "\<dots> = a*b + a^2 + (b^2 - b^2) - 2*a*b" 
    by (simp add: diff_mult_distrib2 power2_eq_square)
  also with a2_ge_b2 have "\<dots> = a*b + (a^2 - b^2) + b^2 - 2*a*b" by simp
  also with ab_ge_b2 have "\<dots> = (a*b - b^2) + a^2 + b^2 - 2*a*b" by auto
  also have "\<dots> = b*(a-b) + a^2 + b^2 - 2*a*b" 
    by (simp only: diff_mult_distrib2 power2_eq_square mult.commute)
  finally show ?thesis by arith
qed

lemma nat_power_le_imp_le_base: "\<lbrakk> n \<noteq> 0; a^n \<le> b^n \<rbrakk> \<Longrightarrow> (a::nat) \<le> b"
proof -
  assume "n \<noteq> 0" and ab: "a^n \<le> b^n"
  then obtain m where "n = Suc m" by (frule_tac n="n" in not0_implies_Suc, auto)
  with ab have "a \<ge> 0" and "a^Suc m \<le> b^Suc m" and "b \<ge> 0" by auto
  thus ?thesis by (rule_tac n="m" in power_le_imp_le_base)
qed
  
lemma nat_power_inject_base: "\<lbrakk> n \<noteq> 0; a^n = b^n \<rbrakk> \<Longrightarrow> (a::nat) = b"
proof -
  assume "n \<noteq> 0" and ab: "a^n = b^n"
  then obtain m where "n = Suc m" by (frule_tac n="n" in not0_implies_Suc, auto)
  with ab have "a^Suc m = b^Suc m" and "a \<ge> 0" and "b \<ge> 0" by auto
  thus ?thesis by (rule power_inject_base)
qed
  
subsection {* Parametrisation of Pythagorean triples (over $\mathbb{N}$ and $\mathbb{Z}$) *}

theorem nat_euclid_pyth_triples:
  assumes abc: "a^2 + b^2 = c^2" and ab_relprime: "gcd a b=1" and aodd: "odd a"
  shows "\<exists> p q. a = p^2 - q^2 \<and> b = 2*p*q \<and> c = p^2 + q^2 \<and> gcd p q=1"
proof -
  have two0: "(2::nat) \<noteq> 0" by simp
  from abc have a2cb: "a^2 = c^2 - b^2" by arith
  -- "factor $a^2$ in coprime factors $(c-b)$ and $(c+b)$; hence both are squares"
  have a2factor: "a^2 = (c-b)*(c+b)"
  proof -
    have "c*b - c*b = 0" by simp
    with a2cb have "a^2 = c*c + c*b - c*b - b*b" by (simp add: power2_eq_square)
    also have "\<dots> = c*(c+b) - b*(c+b)" 
      by (simp add: add_mult_distrib2 add_mult_distrib mult.commute)
    finally show ?thesis by (simp only: diff_mult_distrib)
  qed
  have a_nonzero: "a \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> a \<noteq> 0" hence "a = 0" by simp
    with aodd have "odd (0::nat)" by simp
    thus False by simp
  qed
  have b_less_c: "b < c"
  proof -
    from abc have "b^2 \<le> c^2" by auto
    with two0 have "b \<le> c" by (rule_tac n="2" in nat_power_le_imp_le_base)
    moreover have"b \<noteq> c"
    proof
      assume "b=c" with a2cb have "a^2 = 0" by simp
      with a_nonzero show False by (simp add: power2_eq_square)
    qed
    ultimately show ?thesis by auto
  qed
  hence b2_le_c2: "b^2 \<le> c^2" by (simp add: power_mono)
  have bc_relprime: "gcd b c = 1"
  proof -
    from b2_le_c2 have cancelb2: "c^2-b^2+b^2 = c^2" by auto
    let ?g = "gcd b c"
    have "?g^2 = gcd (b^2) (c^2)" by (simp only: gcd_power_distrib)
    with cancelb2 have "?g^2 = gcd (b^2) (c^2-b^2+b^2)" by simp
    hence "?g^2 = gcd (b^2) (c^2-b^2)" by simp
    with a2cb have "?g^2 dvd a^2" by (simp only: gcd_dvd2)
    hence "?g dvd a \<and> ?g dvd b" by simp
    hence "?g dvd gcd a b" by (simp only: gcd_greatest)
    with ab_relprime show ?thesis by auto
  qed
  have p2: "prime 2" by (rule two_is_prime)
  have factors_odd: "odd (c-b) \<and> odd (c+b)"
  proof (auto simp only: ccontr)
    assume "even (c-b)" 
    with a2factor have "2 dvd a^2" by (simp only: dvd_mult2)
    with p2 have "2 dvd a" by (rule prime_dvd_power)
    with aodd show False by simp
  next
    assume "even (c+b)"
    with a2factor have "2 dvd a^2" by (simp only: dvd_mult)
    with p2 have "2 dvd a" by (rule prime_dvd_power)
    with aodd show False by simp
  qed
  have cb1: "c-b + (c+b) = 2*c" 
  proof -
    have "c-b + (c+b) = ((c-b)+b)+c" by simp
    also with b_less_c have "\<dots> = (c+b-b)+c" by (simp only: diff_add_assoc2)
    also have "\<dots> = c+c" by simp
    finally show ?thesis by simp
  qed
  have cb2: "2*b + (c-b) = c+b"
  proof -
    have "2*b + (c-b) = b+b + (c - b)" by auto
    also have "\<dots> = b + ((c-b)+b)" by simp
    also with b_less_c have " \<dots> = b + (c+b-b)" by (simp only: diff_add_assoc2)
    finally show ?thesis by simp
  qed
  have factors_relprime: "gcd (c-b) (c+b) =1"
  proof -
    let ?g = "gcd (c-b) (c+b)"
    have cb1: "c-b + (c+b) = 2*c"
    proof -
      have "c-b + (c+b) = ((c-b)+b)+c" by simp
      also with b_less_c have "\<dots> = (c+b-b)+c" by (simp only: diff_add_assoc2)
      also have "\<dots> = c+c" by simp
      finally show ?thesis by simp
    qed
    have "?g = gcd (c-b + (c+b)) (c+b)" by simp
    with cb1 have "?g = gcd (2*c) (c+b)" by (rule_tac a="c-b + (c+b)" in back_subst)
    hence g2c: "?g dvd 2*c" by (simp only: gcd_dvd1)
    have "gcd (c-b) (2*b + (c-b)) = gcd (c-b) (2*b)" by simp
    with cb2 have "?g = gcd (c-b) (2*b)" by (rule_tac a="2*b + (c-b)" in back_subst)
    hence g2b: "?g dvd 2*b" by (simp only: gcd_dvd2)
    with g2c have "?g dvd 2 * gcd b c" by (simp only: gcd_greatest gcd_mult_distrib2)
    with bc_relprime have "?g dvd 2" by simp
    with p2 have g1or2: "?g = 2 \<or> ?g = 1" by (unfold prime_def, auto)
    thus ?thesis
    proof (auto)
      assume "?g = 2" hence "2 dvd ?g" by simp
      hence "2 dvd c-b" by simp
      with factors_odd show False by simp
    qed
  qed
  from a2factor have "(c-b)*(c+b) = a^2" and "(2::nat) >1"  by auto
  with factors_relprime have "\<exists> k. c-b = k^2" by (simp only: nat_relprime_power_divisors)
  then obtain r where r: "c-b = r^2" by auto
  from a2factor have "(c+b)*(c-b) = a^2" and "(2::nat) >1"  by auto
  with factors_relprime have "\<exists> k. c+b = k^2" 
    by (simp only: nat_relprime_power_divisors gcd_commute)
  then obtain s where s: "c+b = s^2" by auto
  -- "now $p := (s+r)/2$ and $q := (s-r)/2$ is our solution"
  have rs_odd: "odd r \<and> odd s"
  proof (auto dest: ccontr)
    assume "even r" hence "2 dvd r"by presburger
    with r have  "2 dvd (c-b)" by (simp only: power2_eq_square dvd_mult)
    with factors_odd show False by auto
  next
    assume "even s" hence "2 dvd s" by presburger
    with s have "2 dvd (c+b)" by (simp only: power2_eq_square dvd_mult)
    with factors_odd show False by auto
  qed
  obtain m where m: "m = s-r" by simp
  from r s have "r^2 \<le> s^2" by arith
  with two0 have "r \<le> s" by (rule_tac n="2" in nat_power_le_imp_le_base)
  with m have m2: "s = r + m" by simp
  have "even m" 
  proof (rule ccontr)
    assume "odd m" with rs_odd and m2 show False by presburger 
  qed
  then obtain q where "m = 2*q" ..
  with m2 have q: "s = r + 2*q" by simp
  obtain p where p: "p = r+q" by simp
  have c: "c = p^2 + q^2"
  proof -
    from cb1 and r and s have "2*c = r^2 + s^2" by simp
    also with q have "\<dots> = 2*r^2+(2*q)^2+2*r*(2*q)"
      by (simp add: nat_power2_add)
    also have "\<dots> = 2*r^2+2^2*q^2+2*2*q*r" by (simp add: power_mult_distrib)
    also have "\<dots> = 2*(r^2+2*q*r+q^2)+2*q^2" by (simp add: power2_eq_square)
    also with p have "\<dots> = 2*p^2+2*q^2" by (simp add: nat_power2_add)
    finally show ?thesis by auto
  qed
  moreover have b: "b = 2*p*q"
  proof -
    from cb2 and r and s have "2*b = s^2 - r^2" by arith
    also with q have "\<dots> = (2*q)^2 + 2*r*(2*q)" by (simp add: nat_power2_add)
    also with p have "\<dots> = 4*q*p" by (simp add: power2_eq_square add_mult_distrib2)
    finally show ?thesis by auto
  qed
  moreover have a: "a = p^2 - q^2"
  proof -
    from p have "p\<ge>q" by simp
    hence p2_ge_q2: "p^2 \<ge> q^2" by (simp only: power_mono)
    from a2cb and b and c have "a^2 = (p^2 + q^2)^2 - (2*p*q)^2" by simp
    also have "\<dots> = (p^2)^2 + (q^2)^2 - 2*(p^2)*(q^2)" 
      by (auto simp add: nat_power2_add power_mult_distrib ac_simps)
    also with p2_ge_q2 have "\<dots> = (p^2 - q^2)^2" by (simp only: nat_power2_diff)
    finally have "a^2 = (p^2 - q^2)^2" by simp
    with two0 show ?thesis by (rule_tac n="2" in nat_power_inject_base)
  qed
  moreover have "gcd p q=1"
  proof -
    let ?k = "gcd p q"
    have "?k dvd p \<and> ?k dvd q" by simp
    with b and a have "?k dvd a \<and> ?k dvd b" 
      by (simp add: power2_eq_square)
    hence "?k dvd gcd a b" by (simp only: gcd_greatest)
    with ab_relprime show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

text {* Now for the case of integers. Based on \textit{nat-euclid-pyth-triples}. *}
  
corollary int_euclid_pyth_triples: "\<lbrakk> zgcd a b = 1; a \<in> zOdd; a^2 + b^2 = c^2 \<rbrakk>
  \<Longrightarrow> \<exists> p q. a = p^2 - q^2 \<and> b = 2*p*q \<and> \<bar>c\<bar> = p^2 + q^2 \<and> zgcd p q=1"
proof -
  assume ab_rel: "zgcd a b = 1" and aodd: "a \<in> zOdd" and abc: "a^2 + b^2 = c^2"
  let ?a = "nat\<bar>a\<bar>"
  let ?b = "nat\<bar>b\<bar>"
  let ?c = "nat\<bar>c\<bar>"
  have ab2_pos: "a^2 \<ge> 0 \<and> b^2 \<ge> 0" by simp
  hence "nat(a^2) + nat(b^2) = nat(a^2 + b^2)" by (simp only: nat_add_distrib)
  with abc have "nat(a^2) + nat(b^2) = nat(c^2)" 
    by (auto simp add: power2_eq_square abs_power2_distrib)
  hence "nat(\<bar>a\<bar>^2) + nat(\<bar>b\<bar>^2) = nat(\<bar>c\<bar>^2)"
    by (simp add: abs_power2_distrib)
  hence new_abc: "?a^2 + ?b^2 = ?c^2"
    by (simp only: nat_mult_distrib power2_eq_square nat_add_distrib)
  moreover from ab_rel have new_ab_rel: "gcd ?a ?b = 1" by (simp add: zgcd_def)
  moreover have new_a_odd: "odd ?a" 
  proof -
    from aodd obtain k where k: "a = 2*k+1" by (unfold zOdd_def, auto)
    show ?thesis
    proof (cases)
      assume apos: "a \<ge> 0" with k have "k\<ge>0" by auto
      with k and apos have "?a = 2*(nat k)+1" by arith
      thus ?thesis by simp
    next
      assume "\<not> a\<ge>0" hence aneg: "a<0" by simp
      with k have k2: "2*(-1-k)\<ge> 0" by simp
      have aux2: "(2::int) \<ge> 0" by simp
      have aux1: "(1::int) \<ge> 0" by simp
      from k and aneg have "\<bar>a\<bar> = 2*(-1-k) + 1" by simp
      with k2 aux1 have "?a = nat (2*(-1-k)) + nat 1"
        by (simp only: nat_add_distrib)
      with aux2 have "?a = (nat 2)*nat(-1-k) + nat 1"
        by (simp only: nat_mult_distrib)
      thus ?thesis by simp
    qed
  qed
  ultimately have 
    "\<exists> p q. ?a = p^2-q^2 \<and> ?b = 2*p*q \<and> ?c = p^2 + q^2 \<and> gcd p q =1" 
    by (rule_tac a="?a" and b = "?b" and c="?c" in nat_euclid_pyth_triples)
  then obtain m and n where mn: 
    "?a = m^2-n^2 \<and> ?b = 2*m*n \<and> ?c = m^2 + n^2 \<and> gcd m n =1" by auto
  have "n^2 \<le> m^2"
  proof (rule ccontr)
    assume "\<not> n^2 \<le> m^2" hence "n^2 > m^2" by simp 
    with mn have "?a = 0" by simp
    with new_a_odd show False by simp
  qed
  moreover from mn have "int ?a = int(m^2 - n^2)" and "int ?b = int(2*m*n)" 
    and "int ?c = int(m^2 + n^2)" by auto
  ultimately have "\<bar>a\<bar> = int(m^2) - int(n^2)" and "\<bar>b\<bar> = int(2*m*n)"
    and "\<bar>c\<bar> = int(m^2) + int(n^2)" by (auto simp only: int_nat_abs_eq_abs zdiff_int)
  hence absabc: "\<bar>a\<bar> = (int m)^2 - (int n)^2 \<and> \<bar>b\<bar> = 2*(int m)*int n
    \<and> \<bar>c\<bar> = (int m)^2 + (int n)^2" by (simp add: power2_eq_square int_mult)
  from mn have mn_rel: "zgcd (int m) (int n) = 1" by (simp add: zgcd_def)
  show "\<exists> p q. a = p^2 - q^2 \<and> b = 2*p*q \<and> \<bar>c\<bar> = p^2 + q^2 \<and> zgcd p q=1" 
    (is "\<exists> p q. ?Q p q")
  proof (cases)
    assume apos: "a \<ge> 0" then obtain p where p: "p = int m" by simp
    hence "\<exists> q. ?Q p q"
    proof (cases)
      assume bpos: "b \<ge> 0" then obtain q where "q = int n" by simp
      with p apos bpos absabc mn_rel have "?Q p q" by simp
      thus ?thesis by (rule exI)
    next
      assume "\<not> b\<ge>0" hence bneg: "b<0" by simp 
      then obtain q where "q = - int n" by simp
      with p apos bneg absabc mn_rel have "?Q p q" by simp
      thus ?thesis by (rule exI)
    qed
    thus ?thesis by (simp only: exI)
  next
    assume "\<not> a\<ge>0" hence aneg: "a<0" by simp 
    then obtain p where p: "p = int n" by simp
    hence "\<exists> q. ?Q p q"
    proof (cases)
      assume bpos: "b \<ge> 0" then obtain q where "q = int m" by simp
      with p aneg bpos absabc mn_rel have "?Q p q" 
        by (simp add: zgcd_commute)
      thus ?thesis by (rule exI)
    next
      assume "\<not> b\<ge>0" hence bneg: "b<0" by simp 
      then obtain q where "q = - int m" by simp
      with p aneg bneg absabc mn_rel have "?Q p q" 
        by (simp add: zgcd_commute ac_simps)
      thus ?thesis by (rule exI)
    qed
    thus ?thesis by (simp only: exI)
  qed
qed

subsection {* Fermat's last theorem, case $n=4$ *}

text {* Core of the proof. Constructs a smaller solution over $\mathbb{Z}$ of $$a^4+b^4=c^2\,\land\,\gcd a b=1\,\land\,abc\ne 0\,\land\,a~{\rm odd}.$$ *}

lemma smaller_fermat4:
  assumes abc: "a^4+b^4=c^2" and abc0: "a*b*c \<noteq> 0" and aodd: "a \<in> zOdd" 
    and ab_relprime: "zgcd a b=1"
  shows 
  "\<exists> p q r. (p^4+q^4=r^2 \<and> p*q*r \<noteq> 0 \<and> p \<in> zOdd \<and> zgcd p q = 1 \<and> r^2 < c^2)"
proof - 
  -- "put equation in shape of a pythagorean triple and obtain $u$ and $v$"
  from ab_relprime have a2b2relprime: "zgcd (a^2) (b^2) = 1" 
    by (simp only: zgcd_1_power_distrib)
  moreover from aodd have "a^2 \<in> zOdd" by (simp only: power_preserves_odd)
  moreover from abc have "(a^2)^2 + (b^2)^2 = c^2" by (simp only: quartic_square_square)
  ultimately obtain u and v where uvabc: 
    "a^2 = u^2-v^2 \<and> b^2 = 2*u*v \<and> \<bar>c\<bar> = u^2 + v^2 \<and> zgcd u v = 1" 
    by (frule_tac a="a^2" in int_euclid_pyth_triples, auto)
  with abc0 have uv0: "u\<noteq>0 \<and> v\<noteq>0" by auto
  have av_relprime: "zgcd a v = 1" 
  proof -
    have "zgcd a v dvd zgcd (a^2) v" 
      by (simp only: zgcd_zdvd_zgcd_zmult power2_eq_square)
    moreover
    from uvabc have "zgcd v (a^2) dvd zgcd (b^2) (a^2)" by (simp only: zgcd_zdvd_zgcd_zmult)
    with a2b2relprime have "zgcd (a^2) v dvd (1::int)" by (simp only: zgcd_commute)
    ultimately have "zgcd a v dvd 1" by (rule dvd_trans)
    hence "\<bar>zgcd a v\<bar>= 1" by auto
    thus ?thesis by (simp add: zgcd_geq_zero)
  qed
  -- "make again a pythagorean triple and obtain $k$ and $l$"
  from uvabc have "a^2 + v^2 = u^2" by simp
  with av_relprime and aodd obtain k l where 
    klavu: "a = k^2-l^2 \<and> v = 2*k*l \<and> \<bar>u\<bar> = k^2+l^2" and kl_rel: "zgcd k l = 1" 
    by (frule_tac a="a" in int_euclid_pyth_triples, auto)
  --"prove $b=2m$ and $kl(k^2 + l^2) = m^2$, for coprime $k$, $l$ and $k^2+l^2$"
  from uvabc have "b^2 \<in> zEven" by (unfold zEven_def, auto)
  hence "b \<in> zEven" by (simp only: power_preserves_even)
  then obtain m where bm: "b = 2*m" by (auto simp only: zEven_def)
  have "\<bar>k\<bar>*\<bar>l\<bar>*\<bar>k^2+l^2\<bar> = m^2"
  proof -  
    from bm have "4*m^2 = b^2" by (simp only: power2_eq_square ac_simps)
    also have "\<dots> = \<bar>b^2\<bar>" by simp
    also with uvabc have "\<dots> = 2*\<bar>v\<bar>*\<bar>\<bar>u\<bar>\<bar>" by (simp add: abs_mult)
    also with klavu have "\<dots> = 2*\<bar>2*k*l\<bar>*\<bar>k^2+l^2\<bar>" by simp
    also have "\<dots> = 4*\<bar>k\<bar>*\<bar>l\<bar>*\<bar>k^2+l^2\<bar>" by (auto simp add: abs_mult)
    finally show ?thesis by simp
  qed
  moreover have "(2::nat) > 1" by auto
  moreover from kl_rel have "zgcd \<bar>k\<bar> \<bar>l\<bar> = 1" by (unfold zgcd_def, auto)
  moreover have "zgcd \<bar>l\<bar> (\<bar>k^2+l^2\<bar>) = 1"
  proof -
    from kl_rel have "zgcd (k*k) l = 1" by (simp only: zgcd_zgcd_zmult)
    hence "zgcd (k*k+l*l) l = 1" by simp
    hence "zgcd l (k^2+l^2)=1" by (simp only: power2_eq_square zgcd_commute)
    thus ?thesis by (unfold zgcd_def, auto)
  qed
  moreover have "zgcd \<bar>k^2+l^2\<bar> \<bar>k\<bar>=1"
  proof -
    from kl_rel have "zgcd l k = 1" by (simp only: zgcd_commute)
    hence "zgcd (l*l) k = 1" by (simp only: zgcd_zgcd_zmult)
    hence "zgcd (l*l+k*k) k = 1" by simp
    hence "zgcd (k^2+l^2) k = 1" by (simp only: ac_simps power2_eq_square)
    thus ?thesis by (unfold zgcd_def, auto)
  qed
  ultimately have 
    "\<exists> x y z. \<bar>\<bar>k\<bar>\<bar> = x^2 \<and> \<bar>\<bar>l\<bar>\<bar> = y^2 \<and> \<bar>\<bar>k^2+l^2\<bar>\<bar> = z^2"
    by (rule int_triple_relprime_power_divisors)
  then obtain \<alpha> \<beta> \<gamma> where albega: 
    "\<bar>k\<bar> = \<alpha>^2 \<and> \<bar>l\<bar> = \<beta>^2 \<and> \<bar>k^2+l^2\<bar> = \<gamma>^2" 
    by auto
  -- "show this is a new solution"
  have "k^2 = \<alpha>^4"
  proof -
    from albega have "\<bar>k\<bar>^2 = (\<alpha>^2)^2" by simp
    thus ?thesis by (simp add: quartic_square_square abs_power2_distrib)
  qed
  moreover have "l^2 = \<beta>^4"
  proof -
    from albega have "\<bar>l\<bar>^2 = (\<beta>^2)^2" by simp
    thus ?thesis by (simp add: quartic_square_square abs_power2_distrib)
  qed
  moreover have gamma2: "k^2 + l^2 = \<gamma>^2"
  proof -
    have "k^2 \<ge> 0 \<and> l^2 \<ge> 0" by simp
    with albega show ?thesis by auto
  qed
  ultimately have newabc: "\<alpha>^4 + \<beta>^4 = \<gamma>^2" by auto 
  from uv0 klavu albega have albega0: "\<alpha> * \<beta> * \<gamma>  \<noteq> 0" by auto
  -- "show the coprimality"
  have alphabeta_relprime: "zgcd \<alpha> \<beta> = 1"
  proof (rule classical)
    let ?g = "zgcd \<alpha> \<beta>"
    assume gnot1: "?g \<noteq> 1"
    have "?g > 1"
    proof -
      have "?g \<noteq> 0"
      proof
        assume "?g=0"
        hence "nat \<bar>\<alpha>\<bar>=0" by (unfold zgcd_def, auto simp add: gcd_zero)
        hence "\<alpha>=0" by arith
        with albega0 show False by simp
      qed
      hence "?g>0" by (auto simp only: zgcd_geq_zero less_le)
      with gnot1 show ?thesis by simp
    qed
    moreover have "?g dvd zgcd k l"
    proof -
      have "?g dvd \<alpha> \<and> ?g dvd \<beta>" by auto
      with albega have "?g dvd \<bar>k\<bar> \<and> ?g dvd \<bar>l\<bar>" 
        by (simp add: power2_eq_square mult.commute)
      hence "?g dvd k \<and> ?g dvd l" by simp
      thus ?thesis by (simp add: zgcd_greatest_iff)
    qed
    ultimately have "zgcd k l \<noteq> 1" by auto
    with kl_rel show ?thesis by auto
  qed
  -- "choose $p$ and $q$ in the right way"
  have "\<exists> p q. p^4 + q^4 = \<gamma>^2 \<and> p*q*\<gamma> \<noteq> 0 \<and> p \<in> zOdd \<and> zgcd p q=1"
  proof -
    have "\<alpha> \<in> zOdd \<or> \<beta> \<in> zOdd"      
    proof (rule ccontr)
      assume "\<not> (\<alpha> \<in> zOdd \<or> \<beta> \<in> zOdd)" 
      hence "\<alpha> \<in> zEven \<and> \<beta> \<in> zEven" by (auto simp add: not_odd_impl_even)
      then have "2 dvd \<alpha> \<and> 2 dvd \<beta>" by (auto simp add: zEven_def)
      then have "2 dvd zgcd \<alpha> \<beta>" by (simp add: zgcd_greatest_iff)
      with alphabeta_relprime show False by auto
    qed
    moreover
    { assume "\<alpha> \<in> zOdd"
      with newabc albega0 alphabeta_relprime obtain p q where 
        "p=\<alpha> \<and> q=\<beta> \<and> p^4 + q^4 = \<gamma>^2 \<and> p*q*\<gamma>  \<noteq> 0 \<and> p \<in> zOdd \<and> zgcd p q=1" 
        by auto
      hence ?thesis by auto }
    moreover
    { assume "\<beta> \<in> zOdd"
      with newabc albega0 alphabeta_relprime obtain p q where 
        "q=\<alpha> \<and> p=\<beta> \<and> p^4 + q^4 = \<gamma>^2 \<and> p*q*\<gamma>  \<noteq> 0 \<and> p \<in> zOdd \<and> zgcd p q=1" 
        by (auto simp add: ac_simps zgcd_commute)
      hence ?thesis by auto }
    ultimately show ?thesis by auto
  qed
  -- "show the solution is smaller"
  moreover have "\<gamma>^2 < c^2"
  proof -
    from gamma2 klavu have "\<gamma>^2 \<le> \<bar>u\<bar>" by simp
    also have "\<dots> \<le> \<bar>u\<bar>^2" by (rule power2_ge_self)
    also have "\<dots> \<le> u^2" by (simp add: abs_power2_distrib)
    also have "\<dots> < u^2 + v^2" 
    proof -
      from uv0 have v2non0: "0 \<noteq> v^2" 
        by simp
      have "0 \<le> v^2" by (rule zero_le_power2)
      with v2non0 have "0 < v^2" by (auto simp add: less_le)
      thus ?thesis by auto
    qed
    also with uvabc have "\<dots> \<le> \<bar>c\<bar>" by auto
    also have "\<dots> \<le> \<bar>c\<bar>^2" by (rule power2_ge_self)
    also have "\<dots> \<le> c^2" by (simp add: abs_power2_distrib)
    finally show ?thesis by simp
  qed
  ultimately show ?thesis by auto
qed

text {* Show that no solution exists, by infinite descent of $c^2$. *}

lemma no_rewritten_fermat4:
  "\<not> (\<exists> a b. (a^4 + b^4 = c^2 \<and> a*b*c \<noteq> 0 \<and> a \<in> zOdd \<and> zgcd a b=1))"
proof (induct c rule: infinite_descent0_measure[where V="\<lambda>c. nat(c^2)"])
  case (0 x)
  have "x^2 \<ge> 0" by (rule zero_le_power2)
  with 0 have "int(nat(x^2)) = 0" by auto
  hence "x = 0" by auto
  thus ?case by auto
next
  case (smaller x)
  then obtain a b where "a^4 + b^4 = x^2" and "a*b*x \<noteq> 0" 
    and "a \<in> zOdd" and "zgcd a b=1" by auto
  hence "\<exists> p q r. (p^4+q^4=r^2 \<and> p*q*r \<noteq> 0 \<and> p \<in> zOdd 
    \<and> zgcd p q=1 \<and> r^2 < x^2)" by (rule smaller_fermat4)
  then obtain p q r where pqr: "p^4 + q^4 = r^2 \<and> p*q*r \<noteq> 0 \<and> p \<in> zOdd 
    \<and> zgcd p q=1 \<and> r^2 < x^2" by auto
  have "r^2 \<ge> 0" and "x^2 \<ge> 0" by (auto simp only: zero_le_power2)
  hence "int(nat(r^2)) = r^2 \<and> int(nat(x^2)) = x^2" by auto
  with pqr have "int(nat(r^2)) < int(nat(x^2))" by auto
  hence "nat(r^2) < nat(x^2)" by (simp only: zless_int)
  with pqr show ?case by auto
qed

text {* The theorem. Puts equation in requested shape. *}

theorem fermat4:
  assumes ass: "(x::int)^4 + y^4 = z^4"
  shows "x*y*z=0"
proof (rule ccontr)
  let ?g = "zgcd x y"
  let ?c = "(z div ?g)^2"
  assume xyz0: "x*y*z \<noteq> 0"
  -- "divide out the g.c.d."
  hence "x \<noteq> 0 \<or> y \<noteq> 0" by simp
  then obtain a b where ab: "x = ?g*a \<and> y = ?g*b \<and> zgcd a b=1" 
    by (frule_tac a="x" in make_zrelprime, auto)
  moreover have abc: "a^4 + b^4 = ?c^2 \<and> a*b*?c \<noteq> 0"
  proof -
    have zgab: "z^4 = ?g^4 * (a^4+b^4)"
    proof -
      from ab ass have "z^4 = (?g*a)^4+(?g*b)^4" by simp
      thus ?thesis by (simp only: power_mult_distrib distrib_left)
    qed
    have cgz: "z^2 = ?c * ?g^2" 
    proof -
      from zgab have "?g^4 dvd z^4" by simp
      hence "?g dvd z" by (simp only: zpower_zdvd_mono)
      hence "(z div ?g)*?g = z" by (simp only: ac_simps dvd_mult_div_cancel)
      with ab show ?thesis by (auto simp only: power2_eq_square ac_simps)
    qed
    with xyz0 have c0: "?c\<noteq>0" by (auto simp add: power2_eq_square)
    from xyz0 have g0: "?g\<noteq>0" by (simp add: zgcd_def gcd_zero)
    have "a^4 + b^4 = ?c^2"
    proof -
      have "?c^2 * ?g^4 = (a^4+b^4)*?g^4"
      proof -
        have "?c^2 * ?g^4 = (?c*?g^2)^2" 
          by (simp only: quartic_square_square power_mult_distrib)
        also with cgz have "\<dots> = (z^2)^2" by simp
        also have "\<dots> = z^4" by (rule quartic_square_square)
        also with zgab have "\<dots> = ?g^4*(a^4+b^4)" by simp
        finally show ?thesis by simp
      qed
      with g0 show ?thesis by auto
    qed
    moreover from ab xyz0 c0 have "a*b*?c\<noteq>0" by auto
    ultimately show ?thesis by simp
  qed
  -- "choose the parity right"
  have "\<exists> p q. p^4 + q^4 = ?c^2 \<and> p*q*?c\<noteq>0 \<and> p \<in> zOdd \<and> zgcd p q=1"
  proof -
    have "a \<in> zOdd \<or> b \<in> zOdd"
    proof (rule ccontr)
      assume "\<not>(a \<in> zOdd \<or> b \<in> zOdd)"
      hence "a \<in> zEven \<and> b \<in> zEven" by (auto simp add: not_odd_impl_even)
      hence "2 dvd a \<and> 2 dvd b" by (auto simp add: zEven_def)
      hence "2 dvd zgcd a b" by (simp add: zgcd_greatest_iff)
      with ab show False by auto
    qed
    moreover
    { assume "a \<in> zOdd"
      then obtain p q where "p = a" and "q = b" and "p \<in> zOdd" by simp
      with ab abc have ?thesis by auto }
    moreover 
    { assume "b \<in> zOdd"
      then obtain p q where "p = b" and "q = a" and "p \<in> zOdd" by simp    
      with ab abc have 
        "p^4 + q^4 = ?c^2 \<and> p*q*?c\<noteq>0 \<and> p \<in> zOdd \<and> zgcd p q=1" 
        by (auto simp add: zgcd_commute mult.commute)
      hence ?thesis by auto }
    ultimately show ?thesis by auto
  qed
  -- "show contradiction using the earlier result"
  thus False by (auto simp only: no_rewritten_fermat4)
qed

corollary fermat_mult4:
  assumes xyz: "(x::int)^n + y^n = z^n" and n: "4 dvd n"
  shows "x*y*z=0"
proof -
  from n obtain m where "n = m*4" by (auto simp only: ac_simps dvd_def)
  with xyz have "(x^m)^4 + (y^m)^4 = (z^m)^4" by (simp only: power_mult)
  hence "(x^m)*(y^m)*(z^m) = 0" by (rule fermat4)
  thus ?thesis by auto
qed

end
