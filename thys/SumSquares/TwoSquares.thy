(*  Title:      TwoSquares.thy
    Author:     Roelof Oosterhuis, 2007  Rijksuniversiteit Groningen
*)

section {* Sums of two squares *}

theory TwoSquares
imports "../Fermat3_4/IntNatAux" "~~/src/HOL/Old_Number_Theory/Euler"
begin

text {* Show that $(\frac{-1}{p}) = +1$ for primes $p \equiv 1 \bmod 4$. *}
  
definition
  sum2sq :: "int \<times> int \<Rightarrow> int" where
  "sum2sq = (\<lambda>(a,b). a^2+b^2)"

definition
  is_sum2sq :: "int \<Rightarrow> bool" where
  "is_sum2sq x \<longleftrightarrow> (\<exists> a b. sum2sq(a,b) = x)"

lemma mult_sum2sq: "sum2sq(a,b) * sum2sq(p,q) = 
  sum2sq(a*p+b*q, a*q-b*p)"
  by (unfold sum2sq_def, simp add: eval_nat_numeral field_simps)

lemma is_mult_sum2sq: "is_sum2sq x \<Longrightarrow> is_sum2sq y \<Longrightarrow> is_sum2sq (x*y)"
  by (unfold is_sum2sq_def, auto simp only: mult_sum2sq, blast)

lemma Legendre_1mod4: "zprime (4*m+1) \<Longrightarrow> (Legendre (-1) (4*m+1)) = 1"
proof -
  let ?p = "4*m+1"
  let ?L = "Legendre (-1) ?p"
  assume p: "zprime ?p"
  have "m \<ge> 1"
  proof (rule ccontr)
    assume "\<not> m \<ge> 1" hence "m \<le> 0" by auto
    hence "?p \<le> 1" by auto
    with p show False by (simp add: zprime_def)
  qed
  hence p2: "?p > 2" by simp
  with p have "[?L = (-1)^nat((?p - 1) div 2)] (mod ?p)"
    by (simp only: Euler_Criterion)
  hence "[?L = (-1)^(2*nat m)] (mod ?p)" by (auto simp add: nat_mult_distrib)
  hence "[1 = ?L] (mod ?p)" by (auto simp add: power_mult power2_minus zcong_sym)
  hence "?p dvd 1-?L" by (simp add: zcong_def)
  moreover have "?L=1 \<or> ?L=0 \<or> ?L=-1" by (simp add: Legendre_def)
  ultimately have "?L = 1 \<or> ?p dvd 1 \<or> ?p dvd 2" by auto
  moreover
  { assume "?p dvd 1 \<or> ?p dvd 2"
    with p2 have False by (auto simp add: zdvd_not_zless) }
  ultimately show ?thesis by auto
qed

text {* Use this to prove that such primes can be written as the sum of two squares. *}

lemma qf1_prime_exists: "zprime (4*m+1) \<Longrightarrow> \<exists> x y. x^2 + y^2 = 4*m+1"
proof -
  let ?p = "4*m+1"
  assume p: "zprime ?p"
  hence "Legendre (-1) ?p = 1" by (rule Legendre_1mod4)
  moreover
  { assume "\<not> QuadRes ?p (-1)"
    hence "Legendre (-1) ?p \<noteq> 1" by (unfold Legendre_def, auto) }
  ultimately have "QuadRes ?p (-1)" by auto
  then obtain s1 where s1: "[s1^2 = -1] (mod ?p)" by (auto simp add: QuadRes_def)
  from p have p0: "?p > 0" by (simp add: zprime_def)
  hence "\<exists>! s. 0 \<le> s \<and> s < ?p \<and> [s1 = s] (mod ?p)"
    by (simp only: zcong_zless_unique)
  then obtain s where s0p: "0 \<le> s \<and> s < ?p \<and> [s1 = s] (mod ?p)"
    by auto
  hence "[s^2 = s1^2] (mod ?p)" by (simp only: zcong_sym power2_eq_square zcong_zmult)
  with s1 have s: "[s^2 = -1] (mod ?p)" by (auto dest: zcong_trans)
  hence "?p dvd s^2 - (-1::int)" by (unfold zcong_def, simp)
  moreover have "s^2 -(-1::int) = s^2 + 1" by arith
  ultimately have "?p dvd s^2 + 1" by simp
  then obtain t where t: "s^2 + 1 = ?p*t" by (auto simp add: dvd_def)
  hence "sum2sq(s,1) = ?p*t" by (simp add: sum2sq_def)
  hence qf1pt: "is_sum2sq (?p*t)" by (auto simp add: is_sum2sq_def)
  have t_l_p: "t < ?p"
  proof (rule ccontr)
    assume "\<not> t < ?p" hence "t > ?p - 1" by simp
    with p0 have "?p*(?p - 1) < ?p*t" by (simp only: zmult_zless_mono2)
    also with t have "\<dots> = s^2 + 1" by simp
    also have "\<dots> \<le> ?p*(?p - 1) - ?p + 2"
    proof -
      from s0p have "s \<le> ?p - 1" by (auto simp add: less_le)
      with s0p have "s^2 \<le> (?p - 1)^2" by (simp only: power_mono)
      also have "\<dots> = ?p*(?p - 1) - 1*(?p - 1)" 
        by (simp only: power2_eq_square left_diff_distrib)
      finally show ?thesis by auto
    qed
    finally have "?p < 2" by arith
    with p show False by (unfold zprime_def, auto)
  qed
  have tpos: "t \<ge> 1"
  proof (rule ccontr)
    assume "\<not> t \<ge> 1" hence "t < 1" by auto
    moreover
    { assume "t = 0" with t have "s^2 + 1 = 0" by simp }
     moreover
    { assume "t < 0" 
      with p0 have "?p*t < ?p*0" by (simp only: zmult_zless_mono2)
      with t have "s^2 + 1 < 0" by auto }
    moreover have "s^2 \<ge> 0" by (simp only: zero_le_power2)
    ultimately show False by (auto simp add: less_le)
  qed
  moreover
  { assume "t = 1" 
    with qf1pt have "is_sum2sq ?p" by auto
    hence ?thesis by (unfold is_sum2sq_def sum2sq_def, auto) }
  moreover
  { assume t1: "t > 1" 
    then obtain tn where tn: "tn = (nat t) - 1" and tn0: "tn > 0" by auto
    have "is_sum2sq (?p*(1+ int 0))" (is "?Q 0")
      -- "So, $Q~n =$ there exist $x,y$ such that $x^2+y^2 =(p*(1+ int(n)))$"
    proof (rule ccontr)
      assume nQ1: "\<not> ?Q 0"
      have "(1+int tn) < ?p \<Longrightarrow> \<not> ?Q tn"
      proof (induct tn rule: infinite_descent0)
        case 0 
        from nQ1 show "1+int 0 < ?p \<Longrightarrow> \<not> ?Q 0" by simp
      next
        case (smaller n)
        hence n0: "n > 0" and IH: "1+int n < ?p \<and> ?Q n" by auto
        then obtain x y where xy: "x^2 + y^2 = ?p*(1+int n)"
          by (unfold is_sum2sq_def sum2sq_def, auto)
        let ?n1 = "(1+int n)"
        from n0 have n1pos: "?n1 > 0" by simp
        then obtain r v where rv: "v = x-r*?n1 \<and> 2*\<bar>v\<bar> \<le> ?n1"
          by (frule_tac x="?n1" in best_division_abs, auto)
        from n1pos obtain s w where sw: "w = y-s*?n1 \<and> 2*\<bar>w\<bar> \<le> ?n1"
          by (frule_tac x="?n1" in best_division_abs, auto)
        let ?C = "v^2 + w^2" 
        have "?n1 dvd ?C"
        proof 
          from rv sw have "?C = (x-r*?n1)^2 + (y-s*?n1)^2" by simp
          also have "\<dots> = 
            x^2 + y^2 - 2*x*(r*?n1) - 2*y*(s*?n1) + (r*?n1)^2 + (s*?n1)^2" 
            by (simp only: zdiff_power2)
          also with xy have "\<dots> =
            ?n1*?p - ?n1*(2*x*r) - ?n1*(2*y*s) + ?n1^2*r^2 + ?n1^2*s^2"
            by (simp only: ac_simps power_mult_distrib)
          finally show "?C = ?n1*(?p - 2*x*r - 2*y*s + ?n1*(r^2 + s^2))" 
            by (simp only: power_mult_distrib distrib_left ac_simps
          left_diff_distrib right_diff_distrib power2_eq_square)
        qed
        then obtain m1 where m1: "?C = ?n1*m1" by (auto simp add: dvd_def)
        have mn: "m1 < ?n1" 
        proof (rule ccontr)
          assume "\<not> m1 < ?n1" hence "?n1-m1 \<le> 0" by simp
          hence "4*?n1 - 4*m1 \<le> 0" by simp
          with n1pos have "2*?n1 - 4*m1 < 0" by simp
          moreover from n1pos have "?n1 > 0" by simp
          ultimately have "?n1*(2*?n1 - 4*m1) < ?n1*0" by (simp only: zmult_zless_mono2)
          hence contr: "?n1*(2*?n1- 4*m1) < 0" by simp
          have hlp: "2*\<bar>v\<bar> \<ge> 0 \<and> 2*\<bar>w\<bar> \<ge> 0" by simp
          from m1 have "4*?n1*m1 = 4*v^2 + 4*w^2" by arith
          also have "\<dots> = (2*\<bar>v\<bar>)^2 + (2*\<bar>w\<bar>)^2" 
            by (auto simp add: power2_abs power_mult_distrib)
          also from rv hlp have "\<dots> \<le> ?n1^2 + (2*\<bar>w\<bar>)^2"
            using power_mono [of "2*\<bar>b\<bar>" "1 + int n" 2 for b]
            by auto
          also from sw hlp have "\<dots> \<le> ?n1^2 + ?n1^2"
            using power_mono [of "2*\<bar>b\<bar>" "1 + int n" 2 for b]
            by auto
          finally have "?n1*m1*4 \<le> ?n1*?n1*2" 
            by (simp add: power2_eq_square ac_simps)
          hence "?n1*(2*?n1- 4*m1) \<ge> 0" 
            by (simp only: right_diff_distrib ac_simps)
          hence "?n1*(2*?n1- 4*m1) > -1" by auto
          with contr show False by auto
        qed
        have "(r*v + s*w + m1)^2 + (r*w - s*v)^2 = ?p*m1"
        proof -
          from m1 xy have "(?p*?n1)*?C = (x^2+y^2)*(v^2+w^2)" by simp
          also have "\<dots> = (x*v + y*w)^2 + (x*w - y*v)^2"
            by (simp add: eval_nat_numeral field_simps)
          also with rv sw have "\<dots> = 
            ((r*?n1+v)*v + (s*?n1+w)*w)^2 + ((r*?n1+v)*w - (s*?n1+w)*v)^2"
            by simp
          also have "\<dots> =
             (?n1*(r*v) + ?n1*(s*w) + (v^2+w^2))^2 + (?n1*(r*w) - ?n1*(s*v))^2"
            by (simp add: eval_nat_numeral field_simps)
          also from m1 have "\<dots> = 
             (?n1*(r*v) + ?n1*(s*w) + ?n1*m1)^2 + (?n1*(r*w) - ?n1*(s*v))^2"
            by simp
          finally have 
            "(?p*?n1)*?C = ?n1^2*(r*v + s*w + m1)^2 + ?n1^2*(r*w - s*v)^2"
            by (simp add: eval_nat_numeral field_simps)
          with m1 have 
            "?n1^2*(?p*m1) = ?n1^2*((r*v + s*w + m1)^2 + (r*w - s*v)^2)"
            by (simp only: ac_simps power2_eq_square, simp add: distrib_left)
          hence "?n1^2*(?p*m1 - (r*v+s*w+m1)^2 - (r*w-s*v)^2) = 0"
            by (auto simp add: distrib_left right_diff_distrib)
          moreover from n1pos have "?n1^2 \<noteq> 0" by (simp add: power2_eq_square)
          ultimately show ?thesis by simp
        qed
        hence qf1pm1: "is_sum2sq (?p*m1)" by (unfold is_sum2sq_def sum2sq_def, auto)
        have m1pos: "m1 > 0" 
        proof -
          { assume "v^2 + w^2 = 0"
            moreover
            { assume "v \<noteq> 0"
              hence "v^2 > 0" by (simp add: zero_less_power2)
              moreover have "w^2 \<ge> 0" by (rule zero_le_power2)
              ultimately have "v^2 + w^2 > 0" by arith }
            moreover
            { assume "w \<noteq> 0"
              hence "w^2 > 0" by (simp add: zero_less_power2)
              moreover have "v^2 \<ge> 0" by (rule zero_le_power2)
              ultimately have "v^2 + w^2 > 0" by arith }
            ultimately have "v = 0 \<and> w = 0" by auto
            with rv sw have "?n1 dvd x \<and> ?n1 dvd y" by (unfold dvd_def, auto)
            hence "?n1^2 dvd x^2 \<and> ?n1^2 dvd y^2" by (simp add: zpower_zdvd_mono)
            hence "?n1^2 dvd x^2 + y^2" by (simp only: dvd_add)
            with xy have "?n1*?n1 dvd ?n1*?p" 
              by (simp only: power2_eq_square ac_simps)
            moreover from n1pos have "?n1 \<noteq> 0" by simp
            ultimately have "?n1 dvd ?p" by (rule zdvd_mult_cancel)
            with n1pos have "?n1 \<ge> 0 \<and> ?n1 dvd ?p" by simp
            with p have "?n1 = 1 \<or> ?n1 = ?p" by (unfold zprime_def, blast)
            with IH have "?Q 0" by auto
            with nQ1 have False by simp }
          moreover
          { assume "v^2 + 1*w^2 \<noteq> 0"
            moreover have "v^2 + w^2 \<ge> 0"
            proof -
              have "v^2 \<ge> 0 \<and> w^2 \<ge> 0" by (auto simp only: zero_le_power2)
              thus ?thesis by arith
            qed
            ultimately have vwpos: "v^2 + w^2 > 0" by arith
            with m1 have "m1 \<noteq> 0" by auto
            moreover have "m1 \<ge> 0"
            proof (rule ccontr)
              assume "\<not> m1 \<ge> 0" hence "m1 < 0" by simp
              with n1pos have "?n1*m1 < ?n1*0" by (simp only: zmult_zless_mono2)
              with m1 vwpos show False by simp
            qed
            ultimately have ?thesis "m1 > 0" by auto }
          ultimately show ?thesis by auto
        qed
        hence "1 + int((nat m1) - 1) = m1" by arith
        with qf1pm1 have Qm1: "?Q ((nat m1) - 1)" by auto
        then obtain mm where tmp: "mm = (nat m1) - 1 \<and> ?Q mm" by auto
        moreover have "mm<n"
        proof -
          from tmp mn m1pos have "int mm < int n" by arith
          thus ?thesis by arith
        qed
        moreover with IH have "1 + int mm < ?p" by auto
        ultimately show "\<exists> m. m<n \<and> \<not> (1 + int m < ?p \<longrightarrow> \<not> ?Q m)" by auto
      qed
      moreover from tn tpos t_l_p have "1 + int tn < ?p \<and> tn = nat t- 1" 
        by arith
      ultimately have "\<not> ?Q ((nat t) - 1)" by simp
      moreover from tpos have "1 + int ((nat t) - 1) = t" by arith
      ultimately have "\<not> is_sum2sq (?p*t)" by auto
      with qf1pt show False by simp
    qed
    hence ?thesis by (unfold is_sum2sq_def sum2sq_def, auto) }
  ultimately show ?thesis by (auto simp add: less_le)
qed

end
