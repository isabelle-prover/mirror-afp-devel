(*  Title:      QuadForm.thy
    Author:     Roelof Oosterhuis
                2007  Rijksuniversiteit Groningen
*)

section {* The quadratic form $x^2 + Ny^2$ *}

theory QuadForm
imports
  "~~/src/HOL/Old_Number_Theory/Quadratic_Reciprocity"
  IntNatAux
begin

text {* Shows some properties of the quadratic form $x^2+Ny^2$, such as how to multiply and divide them. The second part focuses on the case $N=3$ and is used in the proof of the case $n=3$ of Fermat's last theorem. The last part -- not used for FLT3 -- shows which primes can be written as $x^2 + 3y^2$. *}

subsection {* Definitions and auxiliary results *}

definition
  is_qfN :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_qfN A N \<longleftrightarrow> (\<exists> x y. A = x^2 + N*y^2)"

definition
  is_cube_form :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_cube_form a b \<longleftrightarrow> (\<exists> p q. a = p^3 - 9*p*q^2 \<and> b = 3*p^2*q - 3*q^3)"

lemma abs_eq_impl_unitfactor: "\<bar>a::int\<bar> = \<bar>b\<bar> \<Longrightarrow> \<exists> u. a = u*b \<and> \<bar>u\<bar>=1"
proof -
  assume "\<bar>a\<bar> = \<bar>b\<bar>"
  hence "a = 1*b \<or> a = (-1)*b" by arith
  then obtain u where "a = u*b \<and> (u=1 \<or> u=-1)" by blast
  thus ?thesis by auto
qed

lemma zprime_3: "zprime 3"
proof (auto simp add: zprime_def)
  fix m::int assume m0: "m \<ge> 0" and mdvd3: "m dvd 3" and mn3: "m \<noteq> 3"
  hence "m \<le> 3" by (auto simp only: zdvd_imp_le)
  with mn3 have "m < 3" by simp
  moreover from mdvd3 have "m \<noteq> 0" by auto
  moreover with m0 have "m > 0" by simp
  ultimately have "m = 1 \<or> m = 2" by auto
  moreover from mdvd3 have "m = 2 \<Longrightarrow> False" by arith
  ultimately show "m = 1" by auto
qed

(*lemma zgcd_not_1_impl_common_primedivisor:
  "zgcd a b \<noteq> 1 \<Longrightarrow> \<exists> p. zprime p \<and> p dvd a \<and> p dvd b"
  by (auto simp add: zgcd1_iff_no_common_primedivisor)

*)
subsection {* Basic facts if $N \ge 1$ *}

lemma qfN_pos: "\<lbrakk> N \<ge> 1; is_qfN A N \<rbrakk> \<Longrightarrow> A \<ge> 0"
proof -
  assume N: "N \<ge> 1" and "is_qfN A N"
  then obtain a b where ab: "A = a^2 + N*b^2" by (auto simp add: is_qfN_def)
  have "N*b^2 \<ge> 0"
  proof (cases)
    assume "b = 0" thus ?thesis by auto
  next
    assume "\<not> b = 0" hence " b^2 > 0" by (simp add: zero_less_power2)
    moreover from N have "N>0" by simp
    ultimately have "N*b^2 > N*0" by (auto simp only: zmult_zless_mono2)
    thus ?thesis by auto
  qed
  with ab have "A \<ge> a^2" by auto
  moreover have "a^2 \<ge> 0" by (rule zero_le_power2)
  ultimately show ?thesis by arith
qed

lemma qfN_zero: "\<lbrakk> (N::int) \<ge> 1; a^2 + N*b^2 = 0 \<rbrakk> \<Longrightarrow> (a = 0 \<and> b = 0)"
proof -
  assume N: "N \<ge> 1" and abN: "a^2 + N*b^2 = 0"
  show ?thesis
  proof (rule ccontr, auto)
    assume "a \<noteq> 0" hence "a^2 > 0" by (simp add: zero_less_power2)
    moreover have "N*b^2 \<ge> 0"
    proof (cases)
      assume "b = 0" thus ?thesis by auto
    next
      assume "\<not> b = 0" hence " b^2 > 0" by (simp add: zero_less_power2)
      moreover from N have "N>0" by simp
      ultimately have "N*b^2 > N*0" by (auto simp only: zmult_zless_mono2)
      thus ?thesis by auto
    qed
    ultimately have "a^2 + N*b^2 > 0" by arith
    with abN show False by auto
  next
    assume "b \<noteq> 0" hence "b^2>0" by (simp add: zero_less_power2)
    moreover from N have "N>0" by simp
    ultimately have "N*b^2>N*0" by (auto simp only: zmult_zless_mono2)
    hence "N*b^2 > 0" by simp
    moreover have "a^2 \<ge> 0" by (rule zero_le_power2)
    ultimately have "a^2 + N*b^2 > 0" by arith
    with abN show False by auto
  qed
qed

subsection {* Multiplication and division *}

lemma qfN_mult1: "((a::int)^2 + N*b^2)*(c^2 + N*d^2)
  = (a*c+N*b*d)^2 + N*(a*d-b*c)^2"
  by (simp add: eval_nat_numeral field_simps)

lemma qfN_mult2: "((a::int)^2 + N*b^2)*(c^2 + N*d^2)
  = (a*c-N*b*d)^2 + N*(a*d+b*c)^2"
  by (simp add: eval_nat_numeral field_simps)

corollary is_qfN_mult: "is_qfN A N \<Longrightarrow> is_qfN B N \<Longrightarrow> is_qfN (A*B) N"
  by (unfold is_qfN_def, auto, auto simp only: qfN_mult1)

corollary is_qfN_power: "(n::nat) > 0 \<Longrightarrow> is_qfN A N \<Longrightarrow> is_qfN (A^n) N"
  by (induct n, auto, case_tac "n=0", auto simp add: is_qfN_mult)

lemma qfN_div_prime:
  assumes ass: "zprime (p^2+N*q^2) \<and> (p^2+N*q^2) dvd (a^2+N*b^2)"
  shows "\<exists> u v. a^2+N*b^2 = (u^2+N*v^2)*(p^2+N*q^2)
                \<and> (\<exists> e. a = p*u+e*N*q*v \<and> b = p*v - e*q*u \<and> \<bar>e\<bar>=1)"
proof -
  let ?P = "p^2+N*q^2"
  let ?A = "a^2+N*b^2"
  from ass obtain U where U: "?A = ?P*U" by (auto simp only: dvd_def)
  have "\<exists> e. ?P dvd b*p + e*a*q \<and> \<bar>e\<bar> = 1"
  proof -
    have "?P dvd (b*p + a*q)*(b*p - a*q)"
    proof -
      have "(b*p + a*q)*(b*p - a*q)= b^2*?P - q^2*?A"
        by (simp add: eval_nat_numeral field_simps)
      also from U have "\<dots> = (b^2 - q^2*U)*?P" by (simp add: field_simps)
      finally show ?thesis by simp
    qed
    with ass have "?P dvd (b*p + a*q) \<or> ?P dvd (b*p - a*q)"
      by (simp only: zprime_zdvd_zmult_general)
    moreover
    { assume "?P dvd b*p + a*q"
      hence "?P dvd b*p + 1*a*q \<and> \<bar>1\<bar> = (1::int)" by simp }
    moreover
    { assume "?P dvd b*p - a*q"
      hence "?P dvd b*p + (-1)*a*q \<and> \<bar>-1\<bar> = (1::int)" by simp }
    ultimately show ?thesis by blast
  qed
  then obtain v e where v: "b*p + e*a*q = ?P*v" and e: "\<bar>e\<bar> = 1"
    by (auto simp only: dvd_def)
  have "?P dvd a*p - e*N*b*q"
  proof (cases)
    assume e1: "e = 1"
    from U have "U * ?P^2 = ?A * ?P" by (simp add: power2_eq_square)
    also with e1 have "\<dots> = (a*p-e*N*b*q)^2 + N*(b*p+e*a*q)^2"
      by (simp only: qfN_mult2 add.commute mult_1_left)
    also with v have "\<dots> = (a*p-e*N*b*q)^2 + N*v^2*?P^2"
      by (simp only: power_mult_distrib ac_simps)
    finally have "(a*p-e*N*b*q)^2 = ?P^2*(U-N*v^2)"
      by (simp add: ac_simps left_diff_distrib)
    hence "?P^2 dvd (a*p - e*N*b*q)^2" by (rule dvdI)
    thus ?thesis by (simp only: zpower_zdvd_mono)
  next
    assume "\<not> e=1" with e have e1: "e=-1" by auto
    from U have "U * ?P^2 = ?A * ?P" by (simp add: power2_eq_square)
    also with e1 have "\<dots> = (a*p-e*N*b*q)^2 + N*( -(b*p+e*a*q))^2"
      by (simp add: qfN_mult1)
    also have "\<dots> = (a*p-e*N*b*q)^2 + N*(b*p+e*a*q)^2"
      by (simp only: power2_minus)
    also with v have "\<dots> = (a*p-e*N*b*q)^2 + N*v^2*?P^2"
      by (simp only: power_mult_distrib ac_simps)
    finally have "(a*p-e*N*b*q)^2 = ?P^2*(U-N*v^2)"
      by (simp add: ac_simps left_diff_distrib)
    hence "?P^2 dvd (a*p-e*N*b*q)^2" by (rule dvdI)
    thus ?thesis by (simp only: zpower_zdvd_mono)
  qed
  then obtain u where u: "a*p - e*N*b*q = ?P*u" by (auto simp only: dvd_def)
  from e have e2_1: "e*e = 1" by auto
  have a: "a = p*u + e*N*q*v"
  proof -
    have "(p*u + e*N*q*v)*?P = p*(?P*u) + (e*N*q)*(?P*v)"
      by (simp only: distrib_right ac_simps)
    also with v u have "\<dots> = p*(a*p - e*N*b*q) + (e*N*q)*(b*p + e*a*q)"
      by simp
    also have "\<dots> = a*(p^2 + e*e*N*q^2)"
      by (simp add: power2_eq_square distrib_left ac_simps right_diff_distrib)
    also with e2_1 have "\<dots> = a*?P" by simp
    finally have "(a-(p*u+e*N*q*v))*?P = 0" by auto
    moreover from ass have "?P \<noteq> 0" by (unfold zprime_def, auto)
    ultimately show ?thesis by simp
  qed
  moreover have b: "b = p*v-e*q*u"
  proof -
    have "(p*v-e*q*u)*?P = p*(?P*v) - (e*q)*(?P*u)"
      by (simp only: left_diff_distrib ac_simps)
    also with v u have "\<dots> = p*(b*p+e*a*q) - e*q*(a*p-e*N*b*q)" by simp
    also have "\<dots> = b*(p^2 + e*e*N*q^2)"
      by (simp add: power2_eq_square distrib_left ac_simps right_diff_distrib)
    also with e2_1 have "\<dots> = b * ?P" by simp
    finally have "(b-(p*v-e*q*u))*?P = 0" by auto
    moreover from ass have "?P \<noteq> 0" by (unfold zprime_def, auto)
    ultimately show ?thesis by simp
  qed
  moreover have "?A = (u^2 + N*v^2)*?P"
  proof (cases)
    assume "e=1"
    with a and b show ?thesis by (simp add: qfN_mult1 mult_1_left ac_simps)
  next
    assume "\<not> e=1" with e have "e=-1" by simp
    with a and b show ?thesis by (simp add: qfN_mult2 mult_1_left ac_simps)
  qed
  moreover from e have "\<bar>e\<bar> = 1" .
  ultimately show ?thesis by blast
qed

corollary qfN_div_prime_weak:
  "\<lbrakk> zprime (p^2+N*q^2); (p^2+N*q^2) dvd (a^2+N*b^2) \<rbrakk>
  \<Longrightarrow> \<exists> u v. a^2+N*b^2 = (u^2+N*v^2)*(p^2+N*q^2)"
  apply (subgoal_tac "\<exists> u v. a^2+N*b^2 = (u^2+N*v^2)*(p^2+N*q^2)
    \<and> (\<exists> e. a = p*u+e*N*q*v \<and> b = p*v - e*q*u \<and> \<bar>e\<bar>=1)", blast)
  apply (rule qfN_div_prime, auto)
done

corollary qfN_div_prime_general: "\<lbrakk> zprime P; P dvd A; is_qfN A N; is_qfN P N \<rbrakk>
  \<Longrightarrow> \<exists> Q. A = Q*P \<and> is_qfN Q N"
  apply (subgoal_tac "\<exists> u v. A = (u^2+N*v^2)*P")
  apply (unfold is_qfN_def, auto)
  apply (simp only: qfN_div_prime_weak)
done

lemma qfN_power_div_prime:
  assumes ass: "zprime P \<and> P \<in> zOdd \<and> P dvd A \<and> P^n = p^2+N*q^2
  \<and> A^n = a^2+N*b^2 \<and> zgcd a b=1 \<and> zgcd p (N*q) = 1 \<and> n>0"
  shows "\<exists> u v. a^2+N*b^2 = (u^2 + N*v^2)*(p^2+N*q^2) \<and> zgcd u v=1
                \<and> (\<exists> e. a = p*u+e*N*q*v \<and> b = p*v-e*q*u \<and> \<bar>e\<bar> = 1)"
proof -
  from ass have "P dvd A \<and> n>0" by simp
  hence "P^n dvd A^n" by (simp add: zpower_zdvd_mono)
  then obtain U where U: "A^n = U*P^n" by (auto simp only: dvd_def ac_simps)
  have "\<exists> e. P^n dvd b*p + e*a*q \<and> \<bar>e\<bar> = 1"
  proof -
    have Pn_dvd_prod: "P^n dvd (b*p + a*q)*(b*p - a*q)"
    proof -
      have "(b*p + a*q)*(b*p - a*q) = (b*p)^2 - (a*q)^2" by (rule zspecial_product)
      also have "\<dots> = b^2 * p^2 + b^2*N*q^2 - b^2*N*q^2 - a^2*q^2"
        by (simp add: power_mult_distrib)
      also with ass have "\<dots> = b^2*P^n - q^2*A^n"
        by (simp only: ac_simps distrib_right distrib_left)
      also with U have "\<dots> = (b^2-q^2*U)*P^n" by (simp only: left_diff_distrib)
      finally show ?thesis by (simp add: ac_simps)
    qed
    have "P^n dvd (b*p + a*q) \<or> P^n dvd (b*p - a*q)"
    proof -
      have PdvdPn: "P dvd P^n"
      proof -
        from ass have "\<exists> m. n = Suc m" by (simp add: not0_implies_Suc)
        then obtain m where "n = Suc m" by auto
        hence "P^n = P*(P^m)" by auto
        thus ?thesis by auto
      qed
      have "\<not> P dvd b*p+a*q \<or>  \<not> P dvd b*p-a*q"
      proof (rule ccontr, simp)
        assume "P dvd b*p+a*q \<and> P dvd b*p-a*q"
        hence "P dvd (b*p+a*q)+(b*p-a*q) \<and> P dvd (b*p+a*q)-(b*p-a*q)"
          by (simp only: dvd_add, simp only: dvd_diff)
        hence "P dvd 2*(b*p) \<and> P dvd 2*(a*q)" by (simp only: mult_2, auto)
        with ass have "(P dvd 2 \<or> P dvd b*p) \<and> (P dvd 2 \<or> P dvd a*q)"
          by (simp add: zprime_zdvd_zmult_general)
        hence "P dvd 2 \<or> (P dvd b*p \<and> P dvd a*q)" by auto
        moreover have "\<not> P dvd 2"
        proof (rule ccontr, simp)
          assume pdvd2: "P dvd 2"
          have "P \<le> 2"
          proof (rule ccontr)
            assume "\<not> P \<le> 2" hence Pl2: "P > 2" by simp
            with pdvd2 show False by (simp add: zdvd_not_zless)
          qed
          moreover from ass have "P > 1" by (simp only: zprime_def)
          ultimately have "P=2" by auto
          with ass have "2 \<in> zOdd" by simp
          moreover have "2 \<in> zEven" by (simp add: zEven_def)
          ultimately show False by (simp add: odd_iff_not_even)
        qed
        ultimately have "P dvd b*p \<and> P dvd a*q" by auto
        with ass have "(P dvd b \<or> P dvd p) \<and> (P dvd a \<or> P dvd q)"
          by (auto simp only: zprime_zdvd_zmult_general)
        moreover have "\<not> P dvd p \<and> \<not> P dvd q"
        proof (auto dest: ccontr)
          assume Pdvdp: "P dvd p"
          hence "P dvd p^2" by (simp only: dvd_mult power2_eq_square)
          with PdvdPn have "P dvd P^n-p^2" by (simp only: dvd_diff)
          with ass have "P dvd N*(q*q)" by (simp add: power2_eq_square)
          with ass have "P dvd N \<or> P dvd q" by (auto dest: zprime_zdvd_zmult_general)
          hence "P dvd N*q" by auto
          with Pdvdp have "P dvd zgcd p (N*q)" by (simp add: zgcd_greatest_iff)
          with ass show False by (auto simp add: zprime_def)
        next
          assume "P dvd q"
          hence PdvdNq: "P dvd N*q" by simp
          hence "P dvd N*q*q" by simp
          hence "P dvd N*q^2" by (simp add: power2_eq_square ac_simps)
          with PdvdPn have "P dvd P^n-N*q^2" by (simp only: dvd_diff)
          with ass have "P dvd p*p" by (simp add: power2_eq_square)
          with ass have "P dvd p" by (auto dest: zprime_zdvd_zmult_general)
          with PdvdNq have "P dvd zgcd p (N*q)" by (simp add: zgcd_greatest_iff)
          with ass show False by (auto simp add: zprime_def)
        qed
        ultimately have "P dvd a \<and> P dvd b" by auto
        hence "P dvd zgcd a b" by (simp add: zgcd_greatest_iff)
        with ass show False by (auto simp add: zprime_def)
      qed
      moreover
      { assume "\<not> P dvd b*p+a*q"
        with Pn_dvd_prod and ass have "P^n dvd b*p-a*q"
          by (rule_tac a="b*p+a*q" in zprime_power_zdvd_cancel_left, simp) }
      moreover
      { assume "\<not> P dvd b*p-a*q"
        with Pn_dvd_prod and ass have "P^n dvd b*p+a*q"
          by (rule_tac a="b*p+a*q" in zprime_power_zdvd_cancel_right, simp) }
      ultimately show ?thesis by auto
    qed
    moreover
    { assume "P^n dvd b*p + a*q"
      hence "P^n dvd b*p + 1*a*q \<and> \<bar>1\<bar> = (1::int)" by simp }
    moreover
    { assume "P^n dvd b*p - a*q"
      hence "P^n dvd b*p + (-1)*a*q \<and> \<bar>-1\<bar> = (1::int)" by simp }
    ultimately show ?thesis by blast
  qed
  then obtain v e where v: "b*p + e*a*q = P^n*v" and e: "\<bar>e\<bar> = 1"
    by (auto simp only: dvd_def)
  have "P^n dvd a*p - e*N*b*q"
  proof (cases)
    assume e1: "e = 1"
    from U have "(P^n)^2*U = A^n*P^n" by (simp add: power2_eq_square ac_simps)
    also with e1 ass have "\<dots> = (a*p-e*N*b*q)^2 + N*(b*p+e*a*q)^2"
      by (simp only: qfN_mult2 add.commute mult_1_left)
    also with v have "\<dots> = (a*p-e*N*b*q)^2 + (P^n)^2*(N*v^2)"
      by (simp only: power_mult_distrib ac_simps)
    finally have "(a*p-e*N*b*q)^2 = (P^n)^2*U - (P^n)^2*N*v^2" by simp
    also have "\<dots> = (P^n)^2 * (U - N*v^2)" by (simp only: right_diff_distrib)
    finally have "(P^n)^2 dvd (a*p - e*N*b*q)^2" by (rule dvdI)
    thus ?thesis by (simp only: zpower_zdvd_mono)
  next
    assume "\<not> e=1" with e have e1: "e=-1" by auto
    from U have "(P^n)^2 * U = A^n * P^n" by (simp add: power2_eq_square)
    also with e1 ass have "\<dots> = (a*p-e*N*b*q)^2 + N*( -(b*p+e*a*q))^2"
      by (simp add: qfN_mult1)
    also have "\<dots> = (a*p-e*N*b*q)^2 + N*(b*p+e*a*q)^2"
      by (simp only: power2_minus)
    also with v and ass have "\<dots> = (a*p-e*N*b*q)^2 + N*v^2*(P^n)^2"
      by (simp only: power_mult_distrib ac_simps)
    finally have "(a*p-e*N*b*q)^2 = (P^n)^2*U-(P^n)^2*N*v^2" by simp
    also have "\<dots> = (P^n)^2 * (U - N*v^2)" by (simp only: right_diff_distrib)
    finally have "(P^n)^2 dvd (a*p-e*N*b*q)^2" by (rule dvdI)
    thus ?thesis by (simp only: zpower_zdvd_mono)
  qed
  then obtain u where u: "a*p - e*N*b*q = P^n*u" by (auto simp only: dvd_def)
  from e have e2_1: "e*e = 1" by auto
  have a: "a = p*u + e*N*q*v"
  proof -
    from ass have "(p*u + e*N*q*v)*P^n = p*(P^n*u) + (e*N*q)*(P^n*v)"
      by (simp only: distrib_right ac_simps)
    also with v and u have "\<dots> = p*(a*p - e*N*b*q) + (e*N*q)*(b*p + e*a*q)"
      by simp
    also have "\<dots> = a*(p^2 + e*e*N*q^2)"
      by (simp add: power2_eq_square distrib_left ac_simps right_diff_distrib)
    also with e2_1 and ass have "\<dots> = a*P^n" by simp
    finally have "(a-(p*u+e*N*q*v))*P^n = 0" by auto
    moreover from ass have "P^n \<noteq> 0"
      by (unfold zprime_def, auto simp add: power_eq_0_iff)
    ultimately show ?thesis by auto
  qed
  moreover have b: "b = p*v-e*q*u"
  proof -
    from ass have "(p*v-e*q*u)*P^n = p*(P^n*v) - (e*q)*(P^n*u)"
      by (simp only: left_diff_distrib ac_simps)
    also with v u have "\<dots> = p*(b*p+e*a*q) - e*q*(a*p-e*N*b*q)" by simp
    also have "\<dots> = b*(p^2 + e*e*N*q^2)"
      by (simp add: power2_eq_square distrib_left ac_simps right_diff_distrib)
    also with e2_1 and ass have "\<dots> = b * P^n" by simp
    finally have "(b-(p*v-e*q*u))*P^n = 0" by auto
    moreover from ass have "P^n \<noteq> 0"
      by (unfold zprime_def, auto simp add: power_eq_0_iff)
    ultimately show ?thesis by auto
  qed
  moreover have "A^n = (u^2 + N*v^2)*P^n"
  proof (cases)
    assume "e=1"
    with a and b and ass show ?thesis by (simp add: qfN_mult1 mult_1_left ac_simps)
  next
    assume "\<not> e=1" with e have "e=-1" by simp
    with a and b and ass show ?thesis by (simp add: qfN_mult2 mult_1_left ac_simps)
  qed
  moreover have "zgcd u v=1"
  proof -
    let ?g = "zgcd u v"
    have "?g dvd u \<and> ?g dvd v" by auto
    hence "?g dvd u*p + v*(e*N*q) \<and> ?g dvd v*p - u*(e*q)" by simp
    with a and b have "?g dvd a \<and> ?g dvd b" by (auto simp only: ac_simps)
    hence "?g dvd zgcd a b" by (simp add: zgcd_greatest_iff)
    with ass have "?g = 1 \<or> ?g = -1" by simp
    moreover have "?g \<ge> 0" by (rule zgcd_geq_zero)
    ultimately show ?thesis by auto
  qed
  moreover from e and ass have
    "\<bar>e\<bar> = 1 \<and> A^n = a^2+N*b^2 \<and> P^n = p^2+N*q^2" by simp
  ultimately show ?thesis by auto
qed

lemma qfN_primedivisor_not:
  assumes ass: "zprime P \<and> Q > 0 \<and> is_qfN (P*Q) N \<and> \<not> is_qfN P N"
  shows "\<exists> R. (zprime R \<and> R dvd Q \<and> \<not> is_qfN R N)"
proof (rule ccontr, auto)
  assume ass2: "\<forall> R. R dvd Q \<longrightarrow> zprime R \<longrightarrow> is_qfN R N"
  have "\<exists> ps. primel ps \<and> int (prod ps) = Q"
  proof -
    from ass have "Q=1 \<or> nat(Q) > Suc 0" by auto
    moreover
    { assume "Q=1" hence "primel [] \<and> int (prod []) = Q" by (simp add: primel_def)
      hence ?thesis by auto }
    moreover
    { assume "nat(Q) > Suc 0"
      then have "\<exists> ps. primel ps \<and> prod ps = nat(Q)" by (simp only: factor_exists)
      with ass have ?thesis by auto }
    ultimately show ?thesis by blast
  qed
  then obtain ps where ps: "primel ps \<and> int(prod ps) = Q" by auto
  have ps_lemma: "(primel ps \<and> is_qfN (P*int(prod ps)) N
    \<and> (\<forall>R. (zprime R \<and> R dvd int(prod ps)) \<longrightarrow> is_qfN R N)) \<Longrightarrow> False"
    (is "?B ps \<Longrightarrow> False")
  proof (induct ps)
    case Nil hence "is_qfN P N" by simp
    with ass show False by simp
  next
    case (Cons p ps)
    hence ass3: "?B ps \<Longrightarrow> False"
      and IH: "?B (p#ps)" by simp_all
    hence p: "zprime (int p)" and "int p dvd int(prod(p#ps))"
      by (auto simp add: primel_def prime_impl_zprime_int int_mult)
    moreover with IH have pqfN: "is_qfN (int p) N"
      and "int p dvd P*int(prod(p#ps))" and "is_qfN (P*int(prod(p#ps))) N"
      by auto
    ultimately obtain S where S: "P*int(prod(p#ps)) = S*(int p) \<and> is_qfN S N"
      using qfN_div_prime_general by blast
    hence "(int p)*(P* int(prod ps) - S) = 0" by (auto simp add: int_mult)
    with p S have "is_qfN (P*int(prod ps)) N" by (auto simp add: zprime_def)
    moreover from IH have "primel ps" by (simp add: primel_def)
    moreover from IH have "\<forall> R. zprime R \<and> R dvd int(prod ps) \<longrightarrow> is_qfN R N"
      by (auto simp add: int_mult)
    ultimately have "?B ps" by simp
    with ass3 show False by simp
  qed
  with ps ass2 ass show False by auto
qed

lemma qfN_oddprime_cube:
  "\<lbrakk> zprime (p^2+N*q^2); (p^2+N*q^2) \<in> zOdd; p \<noteq> 0; N \<ge> 1 \<rbrakk>
  \<Longrightarrow> \<exists> a b. (p^2+N*q^2)^3 = a^2 + N*b^2 \<and> zgcd a (N*b)=1"
proof -
  let ?P = "p^2+N*q^2"
  assume P: "zprime ?P" and Podd: "?P \<in> zOdd" and p0: "p \<noteq> 0" and N1: "N \<ge> 1"
  have suc23: "3 = Suc 2" by simp
  let ?a = "p*(p^2 - 3*N*q^2)"
  let ?b = "q*(3*p^2 - N*q^2)"
  have abP: "?P^3 = ?a^2 + N*?b^2" by (simp add: eval_nat_numeral field_simps)
  have "zgcd ?b ?a \<noteq>  1 \<Longrightarrow> ?P dvd p"
  proof -
    let ?h = "zgcd ?b ?a"
    assume h1: "?h \<noteq> 1"
    have "?h \<ge> 0" by (rule zgcd_geq_zero)
    hence "?h = 0 \<or> ?h = 1 \<or> ?h > 1" by arith
    with h1 have "?h =0 \<or> ?h >1" by auto
    moreover
    { assume "?h = 0" hence "nat\<bar>?b\<bar> = 0 \<and> nat\<bar>?a\<bar> = 0"
        by (unfold zgcd_def, auto simp add: gcd_zero)
      hence "?a = 0 \<and> ?b = 0" by arith
      with abP have "?P^3 = 0" by auto
      with P have False by (unfold zprime_def, auto)
      hence ?thesis by simp }
    moreover
    { assume "?h > 1" hence "\<exists> g. zprime g \<and> g dvd ?h" by (rule zprime_factor_exists)
      then obtain g where g: "zprime g \<and> g dvd ?h" by blast
      hence "g dvd ?b \<and> g dvd ?a" by (simp add: zgcd_greatest_iff)
      with g have g1: "g dvd q \<or> g dvd 3*p^2-N*q^2"
        and g2: "g dvd p \<or> g dvd p^2 - 3*N*q^2"
        by (auto simp add: zprime_zdvd_zmult_general)
      from g have gpos: "g \<ge> 0" by (auto simp only: zprime_def)
      have "g dvd ?P"
      proof (cases)
        assume "g dvd q"
        hence gNq: "g dvd N*q^2" by (auto simp add: dvd_def power2_eq_square)
        show ?thesis
        proof (cases)
          assume gp: "g dvd p"
          hence "g dvd p^2" by (auto simp add: dvd_def power2_eq_square)
          with gNq show ?thesis by auto
        next
          assume "\<not> g dvd p" with g2 have "g dvd p^2 - 3*N*q^2" by auto
          moreover from gNq have "g dvd 4*(N*q^2)" by (rule dvd_mult)
          ultimately have "g dvd p^2 - 3*(N*q^2) + 4*(N*q^2)"
            by (simp only: ac_simps dvd_add)
          moreover have "p^2 - 3*(N*q^2)+4*(N*q^2) = p^2 + N*q^2" by arith
          ultimately show ?thesis by simp
        qed
      next
        assume "\<not> g dvd q" with g1 have gpq: "g dvd 3*p^2-N*q^2" by simp
        show ?thesis
        proof (cases)
          assume "g dvd p"
          hence "g dvd 4*p^2" by (auto simp add: dvd_def power2_eq_square)
          with gpq have " g dvd 4*p^2 - (3*p^2 - N*q^2)" by (simp only: dvd_diff)
          moreover have "4*p^2 - (3*p^2 - N*q^2) = p^2 + N*q^2" by arith
          ultimately show ?thesis by simp
        next
          assume "\<not> g dvd p" with g2 have "g dvd p^2 - 3*N*q^2" by auto
          with gpq have "g dvd 3*p^2-N*q^2 - (p^2 - 3*N*q^2)"
            by (simp only: dvd_diff)
          moreover have "3*p^2-N*q^2 - (p^2 - 3*N*q^2) = 2*?P" by auto
          ultimately have "g dvd 2*?P" by simp
          with g have "g dvd 2 \<or> g dvd ?P" by (simp only: zprime_zdvd_zmult)
          moreover have "\<not> g dvd 2"
          proof (rule ccontr, simp)
            assume gdvd2: "g dvd 2"
            have "g \<le> 2"
            proof (rule ccontr)
              assume "\<not> g \<le> 2" hence "g > 2" by simp
              moreover have "(0::int) < 2" by auto
              ultimately have "\<not> g dvd 2" by (auto simp only: zdvd_not_zless)
              with gdvd2 show False by simp
            qed
            moreover from g have "g \<ge> 2" by (simp add: zprime_def)
            ultimately have "g = 2" by auto
            with g have "2 dvd ?a \<and> 2 dvd ?b" by (auto simp add: zgcd_greatest_iff)
            hence "2 dvd ?a^2 \<and> 2 dvd N*?b^2"
              by (simp add: power2_eq_square)
            with abP have "2 dvd ?P^3" by (simp only: dvd_add)
            hence "?P^3 \<in> zEven" by (auto simp add: dvd_def zEven_def)
            moreover have "?P^3 \<in> zOdd"
            proof -
              from Podd have "?P*?P^2 \<in> zOdd"
                by (simp only: odd_times_odd power2_eq_square)
              thus ?thesis by (simp only: cube_square)
            qed
            ultimately show False by (auto simp only: odd_iff_not_even)
          qed
          ultimately show ?thesis by simp
        qed
      qed
      with P gpos have "g = 1 \<or> g = ?P" by (auto simp only: zprime_def)
      with g have "g = ?P" by (simp add: zprime_def)
      with g have Pab: "?P dvd ?a \<and> ?P dvd ?b" by (auto simp add: zgcd_greatest_iff)
      have ?thesis
      proof -
        from Pab P have "?P dvd p \<or> ?P dvd p^2- 3*N*q^2"
          by (auto simp add: zprime_zdvd_zmult_general)
        moreover
        { assume "?P dvd p^2 - 3*N*q^2"
          moreover have "?P dvd 3*(p^2 + N*q^2)"
            by (auto simp only: dvd_refl dvd_mult)
          ultimately have "?P dvd p^2- 3*N*q^2 + 3*(p^2+N*q^2)"
            by (simp only: dvd_add)
          hence "?P dvd 4*p^2" by auto
          with P have "?P dvd 4 \<or> ?P dvd p^2"
            by (simp only: zprime_zdvd_zmult_general)
          moreover have "\<not> ?P dvd 4"
          proof (rule ccontr, simp)
            assume Pdvd4: "?P dvd 4"
            have "?P \<le> 4"
            proof (rule ccontr)
              assume "\<not> ?P \<le> 4" hence "?P > 4" by simp
              moreover have "(0::int) < 4" by auto
              ultimately have "\<not> ?P dvd 4" by (auto simp only: zdvd_not_zless)
              with Pdvd4 show False by simp
            qed
            moreover from P have "?P \<ge> 2" by (auto simp add: zprime_def)
            moreover have "?P \<noteq> 2 \<and> ?P \<noteq> 4"
            proof (rule ccontr, simp)
              assume "?P = 2 \<or> ?P = 4" hence "?P \<in> zEven"
                by (auto simp add: zEven_def)
              with Podd show False by (simp add: odd_iff_not_even)
            qed
            ultimately have "?P = 3" by auto
            with Pdvd4 have "(3::int) dvd 4" by simp
            thus False by arith
          qed
          ultimately have "?P dvd p*p" by (simp add: power2_eq_square)
          with P have ?thesis by (auto dest: zprime_zdvd_zmult_general) }
        ultimately show ?thesis by auto
      qed }
    ultimately show ?thesis by blast
  qed
  moreover have "zgcd N ?a \<noteq> 1 \<Longrightarrow> ?P dvd p"
  proof -
    let ?h = "zgcd N ?a"
    assume h1: "?h \<noteq> 1"
    have "?h \<ge> 0" by (rule zgcd_geq_zero)
    hence "?h = 0 \<or> ?h = 1 \<or> ?h > 1" by arith
    with h1 have "?h =0 \<or> ?h >1" by auto
    moreover
    { assume "?h = 0" hence "nat\<bar>N\<bar> = 0 \<and> nat\<bar>?a\<bar> = 0"
        by (unfold zgcd_def, auto simp add: gcd_zero)
      hence "N = 0" by arith
      with N1 have False by auto
      hence ?thesis by simp }
    moreover
    { assume "?h > 1" hence "\<exists> g. zprime g \<and> g dvd ?h" by (rule zprime_factor_exists)
      then obtain g where g: "zprime g \<and> g dvd ?h" by blast
      hence gN: "g dvd N" and "g dvd ?a" by (auto simp add: zgcd_greatest_iff)
      hence "g dvd p*p^2 - N*(3*p*q^2)"
        by (auto simp only: right_diff_distrib ac_simps)
      with gN have "g dvd p*p^2 - N*(3*p*q^2) + N*(3*p*q^2)"
        by (simp only: dvd_add dvd_mult2)
      hence "g dvd p*p^2" by simp
      with g have "g dvd p \<or> g dvd p*p"
        by (simp add: zprime_zdvd_zmult_general power2_eq_square)
      with g have gp: "g dvd p" by (auto dest: zprime_zdvd_zmult_general)
      hence "g dvd p^2" by (simp add: power2_eq_square)
      with gN have gP: "g dvd ?P" by auto
      from g have "g \<ge> 0" by (simp add: zprime_def)
      with gP P have "g = 1 \<or> g = ?P" by (auto simp only: zprime_def)
      with g have "g = ?P" by (auto simp only: zprime_def)
      with gp have ?thesis by simp }
    ultimately show ?thesis by auto
  qed
  moreover have "\<not> ?P dvd p"
  proof (rule ccontr, clarsimp)
    assume Pdvdp: "?P dvd p"
    have "p^2 \<ge> ?P^2"
    proof (rule ccontr)
      assume "\<not> p^2 \<ge> ?P^2" hence pP: "p^2 < ?P^2" by simp
      moreover with p0 have "p^2 > 0" by (simp add: zero_less_power2)
      ultimately have "\<not> ?P^2 dvd p^2" by (simp add: zdvd_not_zless)
      with Pdvdp show False by (simp add: zpower_zdvd_mono)
    qed
    moreover with P have "?P*1 < ?P*?P"
      by (unfold zprime_def, auto simp only: zmult_zless_mono2)
    ultimately have "p^2 > ?P" by (auto simp add: power2_eq_square)
    hence neg: "N*q^2 < 0" by auto
    show False
    proof -
      have "is_qfN (0^2 + N*q^2) N" by (auto simp only: is_qfN_def)
      with N1 have "0^2 +N*q^2 \<ge> 0" by (rule qfN_pos)
      with neg show False by simp
    qed
  qed
  ultimately have "zgcd ?b ?a = 1 \<and> zgcd N ?a = 1" by auto
  hence "zgcd (N*?b) ?a = 1" by (simp only: zgcd_zmult_cancel)
  with abP show ?thesis by (auto simp only: zgcd_commute)
qed

subsection {* Uniqueness ($N>1$)*}

lemma qfN_prime_unique:
  "\<lbrakk> zprime (a^2+N*b^2); N > 1; a^2+N*b^2 = c^2+N*d^2 \<rbrakk>
  \<Longrightarrow> (\<bar>a\<bar> = \<bar>c\<bar> \<and> \<bar>b\<bar> = \<bar>d\<bar>)"
proof -
  let ?P = "a^2+N*b^2"
  assume P: "zprime ?P" and N: "N > 1" and abcdN: "?P = c^2 + N*d^2"
  have mult: "(a*d+b*c)*(a*d-b*c) = ?P*(d^2-b^2)"
  proof -
    have "(a*d+b*c)*(a*d-b*c) = (a^2 + N*b^2)*d^2 - b^2*(c^2 + N*d^2)"
      by (simp add: eval_nat_numeral field_simps)
    with abcdN show ?thesis by (simp add: field_simps)
  qed
  have "?P dvd a*d+b*c \<or> ?P dvd a*d-b*c"
  proof -
    from mult have "?P dvd (a*d+b*c)*(a*d-b*c)" by simp
    with P show ?thesis by (simp add: zprime_zdvd_zmult_general)
  qed
  moreover
  { assume "?P dvd a*d+b*c"
    then obtain Q where Q: "a*d+b*c = ?P*Q" by (auto simp add: dvd_def)
    from abcdN have "?P^2 = (a^2 + N*b^2) * (c^2 + N*d^2)"
      by (simp add: power2_eq_square)
    also have "\<dots> = (a*c-N*b*d)^2 + N*(a*d+b*c)^2" by (rule qfN_mult2)
    also with Q have "\<dots> = (a*c-N*b*d)^2 + N*Q^2*?P^2"
      by (simp add: ac_simps power_mult_distrib)
    also have "\<dots> \<ge> N*Q^2*?P^2" by (simp add: zero_le_power2)
    finally have pos: "?P^2 \<ge> ?P^2*(Q^2*N)" by (simp add: ac_simps)
    have "b^2 = d^2"
    proof (rule ccontr)
      assume "b^2 \<noteq> d^2"
      with P mult Q have "Q \<noteq> 0" by (unfold zprime_def, auto)
      hence "Q^2 > 0" by (simp add: zero_less_power2)
      moreover with N have "Q^2*N > Q^2*1" by (simp only: zmult_zless_mono2)
      ultimately have "Q^2*N > 1" by arith
      moreover with P have "?P^2 > 0" by (simp add: zprime_def zero_less_power2)
      ultimately have "?P^2*1 < ?P^2*(Q^2*N)" by (simp only: zmult_zless_mono2)
      with pos show False by simp
    qed }
  moreover
  { assume "?P dvd a*d-b*c"
    then obtain Q where Q: "a*d-b*c = ?P*Q" by (auto simp add: dvd_def)
    from abcdN have "?P^2 = (a^2 + N*b^2) * (c^2 + N*d^2)"
      by (simp add: power2_eq_square)
    also have "\<dots> = (a*c+N*b*d)^2 + N*(a*d-b*c)^2" by (rule qfN_mult1)
    also with Q have "\<dots> = (a*c+N*b*d)^2 + N*Q^2*?P^2"
      by (simp add: ac_simps power_mult_distrib)
    also have "\<dots> \<ge> N*Q^2*?P^2" by (simp add: zero_le_power2)
    finally have pos: "?P^2 \<ge> ?P^2*(Q^2*N)" by (simp add: ac_simps)
    have "b^2 = d^2"
    proof (rule ccontr)
      assume "b^2 \<noteq> d^2"
      with P mult Q have "Q \<noteq> 0" by (unfold zprime_def, auto)
      hence "Q^2 > 0" by (simp add: zero_less_power2)
      moreover with N have "Q^2*N > Q^2*1" by (simp only: zmult_zless_mono2)
      ultimately have "Q^2*N > 1" by arith
      moreover with P have "?P^2 > 0" by (simp add: zprime_def zero_less_power2)
      ultimately have "?P^2*1 < ?P^2 * (Q^2*N)" by (simp only: zmult_zless_mono2)
      with pos show False by simp
    qed }
  ultimately have bd: "b^2 = d^2" by blast
  moreover with abcdN have "a^2 = c^2" by auto
  ultimately show ?thesis by (auto simp only: power2_eq_iff_abs_eq)
qed

lemma qfN_square_prime:
  assumes ass:
  "zprime (p^2+N*q^2) \<and> N>1 \<and> (p^2+N*q^2)^2 = r^2+N*s^2 \<and> zgcd r s=1"
  shows "\<bar>r\<bar> = \<bar>p^2-N*q^2\<bar> \<and> \<bar>s\<bar> = \<bar>2*p*q\<bar>"
proof -
  let ?P = "p^2 + N*q^2"
  let ?A = "r^2 + N*s^2"
  from ass have P1: "?P > 1" by (simp add: zprime_def)
  from ass have APP: "?A = ?P*?P" by (simp only: power2_eq_square)
  with ass have "zprime ?P \<and> ?P dvd ?A" by (simp add: dvdI)
  then obtain u v e where uve:
    "?A = (u^2+N*v^2)*?P \<and> r = p*u+e*N*q*v \<and> s = p*v - e*q*u \<and> \<bar>e\<bar>=1"
    by (frule_tac p="p" in qfN_div_prime, auto)
  with APP P1 ass have "zprime (u^2+N*v^2) \<and> N>1 \<and> u^2 + N*v^2 = ?P"
    by auto
  hence "\<bar>u\<bar> = \<bar>p\<bar> \<and> \<bar>v\<bar> = \<bar>q\<bar>" by (auto dest: qfN_prime_unique)
  then obtain f g where f: "u = f*p \<and> \<bar>f\<bar> = 1" and g: "v = g*q \<and> \<bar>g\<bar> = 1"
    by (blast dest: abs_eq_impl_unitfactor)
  with uve have "r = f*p*p + (e*g)*N*q*q \<and> s = g*p*q - (e*f)*p*q" by simp
  hence rs: "r = f*p^2 + (e*g)*N*q^2 \<and> s = (g - e*f)*p*q"
    by (auto simp only: power2_eq_square left_diff_distrib)
  moreover have "s \<noteq> 0"
  proof (rule ccontr, simp)
    assume s0: "s=0"
    hence "zgcd r s = \<bar>r\<bar>" by (simp only: zgcd_0)
    with ass have "\<bar>r\<bar> = 1" by simp
    hence "r^2 = 1" by (auto simp add: abs_power2_distrib)
    with s0 have "?A = 1" by simp
    moreover have "?P^2 > 1"
    proof -
      from P1 have "1 < ?P \<and> (0::int) \<le>  1 \<and> (0::nat) < 2" by auto
      hence "?P^2 > 1^2" by (simp only: power_strict_mono)
      thus ?thesis by auto
    qed
    moreover from ass have "?A = ?P^2" by simp
    ultimately show False by auto
  qed
  ultimately have "g \<noteq> e*f" by auto
  moreover from f g uve have "\<bar>g\<bar> = \<bar>e*f\<bar>" by auto
  ultimately have "g = -(e*f)" by arith
  with rs uve have "r = f*(p^2 - N*q^2) \<and> s = (-e*f)*2*p*q"
    by (auto simp add: power2_eq_square right_diff_distrib)
  hence "\<bar>r\<bar> = \<bar>f\<bar> * \<bar>p^2-N*q^2\<bar>
    \<and> \<bar>s\<bar> = \<bar>e\<bar>*\<bar>f\<bar>*\<bar>2*p*q\<bar>"
    by (auto simp add: abs_mult)
  with uve f g show ?thesis by (auto simp only: mult_1_left)
qed

lemma qfN_cube_prime:
  assumes ass: "zprime (p^2 + N*q^2) \<and> N > 1
  \<and> (p^2 + N*q^2)^3 = a^2 + N*b^2 \<and> zgcd a b=1"
  shows "\<bar>a\<bar> = \<bar>p^3- 3*N*p*q^2\<bar> \<and> \<bar>b\<bar> = \<bar>3*p^2*q-N*q^3\<bar>"
proof -
  let ?P = "p^2 + N*q^2"
  let ?A = "a^2 + N*b^2"
  from ass have P1: "?P > 1" by (simp add: zprime_def)
  with ass have APP: "?A = ?P*?P^2" by (auto simp only: cube_square)
  with ass have "zprime ?P \<and> ?P dvd ?A" by (simp add: dvdI)
  then obtain u v e where uve:
    "?A = (u^2+N*v^2)*?P \<and> a = p*u+e*N*q*v \<and> b = p*v-e*q*u \<and> \<bar>e\<bar>=1"
    by (frule_tac p="p" in qfN_div_prime, auto)
  have "zgcd u v=1"
  proof -
    let ?g = "zgcd u v"
    have "?g dvd u \<and> ?g dvd v" by (auto simp add: zgcd_greatest_iff)
    with uve have "?g dvd a \<and> ?g dvd b" by auto
    hence "?g dvd zgcd a b" by (auto simp add: zgcd_greatest_iff)
    with ass have "?g dvd 1" by simp
    moreover have "?g \<ge> 0" by (rule zgcd_geq_zero)
    ultimately show ?thesis by auto
  qed
  with P1 uve APP ass have "zprime ?P \<and> N > 1 \<and> ?P^2 = u^2+N*v^2
    \<and> zgcd u v=1" by (auto simp add: ac_simps)
  hence "\<bar>u\<bar> = \<bar>p^2-N*q^2\<bar> \<and> \<bar>v\<bar> = \<bar>2*p*q\<bar>" by (rule qfN_square_prime)
  then obtain f g where f: "u = f*(p^2-N*q^2) \<and> \<bar>f\<bar> = 1"
    and g: "v = g*(2*p*q) \<and> \<bar>g\<bar> = 1" by (blast dest: abs_eq_impl_unitfactor)
  with uve have "a = p*f*(p^2-N*q^2) + e*N*q*g*2*p*q
    \<and> b = p*g*2*p*q -e*q*f*(p^2-N*q^2)" by auto
  hence ab: "a = f*p*p^2 + -f*N*p*q^2 + 2*e*g*N*p*q^2
    \<and> b = 2*g*p^2*q - e*f*p^2*q + e*f*N*q*q^2"
    by (auto simp add: ac_simps right_diff_distrib power2_eq_square)
  from f have f2: "f^2 = 1" by (auto simp add: abs_power2_distrib)
  from g have g2: "g^2 = 1" by (auto simp add: abs_power2_distrib)
  have "e \<noteq> f*g"
  proof (rule ccontr, simp)
    assume efg: "e = f*g"
    with ab g have "a = f*p*p^2+f*N*p*q^2" by (auto simp add: power2_eq_square)
    hence "a = (f*p)*?P" by (auto simp add: distrib_left ac_simps)
    hence Pa: "?P dvd a" by auto
    from efg f ab have "b = g*p^2*q+g*N*q*q^2" by (auto simp add: power2_eq_square)
    hence "b = (g*q)*?P" by (auto simp add: distrib_left ac_simps)
    hence "?P dvd b" by auto
    with Pa have "?P dvd zgcd a b" by (simp add: zgcd_greatest_iff)
    with ass have "?P dvd 1" by auto
    with P1 show False by auto
  qed
  moreover from f g uve have "\<bar>e\<bar> = \<bar>f*g\<bar>" by auto
  ultimately have "e = -(f*g)" by arith
  with ab f g have "a = f*p*p^2 - 3*f*N*p*q^2 \<and> b = 3*g*p^2*q - g*N*q*q^2"
    by (auto simp add: power2_eq_square)
  hence "a = f*(p^3 - 3*N*p*q^2) \<and> b = g*( 3*p^2*q - N*q^3 )"
    by (auto simp only: right_diff_distrib ac_simps cube_square)
  with f g show ?thesis by (auto simp add: mult_1_left abs_mult)
qed

subsection {* The case $N=3$ *}

lemma qf3_even: "a^2+3*b^2 \<in> zEven \<Longrightarrow> \<exists> B. a^2+3*b^2 = 4*B \<and> is_qfN B 3"
proof -
  let ?A = "a^2+3*b^2"
  assume even: "?A \<in> zEven"
  have "(a \<in> zOdd \<and> b \<in> zOdd) \<or> (a \<in> zEven \<and> b \<in> zEven)"
  proof (rule ccontr, auto dest: not_odd_impl_even)
    assume "a \<notin> zOdd" and "b \<notin> zEven"
    hence "a \<in> zEven \<and> b \<in> zOdd" by (auto simp only: odd_iff_not_even)
    hence "a^2 \<in> zEven \<and> b^2 \<in> zOdd"
      by (auto simp only: power2_eq_square odd_times_odd even_times_either)
    moreover have "3 \<in> zOdd" by (unfold zOdd_def, auto)
    ultimately have "?A \<in> zOdd" by (auto simp add: odd_times_odd even_plus_odd)
    with even show False by (simp add: odd_iff_not_even)
  next
    assume "a \<notin> zEven" and "b \<notin> zOdd"
    hence "a \<in> zOdd \<and> b \<in> zEven" by (auto simp only: odd_iff_not_even)
    hence "a^2 \<in> zOdd \<and> b^2 \<in> zEven"
      by (auto simp only: power2_eq_square odd_times_odd even_times_either)
    moreover hence "b^2*3 \<in> zEven" by (simp only: even_times_either)
    ultimately have "b^2*3+a^2 \<in> zOdd" by (auto simp add: even_plus_odd)
    hence "?A \<in> zOdd" by (simp only: ac_simps ac_simps)
    with even show False by (simp add: odd_iff_not_even)
  qed
  moreover
  { assume "a \<in> zEven \<and> b \<in> zEven"
    then obtain c d where abcd: "a = 2*c \<and> b = 2*d" by (unfold zEven_def, auto)
    hence "?A = 4*(c^2 + 3*d^2)" by (simp add: power_mult_distrib)
    moreover have "is_qfN (c^2+3*d^2) 3" by (unfold is_qfN_def, auto)
    ultimately have ?thesis by blast }
  moreover
  { assume "a \<in> zOdd \<and> b \<in> zOdd"
    then obtain c d where abcd: "a = 2*c+1 \<and> b = 2*d+1"
      by (unfold zOdd_def, auto)
    have "c-d \<in> zOdd \<or> c-d \<in> zEven" by (rule_tac x="c-d" in even_odd_disj)
    moreover
    { assume "c-d \<in> zEven"
      then obtain e where "c-d = 2*e" by (auto simp add: zEven_def)
      with abcd have e1: "a-b = 4*e" by arith
      hence e2: "a+3*b = 4*(e+b)" by auto
      have "4*?A = (a+3*b)^2 + 3*(a-b)^2"
        by (simp add: eval_nat_numeral field_simps)
      also with e1 e2 have "\<dots> = (4*(e+b))^2+3*(4*e)^2" by (simp(no_asm_simp))
      finally have "?A = 4*((e+b)^2 + 3*e^2)" by (simp add: eval_nat_numeral field_simps)
      moreover have "is_qfN ((e+b)^2 + 3*e^2) 3" by (unfold is_qfN_def, auto)
      ultimately have ?thesis by blast }
    moreover
    { assume "c-d \<in> zOdd"
      then obtain e where "c-d = 2*e+1" by (auto simp add: zOdd_def)
      with abcd have e1: "a+b = 4*(e+d+1)" by auto
      hence e2: "a- 3*b = 4*(e+d-b+1)" by auto
      have "4*?A = (a- 3*b)^2 + 3*(a+b)^2"
        by (simp add: eval_nat_numeral field_simps)
      also with e1 e2 have "\<dots> = (4*(e+d-b+1))^2 +3*(4*(e+d+1))^2"
        by (simp (no_asm_simp))
      finally have "?A = 4*((e+d-b+1)^2+3*(e+d+1)^2)"
        by (simp add: eval_nat_numeral field_simps)
      moreover have "is_qfN ((e+d-b+1)^2 + 3*(e+d+1)^2) 3"
        by (unfold is_qfN_def, auto)
      ultimately have ?thesis by blast }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
qed

lemma qf3_even_general: "\<lbrakk> is_qfN A 3; A \<in> zEven \<rbrakk>
  \<Longrightarrow> \<exists> B. A = 4*B \<and> is_qfN B 3"
proof -
  assume "A \<in> zEven" and "is_qfN A 3"
  then obtain a b where "A = a^2 + 3*b^2"
    and "a^2 + 3*b^2 \<in> zEven" by (unfold is_qfN_def, auto)
  thus ?thesis by (auto simp add: qf3_even)
qed

lemma qf3_oddprimedivisor_not:
  assumes ass: "zprime P \<and> P \<in> zOdd \<and> Q>0 \<and> is_qfN (P*Q) 3 \<and> \<not> is_qfN P 3"
  shows "\<exists> R. zprime R \<and> R \<in> zOdd \<and> R dvd Q \<and> \<not> is_qfN R 3"
proof (rule ccontr, simp)
  assume ass2: "\<forall> R. R dvd Q \<longrightarrow> R \<in> zOdd \<longrightarrow> zprime R \<longrightarrow> is_qfN R 3"
  (is "?A Q")
  obtain n::nat where "n = nat Q" by auto
  with ass have n: "Q = int n" by auto
  have "(n > 0 \<and> is_qfN (P*int n) 3 \<and> ?A(int n)) \<Longrightarrow> False" (is "?B n \<Longrightarrow> False")
  proof (induct n rule: less_induct)
    case (less n)
    hence IH: "!!m. m<n \<and> ?B m \<Longrightarrow> False"
      and Bn: "?B n" by auto
    show False
    proof (cases)
      assume odd: "(int n) \<in> zOdd"
      from Bn ass have "zprime P \<and> int n > 0 \<and> is_qfN (P*int n) 3 \<and> \<not> is_qfN P 3"
        by simp
      hence "\<exists> R. zprime R \<and> R dvd int n \<and> \<not> is_qfN R 3"
        by (rule qfN_primedivisor_not)
      then obtain R where R: "zprime R \<and> R dvd int n \<and> \<not> is_qfN R 3" by auto
      moreover with odd have "R \<in> zOdd"
      proof -
        from R obtain U where "int n = R*U" by (auto simp add: dvd_def)
        with odd show ?thesis by (auto dest: odd_mult_odd_prop)
      qed
      moreover from Bn have "?A (int n)" by simp
      ultimately show False by auto
    next
      assume "\<not> (int n) \<in> zOdd"
      hence even: "int n \<in> zEven" by (rule not_odd_impl_even)
      hence "(int n)*P \<in> zEven" by (rule even_times_either)
      with Bn have  "P*int n \<in> zEven \<and> is_qfN (P*int n) 3" by (simp add: ac_simps)
      hence "\<exists> B. P*(int n) = 4*B \<and> is_qfN B 3" by (simp only: qf3_even_general)
      then obtain B where B: "P*(int n) = 4*B \<and> is_qfN B 3" by auto
      hence "2^2 dvd (int n)*P" by (simp add: ac_simps)
      moreover have "\<not> 2 dvd P"
      proof (rule ccontr, simp)
        assume "2 dvd P"
        with ass have "P \<in> zOdd \<and> P \<in> zEven" by (simp add: dvd_def zEven_def)
        thus False by (simp only: even_odd_conj)
      qed
      moreover have "zprime 2" by (rule zprime_2)
      ultimately have "2^2 dvd int n"
        by (rule_tac p="2" in zprime_power_zdvd_cancel_right)
      then obtain im::int where "int n = 4*im" by (auto simp add: dvd_def)
      moreover obtain m::nat where "m = nat im" by auto
      ultimately have m: "n = 4*m" by arith
      with B have "is_qfN (P*int m) 3" by (auto simp add: int_mult)
      moreover from m Bn have "m > 0" by auto
      moreover from m Bn have "?A (int m)"
        by (auto simp add: int_mult)
      ultimately have Bm: "?B m" by simp
      from Bn m have "m < n" by arith
      with IH Bm show False by auto
    qed
  qed
  with ass ass2 n show False by auto
qed

lemma qf3_oddprimedivisor:
  "\<lbrakk> zprime P; P \<in> zOdd; zgcd a b=1; P dvd (a^2+3*b^2) \<rbrakk>
  \<Longrightarrow> is_qfN P 3"
proof(induct P arbitrary:a b rule:infinite_descent0_measure[where V="\<lambda>P. nat\<bar>P\<bar>"])
  case (0 x)
  moreover hence "x = 0" by arith
  ultimately show ?case by (simp add: zprime_def)
next
  case (smaller x)
  then obtain a b where abx: "zprime x \<and> x \<in> zOdd \<and> zgcd a b=1
    \<and> x dvd (a^2+3*b^2) \<and> \<not> is_qfN x 3" by auto
  then obtain M where M: "a^2+3*b^2 = x*M" by (auto simp add: dvd_def)
  let ?A = "a^2 + 3*b^2"
  from abx have x0: "x > 0 \<and> x \<in> zOdd" by (simp add: zprime_def)
  then obtain m where "2*\<bar>a-m*x\<bar><x" by (auto dest: best_odd_division_abs)
  then obtain c where cm: "c = a-m*x \<and> 2*\<bar>c\<bar> < x" by auto
  from x0 obtain n where "2*\<bar>b-n*x\<bar><x" by (auto dest: best_odd_division_abs)
  then obtain d where dn: "d = b-n*x \<and> 2*\<bar>d\<bar> < x" by auto
  let ?C = "c^2+3*d^2"
  have C3: "is_qfN ?C 3" by (unfold is_qfN_def, auto)
  have C0: "?C > 0"
  proof -
    have hlp: "(3::int) \<ge> 1" by simp
    have "?C \<ge> 0" by simp
    hence "?C = 0 \<or> ?C > 0" by arith
    moreover
    { assume "?C = 0"
      with hlp have "c=0 \<and> d=0" by (rule qfN_zero)
      with cm dn have "a = m*x \<and> b = n*x" by simp
      hence "x dvd a \<and> x dvd b" by simp
      hence "x dvd zgcd a b" by (simp add: zgcd_greatest_iff)
      with abx have False by (auto simp add: zprime_def) }
    ultimately show ?thesis by blast
  qed
  have "x dvd ?C"
  proof
    have "?C = \<bar>c\<bar>^2 + 3*\<bar>d\<bar>^2" by (simp only: power2_abs)
    also with cm dn have "\<dots> = (a-m*x)^2 + 3*(b-n*x)^2" by simp
    also have "\<dots> =
      a^2 - 2*a*(m*x) + (m*x)^2 + 3*(b^2 - 2*b*(n*x) + (n*x)^2)"
      by (simp only: zdiff_power2)
    also with abx M have "\<dots> =
      x*M - x*(2*a*m + 3*2*b*n) + x^2*(m^2 + 3*n^2)"
      by (simp only: power_mult_distrib distrib_left ac_simps, auto)
    finally show "?C = x*(M - (2*a*m + 3*2*b*n) + x*(m^2 + 3*n^2))"
      by (simp add: power2_eq_square distrib_left right_diff_distrib)
  qed
  then obtain y where y: "?C = x*y" by (auto simp add: dvd_def)
  have yx: "y < x"
  proof (rule ccontr)
    assume "\<not> y < x" hence xy: "x-y \<le> 0" by simp
    have hlp: "2*\<bar>c\<bar> \<ge> 0 \<and> 2*\<bar>d\<bar> \<ge> 0 \<and> (3::nat) > 0" by simp
    from y have "4*x*y = 2^2*c^2 + 3*2^2*d^2" by simp
    hence "4*x*y = (2*\<bar>c\<bar>)^2 + 3*(2*\<bar>d\<bar>)^2"
      by (auto simp add: power2_abs power_mult_distrib)
    with cm dn hlp have "4*x*y < x^2 + 3*(2*\<bar>d\<bar>)^2"
      and "(3::int) > 0 \<and> (2*\<bar>d\<bar>)^2 < x^2"
            using power_strict_mono [of "2*\<bar>b\<bar>" x 2 for b]
      by auto
    hence "x*4*y < x^2 + 3*x^2" by (auto)
    also have "\<dots> = x*4*x" by (simp add: power2_eq_square)
    finally have contr: "(x-y)*(4*x) > 0" by (auto simp add: right_diff_distrib)
    show False
    proof (cases)
      assume "x-y = 0" with contr show False by auto
    next
      assume "\<not> x-y =0" with xy have "x-y < 0" by simp
      moreover from x0 have "4*x > 0" by simp
      ultimately have "4*x*(x-y) < 4*x*0" by (simp only: zmult_zless_mono2)
      with contr show False by auto
    qed
  qed
  have y0: "y > 0"
  proof (rule ccontr)
    assume "\<not> y > 0"
    hence "y \<le> 0" by simp
    moreover have "y \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> y\<noteq>0" hence "y=0" by simp
      with y and C0 show False by auto
    qed
    ultimately have "y < 0" by simp
    with x0 have "x*y < x*0" by (simp only: zmult_zless_mono2)
    with C0 y show False by simp
  qed
  let ?g = "zgcd c d"
  have "c \<noteq> 0 \<or> d \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (c\<noteq>0 \<or> d\<noteq>0)" hence "c=0 \<and> d=0" by simp
    with C0 show False by simp
  qed
  then obtain e f where ef: "c = ?g*e \<and> d = ?g * f \<and> zgcd e f = 1"
    by (frule_tac a="c" in make_zrelprime, auto)
  have g2nonzero: "?g^2 \<noteq> 0"
  proof (rule ccontr, simp)
    assume "c = 0 \<and> d = 0"
    with C0 show False by simp
  qed
  let ?E = "e^2 + 3*f^2"
  have E3: "is_qfN ?E 3" by (unfold is_qfN_def, auto)
  have CgE: "?C = ?g^2 * ?E"
  proof -
    have "?g^2 * ?E = (?g*e)^2 + 3*(?g*f)^2"
      by (simp add: distrib_left power_mult_distrib)
    with ef show ?thesis by simp
  qed
  hence "?g^2 dvd ?C" by (simp add: dvd_def)
  with y have g2dvdxy: "?g^2 dvd y*x" by (simp add: ac_simps)
  moreover have "zgcd x (?g^2) = 1"
  proof -
    let ?h = "zgcd ?g x"
    have "?h dvd ?g" and "?g dvd c" by auto
    hence "?h dvd c" by (rule dvd_trans)
    have "?h dvd ?g" and "?g dvd d" by auto
    hence "?h dvd d" by (rule dvd_trans)
    have "?h dvd x" by simp
    hence "?h dvd m*x" by (rule dvd_mult)
    with `?h dvd c` have "?h dvd c+m*x" by (rule dvd_add)
    with cm have "?h dvd a" by simp
    from `?h dvd x` have "?h dvd n*x" by (rule dvd_mult)
    with `?h dvd d` have "?h dvd d+n*x" by (rule dvd_add)
    with dn have "?h dvd b" by simp
    with `?h dvd a` have "?h dvd zgcd a b" by (simp add: zgcd_greatest_iff)
    with abx have "?h dvd 1" by simp
    hence "?h = 1" by (simp add: zgcd_geq_zero)
    hence "zgcd (?g^2) x = 1" by (rule zgcd_1_power_left_distrib)
    thus ?thesis by (simp only: zgcd_commute)
  qed
  ultimately have "?g^2 dvd y" by (auto dest: zrelprime_zdvd_zmult)
  then obtain w where w: "y = ?g^2 * w" by (auto simp add: dvd_def)
  with CgE y g2nonzero have Ewx: "?E = x*w" by auto
  have "w>0"
  proof (rule ccontr)
    assume "\<not> w>0" hence "w \<le> 0" by auto
    hence "w=0 \<or> w<0" by auto
    moreover
    { assume "w=0" with w y0 have False by auto }
    moreover
    { assume wneg: "w<0"
      have "?g^2 \<ge> 0" by (rule zero_le_power2)
      with g2nonzero have "?g^2 > 0" by arith
      with wneg have "?g^2*w < ?g^2*0" by (simp only: zmult_zless_mono2)
      with w y0 have False by auto }
    ultimately show False by blast
  qed
  have w_le_y: "w \<le> y"
  proof (rule ccontr)
    assume "\<not> w \<le> y"
    hence wy: "w > y" by simp
    have "?g^2 = 1 \<or> ?g^2 > 1"
    proof -
      have "?g^2 \<ge> 0" by (rule zero_le_power2)
      hence "?g^2 =0 \<or> ?g^2 > 0" by auto
      with g2nonzero show ?thesis by arith
    qed
    moreover
    { assume "?g^2 =1" with w wy have False by simp }
    moreover
    { assume g1: "?g^2 >1"
      with `w>0` have "w*1 < w*?g^2" by (auto dest: zmult_zless_mono2)
      with w have "w < y" by (simp add: mult_1_left ac_simps)
      with wy have False by auto }
    ultimately show False by blast
  qed
  from Ewx E3 abx `w>0` have
    "zprime x \<and> x \<in> zOdd \<and> w > 0 \<and> is_qfN (x*w) 3 \<and> \<not> is_qfN x 3" by simp
  then obtain z where z: "zprime z \<and> z \<in> zOdd \<and> z dvd w \<and> \<not> is_qfN z 3"
    by (frule_tac P="x" in qf3_oddprimedivisor_not, auto)
  from Ewx have "w dvd ?E" by simp
  with z have "z dvd ?E" by (auto dest: dvd_trans)
  with z ef have "zprime z \<and> z \<in> zOdd \<and> zgcd e f = 1 \<and> z dvd ?E \<and> \<not> is_qfN z 3"
    by auto
  moreover have "nat\<bar>z\<bar> < nat\<bar>x\<bar>"
  proof -
    have "z \<le> w"
    proof (rule ccontr)
      assume "\<not> z \<le> w" hence "w < z" by auto
      with `w>0` have "\<not> z dvd w" by (rule zdvd_not_zless)
      with z show False by simp
    qed
    with w_le_y yx have "z < x" by simp
    with z have "\<bar>z\<bar> < \<bar>x\<bar>" by (simp add: zprime_def)
    thus ?thesis by auto
  qed
  ultimately show ?case by auto
qed

lemma qf3_cube_prime_impl_cube_form:
  assumes ab_relprime: "zgcd a b = 1" and abP: "P^3 = a^2 + 3*b^2"
  and P: "zprime P \<and> P \<in> zOdd"
  shows "is_cube_form a b"
proof -
  from abP have qfP3: "is_qfN (P^3) 3" by (auto simp only: is_qfN_def)
  have PvdP3: "P dvd P^3" by (simp add: eval_nat_numeral)
  with abP ab_relprime P have qfP: "is_qfN P 3" by (simp only: qf3_oddprimedivisor)
  then obtain p q where pq: "P = p^2 + 3*q^2" by (auto simp only: is_qfN_def)
  with P abP ab_relprime have "zprime (p^2 + 3*q^2) \<and> (3::int) > 1
    \<and> (p^2+3*q^2)^3 = a^2+3*b^2 \<and> zgcd a b=1" by auto
  hence ab: "\<bar>a\<bar> = \<bar>p^3 - 3*3*p*q^2\<bar> \<and> \<bar>b\<bar> = \<bar>3*p^2*q - 3*q^3\<bar>"
    by (rule qfN_cube_prime)
  hence a: "a = p^3 - 9*p*q^2 \<or> a = -(p^3) + 9*p*q^2" by arith
  from ab have b: "b = 3*p^2*q - 3*q^3 \<or> b = -(3*p^2*q) + 3*q^3" by arith
  obtain r s where r: "r = -p" and s: "s = -q"  by simp
  show ?thesis
  proof (cases)
    assume a1: "a = p^3- 9*p*q^2"
    show ?thesis
    proof (cases)
      assume b1: "b = 3*p^2*q - 3*q^3"
      with a1 show ?thesis by (unfold is_cube_form_def, auto)
    next
      assume "\<not> b = 3*p^2*q - 3*q^3"
      with b have "b = - 3*p^2*q + 3*q^3" by simp
      with s have "b = 3*p^2*s - 3*s^3" by (simp add: power3_minus)
      moreover from a1 s have "a = p^3 - 9*p*s^2" by (simp add: power2_minus)
      ultimately show ?thesis by (unfold is_cube_form_def, auto)
    qed
  next
    assume "\<not> a = p^3 - 9*p*q^2"
    with a have "a = -(p^3) + 9*p*q^2" by simp
    with r have ar: "a = r^3 - 9*r*q^2" by (simp add: power3_minus)
    show ?thesis
    proof (cases)
      assume b1: "b = 3*p^2*q - 3*q^3"
      with r have "b = 3*r^2*q - 3*q^3" by (simp add: power2_minus)
      with ar show ?thesis by (unfold is_cube_form_def, auto)
    next
      assume "\<not> b = 3*p^2*q - 3*q^3"
      with b have "b = - 3*p^2*q + 3*q^3" by simp
      with r s have "b = 3*r^2*s - 3*s^3"
        by (simp add: power2_minus power3_minus)
      moreover from ar s have "a = r^3 - 9*r*s^2" by (simp add: power2_minus)
      ultimately show ?thesis by (unfold is_cube_form_def, auto)
    qed
  qed
qed

lemma cube_form_mult: "\<lbrakk> is_cube_form a b; is_cube_form c d; \<bar>e\<bar> = 1 \<rbrakk>
  \<Longrightarrow> is_cube_form (a*c+e*3*b*d) (a*d-e*b*c)"
proof -
  assume ab: "is_cube_form a b" and c_d: "is_cube_form c d" and e: "\<bar>e\<bar> = 1"
  from ab obtain p q where pq: "a = p^3 - 9*p*q^2 \<and> b = 3*p^2*q - 3*q^3"
    by (auto simp only: is_cube_form_def)
  from c_d obtain r s where rs: "c = r^3 - 9*r*s^2 \<and> d = 3*r^2*s - 3*s^3"
    by (auto simp only: is_cube_form_def)
  let ?t = "p*r + e*3*q*s"
  let ?u = "p*s - e*r*q"
  have e2: "e^2=1"
  proof -
    from e have "e=1 \<or> e=-1" by simp
    moreover
    { assume "e=1" hence ?thesis by auto }
    moreover
    { assume "e=-1" hence ?thesis by (simp add: power2_minus) }
    ultimately show ?thesis by blast
  qed
  hence "e*e^2 = e" by simp
  hence e3: "e*1 = e^3" by (simp only: cube_square)
  have "a*c+e*3*b*d = ?t^3 - 9*?t*?u^2"
  proof -
    have "?t^3 - 9*?t*?u^2 = p^3*r^3 + e*9*p^2*q*r^2*s + e^2*27*p*q^2*r*s^2
      + e^3*27*q^3*s^3 - 9*p*p^2*r*s^2 + e*18*p^2*q*r^2*s - e^2*9*p*q^2*(r*r^2)
      - e*27*p^2*q*(s*s^2) + e^2*54*p*q^2*r*s^2 - e*e^2*27*(q*q^2)*r^2*s"
      by (simp add: eval_nat_numeral field_simps)
    also with e2 e3 have "\<dots> =
      p^3*r^3 + e*27*p^2*q*r^2*s + 81*p*q^2*r*s^2 + e*27*q^3*s^3
      - 9*p^3*r*s^2 - 9*p*q^2*r^3 - e*27*p^2*q*s^3 - e*27*q^3*r^2*s"
      by (simp add: cube_square mult_1_left)
    also with pq rs have "\<dots> = a*c + e*3*b*d"
      by (simp only: left_diff_distrib right_diff_distrib ac_simps)
    finally show ?thesis by auto
  qed
  moreover have "a*d-e*b*c = 3*?t^2*?u - 3*?u^3"
  proof -
    have "3*?t^2*?u - 3*?u^3 =
      3*(p*p^2)*r^2*s - e*3*p^2*q*(r*r^2) + e*18*p^2*q*r*s^2
      - e^2*18*p*q^2*r^2*s + e^2*27*p*q^2*(s*s^2) - e*e^2*27*(q*q^2)*r*s^2
      - 3*p^3*s^3 + e*9*p^2*q*r*s^2 - e^2*9*p*q^2*r^2*s + e^3*3*r^3*q^3"
      by (simp add: eval_nat_numeral field_simps)
    also with e2 e3 have "\<dots> = 3*p^3*r^2*s - e*3*p^2*q*r^3 + e*18*p^2*q*r*s^2
      - 18*p*q^2*r^2*s + 27*p*q^2*s^3 - e*27*q^3*r*s^2 - 3*p^3*s^3
      + e*9*p^2*q*r*s^2 - 9*p*q^2*r^2*s + e*3*r^3*q^3"
      by (simp add: cube_square mult_1_left)
    also with pq rs have "\<dots> = a*d-e*b*c"
      by (simp only: left_diff_distrib right_diff_distrib ac_simps)
    finally show ?thesis by auto
  qed
  ultimately show ?thesis by (auto simp only: is_cube_form_def)
qed

lemma qf3_cube_primelist_impl_cube_form: "\<lbrakk> primel ps; int (prod ps) \<in> zOdd \<rbrakk> \<Longrightarrow>
  (!! a b. zgcd a b=1 \<Longrightarrow> a^2 + 3*b^2 = (int(prod ps))^3 \<Longrightarrow> is_cube_form a b)"
proof (induct ps)
  case Nil hence ab1: "a^2 + 3*b^2 = 1" by simp
  have b0: "b=0"
  proof (rule ccontr)
    assume "b\<noteq>0"
    hence "b^2>0" by (simp add: zero_less_power2)
    hence "3*b^2 > 1" by arith
    with ab1 have "a^2 < 0" by arith
    moreover have "a^2 \<ge> 0" by (rule zero_le_power2)
    ultimately show False by auto
  qed
  with ab1 have a1: "(a=1 \<or> a=-1)" by (auto simp add: power2_eq_square zmult_eq_1_iff)
  then obtain p and q where "p=a" and "q=(0::int)" by simp
  with a1 and b0 have "a = p^3 - 9*p*q^2 \<and> b = 3*p^2*q - 3*q^3" by auto
  thus "is_cube_form a b" by (auto simp only: is_cube_form_def)
next
  case (Cons p ps) hence ass: "zgcd a b=1 \<and> int(prod (p#ps)) \<in> zOdd
    \<and> a^2+3*b^2 = int(prod (p#ps))^3 \<and> primel ps \<and> zprime (int p)"
    and IH: "!! u v. zgcd u v=1 \<and> u^2+3*v^2 = int(prod ps)^3
    \<and> int(prod ps) \<in> zOdd \<Longrightarrow> is_cube_form u v"
    by (auto simp add: primel_def prime_impl_zprime_int)
  let ?w = "int (prod (p#ps))"
  let ?X = "int (prod ps)"
  let ?p = "int p"
  have ge3_1: "(3::int) \<ge> 1" by auto
  have pw: "?w = ?p * ?X \<and> ?p \<in> zOdd \<and> ?X \<in> zOdd"
  proof (safe)
    have "prod (p#ps) = p * prod ps" by simp
    thus wpx: "?w = ?p * ?X" by (auto simp only: of_nat_mult [symmetric])
    with ass show "?p \<in> zOdd" by (auto dest: odd_mult_odd_prop)
    from wpx have "?w = ?X*?p" by simp
    with ass show "?X \<in> zOdd" by (metis odd_mult_odd_prop)
  qed
  have "is_qfN ?p 3"
  proof -
    from ass have "a^2+3*b^2 = (?p*?X)^3" by simp
    hence "?p dvd a^2+3*b^2" by (simp add: eval_nat_numeral field_simps)
    moreover from ass have "zprime ?p" and "zgcd a b=1" by simp_all
    moreover from pw have "?p \<in> zOdd" by simp
    ultimately show ?thesis by (simp only: qf3_oddprimedivisor)
  qed
  then obtain \<alpha> \<beta> where alphabeta: "?p = \<alpha>^2 + 3*\<beta>^2"
    by (auto simp add: is_qfN_def)
  have "\<alpha> \<noteq> 0"
  proof (rule ccontr, simp)
    assume "\<alpha> = 0" with alphabeta have "3 dvd ?p" by auto
    with pw have w3: "3 dvd ?w" by (simp only: dvd_mult2)
    then obtain v where "?w = 3*v" by (auto simp add: dvd_def)
    with ass have vab: "27*v^3 = a^2 + 3*b^2" by simp
    hence "a^2 = 3*(9*v^3 - b^2)" by auto
    hence "3 dvd a^2" by (unfold dvd_def, blast)
    moreover have "zprime 3" by (rule zprime_3)
    ultimately have a3: "3 dvd a" by (rule_tac p="3" in zprime_zdvd_power)
    then obtain c where c: "a = 3*c" by (auto simp add: dvd_def)
    with vab have "27*v^3 = 9*c^2 + 3*b^2" by (simp add: power_mult_distrib)
    hence "b^2 = 3*(3*v^3 - c^2)" by auto
    hence "3 dvd b^2" by (unfold dvd_def, blast)
    moreover have "zprime 3" by (rule zprime_3)
    ultimately have "3 dvd b" by (rule_tac p="3" in zprime_zdvd_power)
    with a3 have "3 dvd zgcd a b" by (simp add: zgcd_greatest_iff)
    with ass show False by simp
  qed
  moreover from alphabeta pw ass have
    "zprime (\<alpha>^2 + 3*\<beta>^2) \<and> \<alpha>^2+3*\<beta>^2 \<in> zOdd \<and> (3::int) \<ge> 1" by auto
  ultimately obtain c d where cdp:
    "(\<alpha>^2+3*\<beta>^2)^3 = c^2+3*d^2 \<and> zgcd c (3*d)=1"
    by (blast dest: qfN_oddprime_cube)
  with ass pw alphabeta have "\<exists> u v. a^2+3*b^2 = (u^2 + 3*v^2)*(c^2+3*d^2)
    \<and> zgcd u v=1 \<and> (\<exists> e. a = c*u+e*3*d*v \<and> b = c*v-e*d*u \<and> \<bar>e\<bar> = 1)"
    by (rule_tac A="?w" and n="3" in qfN_power_div_prime, auto)
  then obtain u v e where uve: "a^2+3*b^2 = (u^2+3*v^2)*(c^2+3*d^2)
    \<and> zgcd u v=1 \<and> a = c*u+e*3*d*v \<and> b = c*v-e*d*u \<and> \<bar>e\<bar> = 1" by blast
  moreover have "is_cube_form u v"
  proof -
    have uvX: "u^2+3*v^2 = ?X^3"
    proof -
      from ass have p0: "?p \<noteq> 0" by (simp add: zprime_def)
      from pw have "?p^3*?X^3 = ?w^3" by (simp add: power_mult_distrib)
      also with ass have "\<dots> = a^2+3*b^2" by simp
      also with uve have "\<dots> = (u^2+3*v^2)*(c^2+3*d^2)" by auto
      also with cdp alphabeta have "\<dots> = ?p^3 * (u^2+3*v^2)" by (simp only: ac_simps)
      finally have "?p^3*(u^2+3*v^2-?X^3) = 0" by auto
      with p0 show ?thesis by auto
    qed
    with pw IH uve show ?thesis by simp
  qed
  moreover have "is_cube_form c d"
  proof -
    have "zgcd c d = 1"
    proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
      fix h::int assume "h dvd c" and "h dvd d" and h: "zprime h"
      hence "h dvd c*u + d*(e*3*v) \<and> h dvd c*v-d*(e*u)" by simp
      with uve have "h dvd a \<and> h dvd b" by (auto simp only: ac_simps)
      with ass h show False by (auto simp add: zgcd1_iff_no_common_primedivisor)
    qed
    with pw cdp ass alphabeta show ?thesis
      by (rule_tac P="?p" in qf3_cube_prime_impl_cube_form, auto)
  qed
  ultimately show "is_cube_form a b" by (simp only: cube_form_mult)
qed

lemma qf3_cube_impl_cube_form:
  assumes ass: "zgcd a b=1 \<and> a^2 + 3*b^2 = w^3 \<and> w \<in> zOdd"
  shows "is_cube_form a b"
proof -
  have "\<exists> ps. primel ps \<and> int (prod ps) = w"
  proof -
    have wpos: "w \<ge> 1"
    proof -
      have "b^2 \<ge> 0" by (rule zero_le_power2)
      hence "3*b^2 \<ge> 0" by arith
      moreover have "a^2\<ge>0" by (rule zero_le_power2)
      ultimately have "a^2 + 3*b^2 \<ge> 0" by arith
      with ass have w3pos: "w^3 \<ge> 0" by simp
      have "w\<ge>0"
      proof (rule ccontr)
        assume "\<not> w\<ge>0" hence "-w > 0" by auto
        hence "(-1 * w)^3 > 0" by (auto simp only: zero_less_power)
        hence "(-1)^3* (w^3) > 0" by (simp only: power_mult_distrib)
        hence "w^3 < 0" by (simp add: neg_one_odd_power)
        with w3pos show False by auto
      qed
      moreover have "w \<noteq> 0"
      proof (rule ccontr)
        assume "\<not>w\<noteq>0" with ass have "0 \<in> zOdd" by simp
        moreover have "0 \<in> zEven" by (simp add: zEven_def)
        ultimately show False by (auto simp add: odd_iff_not_even)
      qed
      ultimately show ?thesis by (auto)
    qed
    hence "w=1 \<or> Suc 0 < nat w" by auto
    moreover
    { assume "w=1"
      hence "primel [] \<and> int (prod []) = w" by (auto simp add: primel_def)
      hence ?thesis by (simp only: exI) }
    moreover
    { assume "Suc 0 < nat w"
      hence "\<exists> l. primel l \<and> prod l = nat w" by (rule factor_exists)
      then obtain ps where ps: "primel ps \<and> prod ps = nat w" by auto
      with wpos have ?thesis by auto }
    ultimately show ?thesis by blast
  qed
  with ass show ?thesis by (auto dest: qf3_cube_primelist_impl_cube_form)
qed

subsection {* Existence ($N=3$) *}

text {* This part contains the proof that all prime numbers $\equiv 1 \bmod 6$ can be written as $x^2 + 3y^2$. *}

text {* First show $(\frac{a}{p})(\frac{b}{p}) = (\frac{ab}{p})$, where $p$ is an odd prime. *}
lemma Legendre_zmult: "\<lbrakk> p > 2; zprime p \<rbrakk>
  \<Longrightarrow> (Legendre (a*b) p) = (Legendre a p)*(Legendre b p)"
proof -
  assume p2: "p > 2" and prp: "zprime p"
  let ?p12 = "nat(((p) - 1) div 2)"
  let ?Labp = "Legendre (a*b) p"
  let ?Lap = "Legendre a p"
  let ?Lbp = "Legendre b p"
  from p2 prp have "[?Labp = (a*b)^?p12] (mod p)"
    by (simp only: Euler_Criterion)
  hence "[a^?p12 * b^?p12 = ?Labp] (mod p)"
    by (simp only: power_mult_distrib zcong_sym)
  moreover from p2 prp have "[?Lap * ?Lbp = a^?p12*b^?p12] (mod p)"
    by (simp only: Euler_Criterion zcong_zmult)
  ultimately have "[?Lap * ?Lbp = ?Labp] (mod p)"
    by (rule_tac b="a^?p12 * b^?p12" in zcong_trans)
  then obtain k where k: "?Labp = (?Lap*?Lbp) + p * k"
    by (auto simp add: zcong_iff_lin)
  have "k=0"
  proof (rule ccontr)
    assume "k \<noteq> 0" hence "\<bar>k\<bar> = 1 \<or> \<bar>k\<bar> > 1" by arith
    moreover
    { assume "\<bar>k\<bar>= 1"
      with p2 have "\<bar>k\<bar>*p > 2" by auto }
    moreover
    { assume k1: "\<bar>k\<bar> > 1"
      with p2 have "\<bar>k\<bar>*2 < \<bar>k\<bar>*p"
        by (simp only: zmult_zless_mono2)
      with k1 have "\<bar>k\<bar>*p > 2" by arith }
   ultimately have "\<bar>k\<bar>*p > 2" by auto
   moreover from p2 have "\<bar>p\<bar> = p" by auto
   ultimately have "\<bar>k*p\<bar> > 2" by (auto simp only: abs_mult)
   moreover from k have "?Labp - ?Lap*?Lbp = k*p" by auto
   ultimately have "\<bar>?Labp - ?Lap*?Lbp\<bar> > 2" by auto
   moreover have "?Labp = 1 \<or> ?Labp = 0 \<or> ?Labp = -1"
     by (simp add: Legendre_def)
   moreover have "?Lap*?Lbp = 1 \<or> ?Lap*?Lbp = 0 \<or> ?Lap*?Lbp = -1"
     by (auto simp add: Legendre_def)
   ultimately show False by auto
 qed
 with k show ?thesis by auto
qed

text {* Now show $(\frac{-3}{p}) = +1$ for primes $p \equiv 1 \bmod 6$. *}

lemma Legendre_1mod6: "zprime (6*m+1) \<Longrightarrow> Legendre (-3) (6*m+1) = 1"
proof -
  let ?p = "6*m+1"
  let ?L = "Legendre (-3) ?p"
  let ?L1 = "Legendre (-1) ?p"
  let ?L3 = "Legendre 3 ?p"
  assume p: "zprime ?p"
  have neg1cube: "(-1::int)^3 = -1" by (simp add: power3_minus)
  have m1: "m \<ge> 1"
  proof (rule ccontr)
    assume "\<not> m \<ge> 1" hence "m \<le> 0" by simp
    with p show False by (auto simp add: zprime_def)
  qed
  hence pn3: "?p \<noteq> 3" and p2: "?p > 2" by auto
  with p have "?L = (Legendre (-1) ?p) * (Legendre 3 ?p)"
    by (frule_tac a="-1" and b="3" in Legendre_zmult, auto)
  moreover have "[Legendre (-1) ?p = (-1)^nat m] (mod ?p)"
  proof -
    from p p2 have "[?L1 = (-1)^(nat(((?p) - 1) div 2))] (mod ?p)"
      by (simp only: Euler_Criterion)
    moreover have "nat ((?p - 1) div 2) = 3* nat m"
    proof -
      have "(?p - 1) div 2 = 3*m" by auto
      hence "nat((?p - 1) div 2) = nat (3*m)" by simp
      moreover have "(3::int) \<ge> 0" by simp
      ultimately show ?thesis by (simp add: nat_mult_distrib)
    qed
    moreover with neg1cube have "(-1::int)^(3*nat m) = (-1)^nat m"
      by (simp only: power_mult)
    ultimately show ?thesis by auto
  qed
  moreover have "?L3 = (-1)^nat m"
  proof -
    have "?L3 * (Legendre ?p 3) = (-1)^nat m"
    proof -
      have "3 \<in> zOdd \<and> ?p \<in> zOdd" by (unfold zOdd_def, auto)
      with p pn3 have "?L3 * (Legendre ?p 3) = (-1::int)^(3*nat m)"
        by (simp add: zprime_3 Quadratic_Reciprocity nat_mult_distrib)
      with neg1cube show ?thesis by (simp add: power_mult)
    qed
    moreover have "Legendre ?p 3 = 1"
    proof -
      have "[1^2 = ?p] (mod 3)" by (unfold zcong_def dvd_def, auto)
      hence "QuadRes 3 ?p" by (unfold QuadRes_def, blast)
      moreover have "\<not> [?p = 0] (mod 3)"
      proof (rule ccontr, simp)
        assume "[?p = 0] (mod 3)"
        hence "3 dvd ?p" by (simp add: zcong_def)
        moreover have "3 dvd 6*m" by (auto simp add: dvd_def)
        ultimately have "3 dvd ?p- 6*m" by (simp only: dvd_diff)
        hence "(3::int) dvd 1" by simp
        thus False by auto
      qed
      ultimately show ?thesis by (unfold Legendre_def, auto)
    qed
    ultimately show ?thesis by auto
  qed
  ultimately have "[?L = (-1)^(nat m)*(-1)^(nat m)] (mod ?p)"
    by (auto dest: zcong_scalar)
  hence "[?L = (-1)^((nat m)+(nat m))] (mod ?p)" by (simp only: power_add)
  moreover have "(nat m)+(nat m) = 2*(nat m)" by auto
  ultimately have "[?L = (-1)^(2*(nat m))] (mod ?p)" by simp
  hence "[?L = ((-1)^2)^(nat m)] (mod ?p)" by (simp only: power_mult)
  hence "[1 = ?L] (mod ?p)" by (auto simp add: zcong_sym)
  hence "?p dvd 1 - ?L" by (simp only: zcong_def)
  moreover have "?L = -1 \<or> ?L = 0 \<or> ?L = 1" by (simp add: Legendre_def)
  ultimately have "?p dvd 2 \<or> ?p dvd 1 \<or> ?L = 1" by auto
  moreover
  { assume "?p dvd 2 \<or> ?p dvd 1"
    with p2 have False by (auto simp add: zdvd_not_zless) }
  ultimately show ?thesis by auto
qed

text {* Use this to prove that such primes can be written as $x^2 + 3y^2$. *}

lemma qf3_prime_exists: "zprime (6*m+1) \<Longrightarrow> \<exists> x y. 6*m+1 = x^2 + 3*y^2"
proof -
  let ?p = "6*m+1"
  assume p: "zprime ?p"
  hence "Legendre (-3) ?p = 1" by (rule Legendre_1mod6)
  moreover
  { assume "\<not> QuadRes ?p (-3)"
    hence "Legendre (-3) ?p \<noteq> 1" by (unfold Legendre_def, auto) }
  ultimately have "QuadRes ?p (-3)" by auto
  then obtain s where s: "[s^2 = -3] (mod ?p)" by (auto simp add: QuadRes_def)
  hence "?p dvd s^2 - (-3::int)" by (unfold zcong_def, simp)
  moreover have "s^2 -(-3::int) = s^2 + 3" by arith
  ultimately have "?p dvd s^2 + 3*1^2" by auto
  moreover have "zgcd s 1 = 1" by (unfold zgcd_def, auto)
  moreover have "?p \<in> zOdd"
  proof -
    have "?p = 2*(3*m)+1" by simp
    thus ?thesis by (unfold zOdd_def, blast)
  qed
  moreover from p have "zprime ?p" by simp
  ultimately have "is_qfN ?p 3" by (simp only: qf3_oddprimedivisor)
  thus ?thesis by (unfold is_qfN_def, auto)
qed

end
