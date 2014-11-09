(*  Title:      Fermat3.thy
    Author:     Roelof Oosterhuis, 2007  Rijksuniversiteit Groningen
*)

section {* Fermat's last theorem, case $n=3$ *}

theory Fermat3
imports QuadForm
begin

text {* Proof of Fermat's last theorem for the case $n=3$: $$\forall x,y,z:~x^3 + y^3 = z^3 \Longrightarrow xyz=0.$$ *}

lemma factor_sum_cubes: "(x::int)^3 + y^3 = (x+y)*(x^2 - x*y + y^2)"
  by (simp add: eval_nat_numeral field_simps)

lemma two_not_abs_cube: "\<bar>x^3\<bar> = (2::int) \<Longrightarrow> False"
proof -
  assume "\<bar>x^3\<bar> = 2"
  hence x32: "\<bar>x\<bar>^3 = 2" by (simp only: abs_power3_distrib)
  have "\<bar>x\<bar> \<ge> 0" by simp
  moreover 
  { assume "\<bar>x\<bar> = 0 \<or> \<bar>x\<bar> = 1 \<or> \<bar>x\<bar> = 2"
    with x32 have False by (auto simp add: power_0_left) }
  moreover
  { assume "\<bar>x\<bar> > 2"
    moreover have "(0::int) \<le> 2" and "(0::nat) < 3" by auto
    ultimately have "\<bar>x\<bar>^3 > 2^3" by (simp only: power_strict_mono) 
    with x32 have False by simp }
  ultimately show False by arith
qed

text {* Shows there exists no solution $v^3+w^3 = x^3$ with $vwx\ne 0$ and $\gcd(v,w)=1$ and $x$ even, by constructing a solution with a smaller $|x^3|$. *}

lemma no_rewritten_fermat3: 
  "\<not> (\<exists> v w. v^3+w^3 = x^3 \<and> v*w*x \<noteq> 0 \<and> x \<in> zEven \<and> zgcd v w=1)"
proof (induct x rule: infinite_descent0_measure[where V="\<lambda>x. nat\<bar>x^3\<bar>"])
  case (0 x) hence "x^3 = 0" by arith
  hence "x=0" by auto
  thus ?case by auto
next
  case (smaller x)
  then obtain v w where vwx: 
    "v^3+w^3=x^3 \<and> v*w*x \<noteq> 0 \<and> x \<in> zEven \<and> zgcd v w=1" (is "?P v w x")
    by auto
  have "\<exists> \<alpha> \<beta> \<gamma>. ?P \<alpha> \<beta> \<gamma> \<and> nat\<bar>\<gamma>^3\<bar> < nat\<bar>x^3\<bar>"
  proof -
    -- "obtain coprime $p$ and $q$ such that $v = p+q$ and $w = p-q$"
    have vwOdd: "v \<in> zOdd \<and> w \<in> zOdd"
    proof (rule ccontr, case_tac "v \<in> zOdd", simp_all)
      assume "v \<notin> zOdd" hence ve: "v \<in> zEven" by (rule not_odd_impl_even)
      hence "v^3 \<in> zEven" by (simp only: power_preserves_even)
      moreover from vwx have "x^3 \<in> zEven" by (simp only: power_preserves_even)
      ultimately have "(x^3-v^3) \<in> zEven" by (simp only: even_minus_even)
      moreover from vwx have "x^3-v^3 = w^3" by simp
      ultimately have "w^3 \<in> zEven" by simp
      hence "w \<in> zEven" by (simp only: power_preserves_even)
      with ve have "2 dvd v \<and> 2 dvd w" by (auto simp add: zEven_def)
      hence "2 dvd zgcd v w" by (simp add: zgcd_greatest_iff)
      with vwx show False by simp
    next
      assume vo: "v \<in> zOdd" and "w \<notin> zOdd" 
      hence "w \<in> zEven" by (simp add: not_odd_impl_even)
      with vo have "v^3 \<in> zOdd" and "w^3 \<in> zEven" 
        by (auto simp only: power_preserves_even power_preserves_odd)
      hence "w^3 + v^3 \<in> zOdd" by (simp only: even_plus_odd)
      with vwx have "x^3 \<in> zOdd" by (simp add: add.commute)
      hence "x \<in> zOdd" by (simp only: power_preserves_odd)
      with vwx show False by (auto simp add: odd_iff_not_even)
    qed
    hence "v+w \<in> zEven \<and> v-w \<in> zEven" by (simp add: odd_minus_odd odd_plus_odd)
    then obtain p q where pq: "v+w = 2*p \<and> v-w = 2*q" 
      by (auto simp add: zEven_def)
    hence vw: "v = p+q \<and> w = p-q" by auto
    -- "show that $x^3 = (2p)(p^2 + 3q^2)$ and that these factors are"
    -- "either coprime (first case), or have $3$ as g.c.d. (second case)"
    have vwpq: "v^3 + w^3 = (2*p)*(p^2 + 3*q^2)"
    proof -
      have "2*(v^3 + w^3) = 2*(v+w)*(v^2 - v*w + w^2)" 
        by (simp only: factor_sum_cubes)
      also from pq have "\<dots> = 4*p*(v^2 - v*w + w^2)" by auto
      also have "\<dots> = p*((v+w)^2 + 3*(v-w)^2)" 
        by (simp add: eval_nat_numeral field_simps)
      also with pq have "\<dots> = p*((2*p)^2 + 3*(2*q)^2)" by simp
      also have "\<dots> = 2*(2*p)*(p^2+3*q^2)" by (simp add: power_mult_distrib)
      finally show ?thesis by simp
    qed
    let ?g = "zgcd (2*p) (p^2+3*q^2)"
    have g1: "?g \<ge> 1" 
    proof (rule ccontr)
      assume "\<not> ?g \<ge> 1"
      then have "?g < 0 \<or> ?g = 0" unfolding not_le by arith
      moreover have "?g \<ge> 0" by (rule zgcd_geq_zero)
      ultimately have "?g = 0" by arith
      hence "p = 0" by simp
      with vwpq vwx `0 < nat\<bar>x^3\<bar>` show False by auto
    qed
    have gOdd: "\<not> 2 dvd ?g"
    proof (rule ccontr, simp)
      assume "2 dvd ?g"
      hence"2 dvd p^2+3*q^2" by (simp only: zgcd_greatest_iff)
      then obtain k where k: "p^2 + 3*q^2 = 2*k" by (auto simp add: dvd_def)
      hence "2*(k - 2*q^2) = p^2-q^2" by auto
      with vw have "v*w = 2*(k - 2*q^2)" by (simp add: zspecial_product)
      hence "v*w \<in> zEven" by (auto simp only: zEven_def)
      hence "v \<in> zEven \<or> w \<in> zEven" by (simp add: even_product)
      with vwOdd show False by (auto simp add: odd_iff_not_even)
    qed
    -- "first case: $p$ is not a multiple of $3$; hence $2p$ and $p^2+3q^2$"
    -- "are coprime; hence both are cubes"
    { assume p3: "\<not> 3 dvd p"
      have g3: "\<not> 3 dvd ?g"
      proof (rule ccontr, simp)
        assume "3 dvd ?g" hence "3 dvd 2*p" by (simp add: zgcd_greatest_iff)
        hence "(3::int) dvd 2 \<or> 3 dvd p" 
          by (auto simp only: zprime_3 zprime_zdvd_zmult_general)
        with p3 show False by arith
      qed
      have pq_relprime: "zgcd p q=1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and zp: "z dvd p" and zq: "z dvd q"
        hence "z dvd p+q \<and> z dvd p-q" by (auto simp only: dvd_add dvd_diff)
        with vw have "z dvd v \<and> z dvd w" by simp
        with z vwx show False
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      have factors_relprime: "?g = 1" 
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and z2p: "z dvd 2*p" and zpq: "z dvd p^2+3*q^2"
        hence zg: "z dvd ?g" by (simp add: zgcd_greatest_iff)
        with gOdd have "z \<noteq> 2" by auto
        with z have zg2: "z > 2" by (auto simp add: zprime_def)
        from z z2p have "z dvd 2 \<or> z dvd p" by (simp only: zprime_zdvd_zmult_general)
        moreover
        { assume "z dvd 2"
          hence "z \<le> 2" by (auto simp add: zdvd_imp_le)
          with zg2 have False by simp }
        ultimately have zp: "z dvd p" by auto
        hence "z dvd p^2" by (auto simp add: power2_eq_square)
        with zpq have "z dvd p^2+3*q^2-p^2" by (simp only: dvd_diff)
        hence "z dvd 3*q^2" by auto
        with z have "z dvd 3 \<or> z dvd q^2" by (simp only: zprime_zdvd_zmult_general)
        moreover
        { assume "z dvd 3"
          hence "z \<le> 3" by (auto simp add: zdvd_imp_le)
          with zg2 have "z = 3" by auto
          with zg g3 have False by auto }
        ultimately have "z dvd q^2" by auto
        with z have "z dvd q" by (rule zprime_zdvd_power)
        with zp z pq_relprime show False
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      moreover from vwx vwpq have pqx: "(2*p)*(p^2 + 3*q^2) = x^3" by auto
      moreover have triv3: "3 = nat 3 \<and> nat 3 > 1 \<and> 3 \<in> zOdd"
        by (unfold zOdd_def, auto)
      ultimately have "\<exists> c. 2*p = c^3"
        by (simp only: int_relprime_odd_power_divisors)
      then obtain c where c: "c^3 = 2*p" by auto
      from pqx factors_relprime have "zgcd (p^2 + 3*q^2) (2*p) = 1"
        and "(p^2 + 3*q^2)*(2*p) = x^3" by (auto simp add: zgcd_commute ac_simps)
      with triv3 have "\<exists> d. p^2 + 3*q^2 = d^3"
        by (simp only: int_relprime_odd_power_divisors)
      then obtain d where d: "p^2 + 3*q^2 = d^3" by auto
      have "d \<in> zOdd"
      proof (rule ccontr)
        assume "d \<notin> zOdd" hence "d \<in> zEven" by (rule not_odd_impl_even)
        hence "d^3 \<in> zEven" by (simp only: power_preserves_even)
        hence "2 dvd d^3" by (simp add: zEven_def dvd_def)
        moreover have "2 dvd 2*p" by (rule dvd_triv_left)
        ultimately have "2 dvd zgcd (2*p) (d^3)" by (simp add: zgcd_greatest_iff)
        with d factors_relprime show False by simp
      qed
      with d pq_relprime have "zgcd p q=1 \<and> p^2 + 3*q^2 = d^3 \<and> d \<in> zOdd"
        by simp
      hence "is_cube_form p q" by (rule qf3_cube_impl_cube_form)
      then obtain a b where "p = a^3 - 9*a*b^2 \<and> q = 3*a^2*b - 3*b^3"
        by (unfold is_cube_form_def, auto)
      hence ab: "p = a*(a+3*b)*(a- 3*b) \<and> q = b*(a+b)*(a-b)*3"
        by (simp add: eval_nat_numeral field_simps)
      with c have abc: "(2*a)*(a+3*b)*(a- 3*b) = c^3" by auto
      have ab_relprime: "zgcd a b=1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and za: "z dvd a" and zb: "z dvd b"
        with ab have "z dvd p \<and> z dvd q" by simp
        with z pq_relprime show 
          False by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      have ab1: "zgcd (2*a) (a+3*b) = 1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and "z dvd 2*a" and zab: "z dvd a+3*b"
        hence "z dvd 2 \<or> z dvd a" by (simp add: zprime_zdvd_zmult)
        moreover have zn2: "\<not> z dvd 2"
        proof (rule ccontr, simp)
          assume z2: "z dvd 2" 
          hence "z \<le> 2" by (simp only: zdvd_imp_le)
          with z have "z = 2" by (unfold zprime_def, auto)
          with zab have ab2: "2 dvd a+3*b" by simp
          moreover have "2 dvd 2*b" by (rule dvd_triv_left)
          ultimately have "2 dvd a+3*b- 2*b" by (rule dvd_diff)
          hence "2 dvd a+b" by arith
          hence "2 dvd (a+b)*((a-b)*b*3)" by (rule dvd_mult2)
          with ab have qEven: "2 dvd q" by (simp only: ac_simps)
          from ab2 have "2 dvd (a+3*b)*((a- 3*b)*a)" by (rule dvd_mult2)
          with ab have "2 dvd p" by (simp only: ac_simps)
          with qEven have "2 dvd zgcd p q" by (simp add: zgcd_greatest_iff)
          with pq_relprime show False by auto
        qed
        ultimately have za: "z dvd a" by auto
        with zab have "z dvd a+3*b-a" by (simp only: dvd_diff)
        hence "z dvd 3*b" by simp
        with z have "z dvd 3 \<or> z dvd b" by (simp only: zprime_zdvd_zmult_general)
        moreover
        { assume "z dvd 3"
          with z have "z \<le> 3" by (auto simp add: zdvd_imp_le)
          moreover from zn2 have "z\<noteq>2" by auto
          moreover from z have "z > 1" by (simp add: zprime_def)
          ultimately have "z=3" by auto
          with za have "3 dvd a" by simp
          with ab have "3 dvd p" by auto
          with p3 have False by auto }
        ultimately have "z dvd b" by auto
        with za z ab_relprime show False
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      have ab2: "zgcd (a+3*b) (a- 3*b) = 1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and zab1: "z dvd a+3*b" and zab2: "z dvd a- 3*b"
        hence "z dvd (a+3*b)+(a- 3*b)" by (simp only: dvd_add)
        hence "z dvd 2*a" by simp
        with zab1 z ab1 show False
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      have "zgcd(a- 3*b) (2*a) = 1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and z2a: "z dvd 2*a" and zab: "z dvd a- 3*b"
        hence "z dvd 2*a-(a- 3*b)" by (simp only: dvd_diff)
        moreover have "2*a-(a- 3*b) = a+3*b" by simp
        ultimately have "z dvd a+3*b" by simp
        with z2a z ab1 show False
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      with abc ab1 ab2 triv3 have "\<exists> k l m. 2*a=k^3 \<and> a+3*b=l^3 \<and> a- 3*b=m^3"
        by (simp only: int_triple_relprime_odd_power_divisors)
      then obtain \<alpha> \<beta> \<gamma> where albega: 
        "2*a = \<gamma>^3 \<and> a - 3*b = \<alpha>^3 \<and> a+3*b = \<beta>^3" by auto 
      -- "show this is a (smaller) solution"
      hence "\<alpha>^3 + \<beta>^3 = \<gamma>^3" by auto
      moreover have "\<alpha>*\<beta>*\<gamma> \<noteq> 0"
      proof (rule ccontr, safe)
        assume "\<alpha> * \<beta> * \<gamma> = 0"
        with albega ab have "p=0" by (auto simp add: power_0_left)
        with vwpq vwx show False by auto
      qed
      moreover have "\<gamma> \<in> zEven"
      proof -
        have "2*a \<in> zEven" by (simp add: zEven_def)
        with albega have "\<gamma>^3 \<in> zEven" by simp
        thus ?thesis by (simp only: power_preserves_even)
      qed
      moreover have "zgcd \<alpha> \<beta>=1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and za: "z dvd \<alpha>" and zb: "z dvd \<beta>"
        hence "z dvd \<alpha> * \<alpha>^2 \<and> z dvd \<beta> * \<beta>^2" by simp
        hence "z dvd \<alpha>^Suc 2 \<and> z dvd \<beta>^Suc 2" by (auto simp only: power_Suc)
        with albega have "z dvd a- 3*b \<and> z dvd a+3*b" by auto 
        with ab2 z show False
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      moreover have "nat\<bar>\<gamma>^3\<bar> < nat\<bar>x^3\<bar>"
      proof -
        let ?A = "p^2 + 3*q^2"
        from vwx vwpq have "x^3 = 2*p*?A" by auto
        also with ab have "\<dots> = 2*a*((a+3*b)*(a- 3*b)*?A)" by auto
        also with albega have "\<dots> = \<gamma>^3 *((a+3*b)*(a- 3*b)*?A)" by auto
        finally have eq: "\<bar>x^3\<bar> = \<bar>\<gamma>^3\<bar> * \<bar>(a+3*b)*(a- 3*b)*?A\<bar>"
          by (auto simp add: abs_mult)
        with `0 < nat\<bar>x^3\<bar>` have "\<bar>(a+3*b)*(a- 3*b)*?A\<bar> > 0" by auto
        hence eqpos: "\<bar>(a+3*b)*(a- 3*b)\<bar> > 0" by auto
        moreover have Ag1: "\<bar>?A\<bar> > 1"
        proof -
          have Aqf3: "is_qfN ?A 3" by (auto simp add: is_qfN_def)
          moreover have triv3b: "(3::int) \<ge> 1" by simp
          ultimately have "?A \<ge> 0" by (simp only: qfN_pos)
          hence "?A > 1 \<or> ?A = 0 \<or> ?A =1" by arith
          moreover
          { assume "?A = 0" with triv3b have "p = 0 \<and> q = 0" by (rule qfN_zero)
            with vwpq vwx have False by auto }
          moreover 
          { assume A1: "?A = 1" 
            have "q=0"
            proof (rule ccontr)
              assume "q \<noteq> 0"
              hence "q^2 > 0"  by (simp add: zero_less_power2)
              hence "3*q^2 > 1" by arith
              moreover have "p^2 \<ge> 0" by (rule zero_le_power2)
              ultimately have "?A > 1" by arith
              with A1 show False by simp
            qed
            with A1 have p21: "p^2 = 1" by simp
            hence "\<bar>p\<bar> = 1" by (rule power2_eq1_iff)
            with vwpq vwx A1 have "\<bar>x^3\<bar> = 2" by auto
            hence False by (rule two_not_abs_cube) }
          ultimately show ?thesis by auto
        qed
        ultimately have 
          "\<bar>(a+3*b)*(a- 3*b)\<bar>*1 < \<bar>(a+3*b)*(a- 3*b)\<bar>*\<bar>?A\<bar>"
          by (simp only: zmult_zless_mono2)
        with eqpos have "\<bar>(a+3*b)*(a- 3*b)\<bar>*\<bar>?A\<bar> > 1" by arith
        hence "\<bar>(a+3*b)*(a- 3*b)*?A\<bar> > 1" by (auto simp add: abs_mult)
        moreover have "\<bar>\<gamma>^3\<bar> > 0"
        proof - 
          from eq have "\<bar>\<gamma>^3\<bar> = 0 \<Longrightarrow> \<bar>x^3\<bar>=0" by auto
          with `0 < nat\<bar>x^3\<bar>` show ?thesis by auto
        qed
        ultimately have "\<bar>\<gamma>^3\<bar> * 1 < \<bar>\<gamma>^3\<bar> * \<bar>(a+3*b)*(a- 3*b)*?A\<bar>"
          by (rule zmult_zless_mono2)
        with eq have "\<bar>x^3\<bar> > \<bar>\<gamma>^3\<bar>" by auto
        thus ?thesis by arith
      qed
      ultimately have ?thesis by auto }
    moreover
    -- "second case: $p = 3r$ and hence $x^3 = (18r)(q^2+3r^2)$ and these"
    -- "factors are coprime; hence both are cubes" 
    { assume p3: "3 dvd p"
      then obtain r where r: "p = 3*r" by (auto simp add: dvd_def)
      moreover have "3 dvd 3*(3*r^2 + q^2)" by (rule dvd_triv_left)
      ultimately have pq3: "3 dvd p^2+3*q^2" by (simp add: power_mult_distrib)
      moreover from p3 have "3 dvd 2*p" by (rule dvd_mult)
      ultimately have g3: "3 dvd ?g" by (simp add: zgcd_greatest_iff)
      have qr_relprime: "zgcd q r = 1" 
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and zq: "z dvd q" and "z dvd r"
        with r have "z dvd p" by simp
        with zq have "z dvd p+q \<and> z dvd p-q" by simp
        with vw have "z dvd zgcd v w" by (simp add: zgcd_greatest_iff)
        with vwx z show False by (auto simp add: zprime_def) 
      qed
      have factors_relprime: "zgcd (18*r) (q^2 + 3*r^2) = 1"
      proof -
        from g3 obtain k where k: "?g = 3*k" by (auto simp add: dvd_def)
        have "k = 1"
        proof (rule ccontr)
          assume "k \<noteq> 1"
          with g1 k have "k > 1" by auto
          then obtain h where h: "zprime h \<and> h dvd k" 
            by (frule_tac a="k" in zprime_factor_exists, blast)
          with k have hg: "3*h dvd ?g" by (auto simp add: mult_dvd_mono)
          hence "3*h dvd p^2 + 3*q^2" and hp: "3*h dvd 2*p" 
            by (auto simp only: zgcd_greatest_iff)
          then obtain s where s: "p^2 + 3*q^2 = (3*h)*s" 
            by (auto simp add: dvd_def)
          with r have rqh: "3*r^2+q^2 = h*s" by (simp add: power_mult_distrib)
          from hp r have "3*h dvd 3*(2*r)" by simp
          moreover have "(3::int) \<noteq> 0" by simp
          ultimately have "h dvd 2*r" by (rule zdvd_mult_cancel)
          with h have "h dvd 2 \<or> h dvd r" by (simp only: zprime_zdvd_zmult_general)
          moreover have "\<not> h dvd 2" 
          proof (rule ccontr, simp)
            assume "h dvd 2" 
            with h have "h=2" by (auto simp add: zdvd_not_zless zprime_def)
            with hg have "2*3 dvd ?g" by auto
            hence "2 dvd ?g" by (rule dvd_mult_left)
            with gOdd show False by simp
          qed
          ultimately have hr: "h dvd r" by simp
          then obtain t where "r = h*t" by (auto simp add: dvd_def)
          hence t: "r^2 = h*(h*t^2)" by (auto simp add: power2_eq_square)
          with rqh have "h*s = h*(3*h*t^2) + q^2" by simp
          hence "q^2 = h*(s - 3*h*t^2)" by (simp add: right_diff_distrib)
          hence "h dvd q^2" by simp
          with h have "h dvd q" by (auto dest: zprime_zdvd_power)
          with hr have "h dvd zgcd q r" by (simp add: zgcd_greatest_iff)
          with h qr_relprime show False by (unfold zprime_def, auto)
        qed
        with k r have "3 = zgcd (2*(3*r)) ((3*r)^2 + 3*q^2)" by auto
        also have "\<dots> = zgcd (3*(2*r)) (3*(3*r^2 + q^2))" 
          by (simp add: power_mult_distrib)
        also have "\<dots> = 3 * zgcd (2*r) (3*r^2 + q^2)" 
          by (simp only: zgcd_zmult_distrib2)
        finally have "zgcd (2*r) (3*r^2 + q^2) = 1" by auto
        moreover have "zgcd (3*3) (3*r^2 + q^2) = 1"
        proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
          fix h::int assume "h dvd 3*3" and h: "zprime h" and hrq: "h dvd 3*r^2 + q^2"
          hence "h dvd 3 \<or> h dvd 3" by (simp only: zprime_zdvd_zmult_general)
          hence h3: "h dvd 3" by simp
          have "h \<le> 3" 
          proof (rule ccontr)
            assume "\<not> h \<le> 3" hence "h > 3" by simp
            with h3 show False by (auto simp add: zdvd_not_zless)
          qed
          with h have "h = 2 \<or> h = 3" by (unfold zprime_def, auto)
          with h h3 have "h = 3 \<or> (2::int) dvd 3" by auto
          hence "h=3" by arith
          with hrq obtain s where "3*r^2+q^2 = 3*s" by (auto simp add: dvd_def)
          hence "q^2 = 3*(s- r^2)" by auto
          hence "3 dvd q^2" and "zprime 3" by (auto simp only: dvd_triv_left zprime_3)
          hence "3 dvd q" by (rule_tac p="3" in zprime_zdvd_power)
          with p3 have "3 dvd p+q \<and> 3 dvd p-q" by simp
          with vw have "3 dvd zgcd v w" by (simp add: zgcd_greatest_iff)
          with vwx show False by auto
        qed
        ultimately have "zgcd ((3*3)*(2*r)) (3*r^2 + q^2) = 1" 
          by (simp only: zgcd_zmult_cancel)
        thus ?thesis by (auto simp add: ac_simps ac_simps)
      qed
      moreover have rqx: "(18*r)*(q^2 + 3*r^2) = x^3"
      proof -
        from vwx vwpq have "x^3 = 2*p*(p^2 + 3*q^2)" by auto
        also with r have "\<dots> = 2*(3*r)*(9*r^2 + 3*q^2)" 
          by (auto simp add: power2_eq_square)
        finally show ?thesis by auto
      qed
      moreover have triv3: "3 = nat 3 \<and> nat 3 > 1 \<and> 3 \<in> zOdd" 
        by (unfold zOdd_def, auto)
      ultimately have "\<exists> c. 18*r = c^3" 
        by (simp only: int_relprime_odd_power_divisors)
      then obtain c1 where c1: "c1^3 = 3*(6*r)" by auto
      hence "3 dvd c1^3" and "zprime 3" by (auto simp only: dvd_triv_left zprime_3)
      hence "3 dvd c1" by (rule_tac p="3" in zprime_zdvd_power)
      with c1 obtain c where c: "3*c^3 = 2*r" 
        by (auto simp add: power_mult_distrib dvd_def)
      from rqx factors_relprime have "zgcd (q^2 + 3*r^2) (18*r) = 1"
        and "(q^2 + 3*r^2)*(18*r) = x^3" by (auto simp add: zgcd_commute ac_simps)
      with triv3 have "\<exists> d. q^2 + 3*r^2 = d^3" 
        by (simp only: int_relprime_odd_power_divisors)
      then obtain d where d: "q^2 + 3*r^2 = d^3" by auto
      have "d \<in> zOdd"
      proof (rule ccontr)
        assume "d \<notin> zOdd" hence "d \<in> zEven" by (rule not_odd_impl_even)
        hence "d^3 \<in> zEven" by (simp only: power_preserves_even)
        hence "2 dvd d^3" by (simp add: zEven_def dvd_def)
        moreover have "2 dvd 2*(9*r)" by (rule dvd_triv_left)
        ultimately have "2 dvd zgcd (2*(9*r)) (d^3)" by (simp add: zgcd_greatest_iff)
        with d factors_relprime show False by auto
      qed
      with d qr_relprime have "zgcd q r=1 \<and> q^2 + 3*r^2 = d^3 \<and> d \<in> zOdd" 
        by simp
      hence "is_cube_form q r" by (rule qf3_cube_impl_cube_form)
      then obtain a b where "q = a^3 - 9*a*b^2 \<and> r = 3*a^2*b - 3*b^3" 
        by (unfold is_cube_form_def, auto)
      hence ab: "q = a*(a+3*b)*(a- 3*b) \<and> r = b*(a+b)*(a-b)*3"
        by (simp add: eval_nat_numeral field_simps)
      with c have abc: "(2*b)*(a+b)*(a-b) = c^3" by auto
      have ab_relprime: "zgcd a b=1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and za: "z dvd a" and zb: "z dvd b"
        with ab have "z dvd q \<and> z dvd r" by simp
        with z qr_relprime show False 
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      have ab1: "zgcd (2*b) (a+b) = 1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and "z dvd 2*b" and zab: "z dvd a+b"
        hence "z dvd 2 \<or> z dvd b" by (simp add: zprime_zdvd_zmult)
        moreover
        { assume z2: "z dvd 2" 
          hence "z \<le> 2" by (simp only: zdvd_imp_le)
          with z have "z = 2" by (unfold zprime_def, auto)
          with zab have ab2: "2 dvd a+b" by simp
          moreover have "2 dvd 2*b" by (rule dvd_triv_left)
          ultimately have "2 dvd a+b+2*b" by (rule dvd_add)
          hence "2 dvd a+3*b" by arith
          hence "2 dvd (a+3*b)*((a- 3*b)*a)" by (rule dvd_mult2)
          with ab have qEven: "2 dvd q" by (simp only: ac_simps)
          from ab2 have "2 dvd (a+b)*((a-b)*3*b)" by (rule dvd_mult2)
          with ab have "2 dvd r" by (simp only: ac_simps)
          with qEven have "2 dvd zgcd q r" by (simp add: zgcd_greatest_iff)
          with qr_relprime have False by auto }
        moreover
        { assume zb: "z dvd b"
          with zab have "z dvd a+b-b" by (simp only: dvd_diff)
          hence "z dvd a" by simp
          with zb ab_relprime z have False 
            by (auto simp add: zgcd1_iff_no_common_primedivisor) }
        ultimately show False by auto
      qed
      have ab2: "zgcd (a+b) (a-b) = 1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and zab1: "z dvd a+b" and zab2: "z dvd a-b"
        hence "z dvd (a+b)-(a-b)" by (simp only: dvd_diff)
        hence "z dvd 2*b" by simp
        with zab1 z ab1 show False 
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      have "zgcd (a-b) (2*b) = 1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and z2b: "z dvd 2*b" and zab: "z dvd a-b"
        hence "z dvd a-b+2*b" by (simp only: dvd_add)
        moreover have "a-b+2*b = a+b" by simp
        ultimately have "z dvd a+b" by simp
        with z2b z ab1 show False 
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      with abc ab1 ab2 triv3 have "\<exists> k l m. 2*b = k^3 \<and> a+b = l^3 \<and> a-b = m^3" 
        by (simp only: int_triple_relprime_odd_power_divisors)
      then obtain \<alpha>1 \<beta> \<gamma> where a1: "2*b = \<gamma>^3 \<and> a-b = \<alpha>1^3 \<and> a+b = \<beta>^3"
        by auto 
      then obtain \<alpha> where "\<alpha> = -\<alpha>1" by auto
      -- "show this is a (smaller) solution"
      with triv3 a1 have a2: "\<alpha>^3 = b-a" by (auto simp only: neg_odd_power)
      with a1 have "\<alpha>^3 + \<beta>^3 = \<gamma>^3" by auto
      moreover have "\<alpha>*\<beta>*\<gamma> \<noteq> 0"
      proof (rule ccontr, safe)
        assume "\<alpha> * \<beta> * \<gamma> = 0"
        with a1 a2 ab have "r=0" by (auto simp add: power_0_left)
        with r vwpq vwx show False by auto
      qed
      moreover have "\<gamma> \<in> zEven"
      proof -
        have "2*b \<in> zEven" by (simp add: zEven_def)
        with a1 have "\<gamma>^3 \<in> zEven" by simp
        thus ?thesis by (simp only: power_preserves_even)
      qed
      moreover have "zgcd \<alpha> \<beta>=1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix z assume z: "zprime z" and za: "z dvd \<alpha>" and zb: "z dvd \<beta>"
        hence "z dvd \<alpha> * \<alpha>^2 \<and> z dvd \<beta> * \<beta>^2" by simp
        hence "z dvd \<alpha>^Suc 2 \<and> z dvd \<beta>^Suc 2" by (auto simp only: power_Suc)
        with a1 a2 have "z dvd b-a \<and> z dvd a+b" by auto 
        hence "z dvd -(b-a) \<and> z dvd a+b" by (auto simp only: dvd_minus_iff)
        with ab2 z show False 
          by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      moreover have "nat\<bar>\<gamma>^3\<bar> < nat\<bar>x^3\<bar>"
      proof -
        let ?A = "p^2 + 3*q^2"
        from vwx vwpq have "x^3 = 2*p*?A" by auto
        also with r have "\<dots> = 6*r*?A" by auto
        also with ab have "\<dots> = 2*b*(9*(a+b)*(a-b)*?A)" by auto
        also with a1 have "\<dots> = \<gamma>^3 *(9*(a+b)*(a-b)*?A)" by auto
        finally have eq: "\<bar>x^3\<bar> = \<bar>\<gamma>^3\<bar> * \<bar>9*(a+b)*(a-b)*?A\<bar>" 
          by (auto simp add: abs_mult)
        with `0 < nat\<bar>x^3\<bar>` have "\<bar>9*(a+b)*(a-b)*?A\<bar> > 0" by auto
        hence "\<bar>(a+b)*(a-b)*?A\<bar> \<ge> 1" by arith
        hence "\<bar>9*(a+b)*(a-b)*?A\<bar> > 1" by arith
        moreover have "\<bar>\<gamma>^3\<bar> > 0"
        proof - 
          from eq have "\<bar>\<gamma>^3\<bar> = 0 \<Longrightarrow> \<bar>x^3\<bar>=0" by auto
          with `0 < nat\<bar>x^3\<bar>` show ?thesis by auto
        qed
        ultimately have "\<bar>\<gamma>^3\<bar> * 1 < \<bar>\<gamma>^3\<bar> * \<bar>9*(a+b)*(a-b)*?A\<bar>"
          by (rule zmult_zless_mono2)
        with eq have "\<bar>x^3\<bar> > \<bar>\<gamma>^3\<bar>" by auto
        thus ?thesis by arith
      qed
      ultimately have ?thesis by auto }
    ultimately show ?thesis by auto
  qed
  thus ?case by auto
qed

text {* The theorem. Puts equation in requested shape. *}  

theorem fermat3:
  assumes ass: "(x::int)^3 + y^3 = z^3"
  shows "x*y*z=0"
proof (rule ccontr)
  let ?g = "zgcd x y"
  let ?c = "z div ?g"
  assume xyz0: "x*y*z\<noteq>0"
  -- "divide out the g.c.d."
  hence "x \<noteq> 0 \<or> y \<noteq> 0" by simp
  then obtain a b where ab: "x = ?g*a \<and> y = ?g*b \<and> zgcd a b=1"
    by (frule_tac a="x" in make_zrelprime, auto)
  moreover have abc: "?c*?g = z \<and> a^3 + b^3 = ?c^3 \<and> a*b*?c \<noteq> 0"
  proof -
    from xyz0 have g0: "?g\<noteq>0" by (simp add: zgcd_def gcd_zero)
    have zgab: "z^3 = ?g^3 * (a^3+b^3)"
    proof -
      from ab and ass have "z^3 = (?g*a)^3+(?g*b)^3" by simp
      thus ?thesis by (simp only: power_mult_distrib distrib_left)
    qed
    have cgz: "?c * ?g = z"
    proof - 
      from zgab have "?g^3 dvd z^3" by simp
      hence "?g dvd z" by (simp only: zpower_zdvd_mono)
      thus ?thesis by (simp only: ac_simps dvd_mult_div_cancel)
    qed
    moreover have "a^3 + b^3 = ?c^3"
    proof -
      have "?c^3 * ?g^3 = (a^3+b^3)*?g^3"
      proof -
        have "?c^3 * ?g^3 = (?c*?g)^3" by (simp only: power_mult_distrib)
        also with cgz have "\<dots> = z^3" by simp
        also with zgab have "\<dots> = ?g^3*(a^3+b^3)" by simp
        finally show ?thesis by simp
      qed
      with g0 show ?thesis by auto
    qed
    moreover from ab and xyz0 and cgz have "a*b*?c\<noteq>0" by auto
    ultimately show ?thesis by simp
  qed
  -- "make both sides even"
  have "\<exists> u v w. u^3 + v^3 = w^3 \<and> u*v*w\<noteq>0 \<and> w \<in> zEven \<and> zgcd u v = 1"
  proof -
    let "?Q u v w" = "u^3 + v^3 = w^3 \<and> u*v*w\<noteq>0 \<and> w \<in> zEven \<and> zgcd u v=1"
    have "a \<in> zEven \<or> b \<in> zEven \<or> ?c \<in> zEven"
    proof (rule ccontr)
      assume "\<not>(a \<in> zEven \<or> b \<in> zEven \<or> ?c \<in> zEven)"
      hence aodd: "a \<in> zOdd" and "b \<in> zOdd \<and> ?c \<in> zOdd" 
        by (auto simp add: odd_iff_not_even)
      hence "?c^3 - b^3 \<in> zEven" by (simp only: power_preserves_odd odd_minus_odd)
      moreover from abc have "?c^3-b^3 = a^3" by simp
      ultimately have "a^3 \<in> zEven" by auto
      hence "a \<in> zEven" by (simp only: power_preserves_even)
      with aodd show False by (simp add: odd_iff_not_even)
    qed
    moreover
    { assume "a \<in> zEven"
      then obtain u v w where uvwabc: "u = -b \<and> v = ?c \<and> w = a \<and> w \<in> zEven" 
        by auto
      moreover with abc have "u*v*w\<noteq>0" by auto
      moreover have uvw: "u^3+v^3=w^3" 
      proof -
        from uvwabc have "u^3 + v^3 = (-1*b)^3 + ?c^3" by simp
        also have "\<dots> = (-1)^3*b^3 + ?c^3" by (simp only: power_mult_distrib)
        also have "\<dots> = - (b^3) + ?c^3" by (auto simp add: neg_one_odd_power)
        also with abc and uvwabc have "\<dots> = w^3" by auto
        finally show ?thesis by simp
      qed
      moreover have "zgcd u v=1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix h::int assume hu: "h dvd u" and "h dvd v" and h: "zprime h"
        with uvwabc have "h dvd ?c*?c^2" by (simp only: dvd_mult2)
        with abc have "h dvd a^3+b^3" by (simp only: cube_square)
        moreover from hu uvwabc have "h dvd b*b^2" by simp
        ultimately have "h dvd a^3+b^3-b^3" by (simp only: cube_square dvd_diff)
        with h hu uvwabc have "h dvd a \<and> h dvd b" by (auto dest: zprime_zdvd_power)
        with h ab show False by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      ultimately have "?Q u v w" using `a \<in> zEven` by simp
      hence ?thesis by auto }
    moreover 
    { assume "b \<in> zEven"
      then obtain u v w where uvwabc: "u = -a \<and> v = ?c \<and> w = b \<and> w \<in> zEven" 
        by auto
      moreover with abc have "u*v*w\<noteq>0" by auto
      moreover have uvw: "u^3+v^3=w^3" 
      proof -
        from uvwabc have "u^3 + v^3 = (-1*a)^3 + ?c^3" by simp
        also have "\<dots> = (-1)^3*a^3 + ?c^3" by (simp only: power_mult_distrib)
        also have "\<dots> = - (a^3) + ?c^3" by (auto simp add: neg_one_odd_power)
        also with abc and uvwabc have "\<dots> = w^3" by auto
        finally show ?thesis by simp
      qed
      moreover have "zgcd u v=1"
      proof (simp only: zgcd1_iff_no_common_primedivisor, clarify)
        fix h::int assume hu: "h dvd u" and "h dvd v" and h: "zprime h"
        with uvwabc have "h dvd ?c*?c^2" by (simp only: dvd_mult2)
        with abc have "h dvd a^3+b^3" by (simp only: cube_square)
        moreover from hu uvwabc have "h dvd a*a^2" by simp
        ultimately have "h dvd a^3+b^3-a^3" by (simp only: cube_square dvd_diff)
        with h hu uvwabc have "h dvd a \<and> h dvd b" by (auto dest: zprime_zdvd_power)
        with h ab show False by (auto simp add: zgcd1_iff_no_common_primedivisor)
      qed
      ultimately have "?Q u v w" using `b \<in> zEven` by simp
      hence ?thesis by auto }
    moreover 
    { assume "?c \<in> zEven"
      then obtain u v w where uvwabc: "u = a \<and> v = b \<and> w = ?c \<and> w \<in> zEven"
        by auto
      with abc ab have ?thesis by auto }
    ultimately show ?thesis by auto
  qed
  hence "\<exists> w. \<exists> u v. u^3 + v^3 = w^3 \<and> u*v*w \<noteq> 0 \<and> w \<in> zEven \<and> zgcd u v=1"
    by auto
  -- "show contradiction using the earlier result"
  thus False by (auto simp only: no_rewritten_fermat3)
qed

corollary fermat_mult3:
  assumes xyz: "(x::int)^n + y^n = z^n" and n: "3 dvd n"
  shows "x*y*z=0"
proof -
  from n obtain m where "n = m*3" by (auto simp only: ac_simps dvd_def)
  with xyz have "(x^m)^3 + (y^m)^3 = (z^m)^3" by (simp only: power_mult)
  hence "(x^m)*(y^m)*(z^m) = 0" by (rule fermat3)
  thus ?thesis by auto
qed

end
