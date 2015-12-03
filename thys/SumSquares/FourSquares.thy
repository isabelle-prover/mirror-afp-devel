(*  Title:      FourSquares.thy
    Author:     Roelof Oosterhuis, 2007  Rijksuniversiteit Groningen
*)

section {* Lagrange's four-square theorem *}

theory FourSquares
imports "../Fermat3_4/IntNatAux" "~~/src/HOL/Old_Number_Theory/Quadratic_Reciprocity"
begin

text {* Shows that all nonnegative integers can be written as the sum of four squares. The proof consists of the following steps:
\begin{itemize}\item For every prime $p=2n+1$ the two sets of residue classes $$\{x^2 \bmod p\mid 0\le x\le n\} ~{\rm and}~ \{-1-y^2 \bmod p \mid 0 \le y \le n\}$$ both contain $n+1$ different elements and therefore they must have at least one element in common.
\item Hence there exist $x,y$ such that $x^2+y^2+1^2+0^2$ is a multiple of $p$.
\item The next step is to show, by an infinite descent, that $p$ itself can be written as the sum of four squares.
\item Finally, using the multiplicity of this form, the same holds for all positive numbers.
\end{itemize} *}

definition
  sum4sq :: "int \<times> int \<times> int \<times> int \<Rightarrow> int" where
  "sum4sq = (\<lambda>(a,b,c,d). a^2+b^2+c^2+d^2)"

definition
  is_sum4sq :: "int \<Rightarrow> bool" where
  "is_sum4sq x \<longleftrightarrow> (\<exists> a b c d. sum4sq(a,b,c,d) = x)"

lemma mult_sum4sq: "sum4sq(a,b,c,d) * sum4sq(p,q,r,s) = 
  sum4sq(a*p+b*q+c*r+d*s, a*q-b*p-c*s+d*r, 
         a*r+b*s-c*p-d*q, a*s-b*r+c*q-d*p)"
  by (unfold sum4sq_def, simp add: eval_nat_numeral field_simps)

lemma is_mult_sum4sq: "is_sum4sq x \<Longrightarrow> is_sum4sq y \<Longrightarrow> is_sum4sq (x*y)"
  by (unfold is_sum4sq_def, auto simp only: mult_sum4sq, blast)

lemma mult_oddprime_is_sum4sq: "\<lbrakk> zprime p; p \<in> zOdd \<rbrakk> \<Longrightarrow> 
  \<exists> t. 0<t \<and> t<p \<and> is_sum4sq (p*t)"
proof -
  assume p1: "zprime p" 
  hence p0: "p > 1" by (simp add: zprime_def)
  assume p2: "p \<in> zOdd"
  then obtain n where n: "p = 2*n+1" by (auto simp add: zOdd_def)
  with p1 have n0: "n > 0" by (auto simp add: zprime_def)
  let ?C = "{y. 0 \<le> y \<and> y < p}"
  let ?D = "{y. 0 \<le> y \<and> y \<le> n}"
  let ?f = "%x. x^2 mod p"
  let ?g = "%x. (-1-x^2) mod p"
  let ?A = "?f ` ?D"
  let ?B = "?g ` ?D"
  have finC: "finite ?C" by (rule bdd_int_set_l_finite)
  have finD: "finite ?D" by (rule bdd_int_set_le_finite)
  from p0 have AsubC: "?A \<subseteq> ?C" and BsubC: "?B \<subseteq> ?C" 
    by (auto simp add: pos_mod_conj)
  with finC have finA: "finite ?A" and finB: "finite ?B"
    by (auto simp add: finite_subset)
  from AsubC BsubC have AunBsubC: "?A \<union> ?B \<subseteq> ?C" by (rule Un_least)
  from p0 have cardC: "card ?C = nat p" by (simp only: card_bdd_int_set_l)
  from n0 have cardD: "card ?D = 1+ nat n" by (simp only: card_bdd_int_set_le)
  have cardA: "card ?A = card ?D"
  proof -
    have "inj_on ?f ?D"
    proof (unfold inj_on_def, auto)
      fix x fix y
      assume x0: "0 \<le> x" and xn: "x \<le> n" and y0: "0 \<le> y" and yn: " y \<le> n"
        and xyp: "x^2 mod p = y^2 mod p"
      with p0 have "[x^2 = y^2] (mod p)" by (simp only: zcong_zmod_eq)
      hence "p dvd x^2-y^2" by (simp only: zcong_def)
      hence "p dvd (x+y)*(x-y)" by (simp only: zspecial_product)
      with p1 have "p dvd x+y \<or> p dvd x-y" by (simp only: zprime_zdvd_zmult_general)
      moreover
      { assume "p dvd x+y" 
        moreover from xn yn n have "x+y < p" by auto
        ultimately have "\<not> x+y > 0" by (auto simp add: zdvd_not_zless)
        with x0 y0 have "x = y" by auto } -- "both are zero"
      moreover
      { assume ass: "p dvd x-y"
        have "x = y"
        proof (rule ccontr, case_tac "x-y \<ge> 0")
          assume "x-y \<ge> 0" and "x \<noteq> y" hence "x-y > 0" by auto
          with ass have "\<not> x-y < p" by (auto simp add: zdvd_not_zless)
          with xn y0 n p0 show "False" by auto
        next
          assume "\<not> 0 \<le> x-y" hence "y-x > 0" by auto
          moreover from x0 yn n p0 have "y-x < p" by auto
          ultimately have "\<not> p dvd y-x" by (auto simp add: zdvd_not_zless)
          moreover from ass have "p dvd -(x-y)" by (simp only: dvd_minus_iff)
          ultimately show "False" by auto
        qed }
      ultimately show "x=y" by auto
    qed
    with finD show ?thesis by (simp only: inj_on_iff_eq_card)
  qed
  have cardB: "card ?B = card ?D"
  proof -
    have "inj_on ?g ?D"
    proof (unfold inj_on_def, auto)
      fix x fix y
      assume x0: "0 \<le> x" and xn: "x \<le> n" and y0: "0 \<le> y" and yn: " y \<le> n"
        and xyp: "(-1-x^2) mod p = (-1-y^2) mod p"
      with p0 have "[-1-y^2 = -1-x^2] (mod p)" by (simp only: zcong_zmod_eq)
      hence "p dvd (-1-y^2) - (-1-x^2)" by (simp only: zcong_def)
      moreover have "-1-y^2 - (-1-x^2) = x^2 - y^2" by arith
      ultimately have "p dvd x^2-y^2" by simp
      hence "p dvd (x+y)*(x-y)" by (simp only: zspecial_product)
      with p1 have "p dvd x+y \<or> p dvd x-y" by (simp only: zprime_zdvd_zmult_general)
      moreover
      { assume "p dvd x+y" 
        moreover from xn yn n have "x+y < p" by auto
        ultimately have "\<not> x+y > 0" by (auto simp add: zdvd_not_zless)
        with x0 y0 have "x = y" by auto } -- "both are zero"
      moreover
      { assume ass: "p dvd x-y"
        have "x = y"
        proof (rule ccontr, case_tac "x-y \<ge> 0")
          assume "x-y \<ge> 0" and "x \<noteq> y" hence "x-y > 0" by auto
          with ass have "\<not> x-y < p" by (auto simp add: zdvd_not_zless)
          with xn y0 n p0 show "False" by auto
        next
          assume "\<not> 0 \<le> x-y" hence "y-x > 0" by auto
          moreover from x0 yn n p0 have "y-x < p" by auto
          ultimately have "\<not> p dvd y-x" by (auto simp add: zdvd_not_zless)
          moreover from ass have "p dvd -(x-y)" by (simp only: dvd_minus_iff)
          ultimately show "False" by auto
        qed }
      ultimately show "x=y" by auto
    qed
    with finD show ?thesis by (simp only: inj_on_iff_eq_card)
  qed
  have "?A \<inter> ?B \<noteq> {}"
  proof (rule ccontr, auto)
    assume ABdisj: "?A \<inter> ?B = {}"
    from cardA cardB cardD have "2 + 2*(nat n) = card ?A + card ?B" by auto
    also with finA finB ABdisj have "\<dots> = card (?A \<union> ?B)" 
      by (simp only: card_Un_disjoint)
    also with finC AunBsubC have "\<dots> \<le> card ?C" by (simp only: card_mono)
    also with cardC have "\<dots> = nat p" by simp
    finally have "2 + 2*(nat n) \<le> nat p" by simp
    with n show "False" by arith
  qed
  then obtain z where "z \<in> ?A \<and> z \<in> ?B" by auto
  then obtain x y where xy: "x \<in> ?D \<and> y \<in> ?D \<and> z = x^2 mod p \<and> 
    z = (-1-y^2) mod p" by auto
  with p0 have "[x^2=-1-y^2](mod p)" by (simp add: zcong_zmod_eq)
  hence "p dvd x^2-(-1-y^2)" by (simp only: zcong_def)
  moreover have "x^2-(-1-y^2)=x^2+y^2+1" by arith
  ultimately have "p dvd sum4sq(x,y,1,0)" by (auto simp add: sum4sq_def)
  then obtain t where t: "sum4sq(x,y,1,0) = p*t" by (auto simp add: dvd_def)
  hence "is_sum4sq (p*t)" by (unfold is_sum4sq_def, auto)
  moreover have "t > 0 \<and> t < p"
  proof
    have "x^2 \<ge> 0 \<and> y^2 \<ge> 0" by (simp add: zero_le_power2)
    hence "x^2+y^2+1 > 0" by arith
    with t have "p*t > 0" by (unfold sum4sq_def, auto)
    moreover
    { assume "t < 0" with p0 have "p*t < p*0" by (simp only: zmult_zless_mono2)
      hence "p*t < 0" by simp }
    moreover
    { assume "t = 0" hence "p*t = 0" by simp }
    ultimately have "\<not> t < 0 \<and> t \<noteq> 0" by auto
    thus "t > 0" by simp
    from xy have "x^2 \<le> n^2 \<and> y^2 \<le> n^2" by (auto simp add: power_mono)
    hence "x^2+y^2+1 \<le> 2*n^2 + 1" by auto
    with t have contr: "p*t \<le> 2*n^2+1" by (simp add: sum4sq_def)
    moreover
    { assume "t > n+1"
      with p0 have "p*(n+1) < p*t" by (simp only: zmult_zless_mono2)
      with n have "p*t > (2*n+1)*n + (2*n+1)*1" by (simp only: distrib_left)
      hence "p*t > 2*n*n + n + 2*n + 1" by (simp only: distrib_right mult_1_left)
      with n0 have "p*t > 2*n^2 + 1" by (simp add: power2_eq_square) }
    ultimately have "\<not> t > n+1" by auto
    with n0 n show "t < p" by auto
  qed
  ultimately show ?thesis by blast
qed

lemma zprime_is_sum4sq: "zprime p \<Longrightarrow> is_sum4sq p"
proof (cases)
  assume p2: "p=2" 
  hence "p = sum4sq(1,1,0,0)" by (auto simp add: sum4sq_def)
  thus ?thesis by (auto simp add: is_sum4sq_def)
next
  assume "\<not> p =2" and prp: "zprime p"
  hence "2 < p" by (simp add: zprime_def)
  with prp have "p \<in> zOdd" by (simp only: zprime_zOdd_eq_grt_2)
  with prp have "\<exists> t. 0<t \<and> t<p \<and> is_sum4sq (p*t)"
    by (rule mult_oddprime_is_sum4sq)
  then obtain a b c d t where pt_sol: "0<t \<and> t<p \<and> sum4sq(a,b,c,d)=p*t" 
    by (unfold is_sum4sq_def, blast)
  hence Qt: "0<t \<and> t<p \<and> (\<exists> a1 a2 a3 a4. sum4sq(a1,a2,a3,a4)=p*t)"
    (is "?Q t") by blast
  have "?Q 1"
  proof (rule ccontr)
    assume nQ1: "\<not> ?Q 1"
    have "\<not> ?Q t"
    proof (induct t rule: infinite_descent0_measure[where V="\<lambda>x. (nat x)- 1"], clarify)
      fix x a b c d 
      assume "nat x - 1 = 0" and "x > 0" and s: "sum4sq(a,b,c,d)=p*x" and "x < p"
      moreover hence "x = 1" by arith
      ultimately have "?Q 1" by auto
      with nQ1 show False by auto
    next
      fix x 
      assume "0 < nat x - 1" and "\<not> \<not> ?Q x"
      then obtain a1 a2 a3 a4 where ass: "1<x \<and> x<p \<and> sum4sq(a1,a2,a3,a4)=p*x"
        by auto
      have "\<exists> y. nat y - 1 < nat x - 1 \<and> ?Q y"
      proof (cases)
        assume evx: "x \<in> zEven"
        hence "x*p \<in> zEven" by (rule even_times_either)
        with ass have ev1234: "a1^2+a2^2 + a3^2+a4^2 \<in> zEven" 
          by (auto simp add: sum4sq_def ac_simps)
        have "\<exists> b1 b2 b3 b4. sum4sq(b1,b2,b3,b4)=p*x \<and> 
          b1+b2 \<in> zEven \<and> b3+b4 \<in> zEven"
        proof (cases)
          assume ev12: "a1^2+a2^2 \<in> zEven"
          moreover have "2*a1*a2 \<in> zEven" by (auto simp add: zEven_def)
          ultimately have"a1^2+a2^2+2*a1*a2 \<in> zEven" by (rule even_plus_even)
          hence "(a1+a2)^2 \<in> zEven" by (auto simp add: zadd_power2 ac_simps)
          hence tmp: "a1+a2 \<in> zEven" by (auto simp add: power_preserves_even)
          from ev12 ev1234 have "a1^2+a2^2+a3^2+a4^2-(a1^2+a2^2) \<in> zEven" 
            by (simp only: even_minus_even)
          hence "a3^2+a4^2 \<in> zEven" by auto
          moreover have "2*a3*a4 \<in> zEven" by (auto simp add: zEven_def)
          ultimately have"a3^2+a4^2+2*a3*a4 \<in> zEven" by (rule even_plus_even)
          hence "(a3+a4)^2 \<in> zEven" by (auto simp add: zadd_power2 ac_simps)
          hence "a3+a4 \<in> zEven" by (auto simp add: power_preserves_even)
          with tmp ass show ?thesis by blast
        next
          assume "\<not> a1^2+a2^2 \<in> zEven"
          hence odd12: "a1^2+a2^2 \<in> zOdd" by (simp add: odd_iff_not_even)
          with ev1234 have "a1^2+a2^2+a3^2+a4^2-(a1^2+a2^2) \<in> zOdd"
            by (simp only: even_minus_odd)
          hence odd34: "a3^2+a4^2 \<in> zOdd" by auto
          show ?thesis
          proof (cases)
            assume ev1: "a1^2 \<in> zEven"
            with odd12 have odd2: "a2^2 \<in> zOdd" by (rule even_plus_odd_prop2)
            show ?thesis
            proof (cases)
              assume ev3: "a3^2 \<in> zEven"
              with odd34 have "a4^2 \<in> zOdd" by (rule even_plus_odd_prop2)
              with odd2 have "a2 \<in> zOdd \<and>  a4 \<in> zOdd" 
                by (auto simp add: power_preserves_odd)
              hence tmp: "a2+a4 \<in> zEven" by (simp only: odd_plus_odd)
              from ev3 ev1 have "a1 \<in> zEven \<and> a3 \<in> zEven"
                by (auto simp add: power_preserves_even)
              hence tmp2: "a1+a3 \<in> zEven" by (simp only: even_plus_even)
              from ass have "sum4sq(a1,a3,a2,a4)=p*x" 
                by (auto simp add: sum4sq_def)
              with tmp tmp2 show ?thesis by blast
            next
              assume "\<not> a3^2 \<in> zEven"
              hence odd3: "a3^2 \<in> zOdd" by (simp add: odd_iff_not_even)
              with odd34 have "a4^2 \<in> zEven" by (rule even_plus_odd_prop1)
              with ev1 have "a1 \<in> zEven \<and>  a4 \<in> zEven" 
                by (auto simp add: power_preserves_even)
              hence tmp: "a1+a4 \<in> zEven" by (simp only: even_plus_even)
              from odd2 odd3 have "a2 \<in> zOdd \<and> a3 \<in> zOdd"
                by (auto simp add: power_preserves_odd)
              hence tmp2: "a2+a3 \<in> zEven" by (simp only: odd_plus_odd)
              from ass have "sum4sq(a1,a4,a2,a3)=p*x" 
                by (auto simp add: sum4sq_def)
              with tmp tmp2 show ?thesis by blast
            qed
          next
            assume "\<not> a1^2 \<in> zEven"
            hence odd1: "a1^2 \<in> zOdd" by (simp add: odd_iff_not_even)
            with odd12 have ev2: "a2^2 \<in> zEven" by (rule even_plus_odd_prop1)
            show ?thesis
            proof (cases)
              assume ev3: "a3^2 \<in> zEven"
              with odd34 have "a4^2 \<in> zOdd" by (rule even_plus_odd_prop2)
              with odd1 have "a1 \<in> zOdd \<and>  a4 \<in> zOdd" 
                by (auto simp add: power_preserves_odd)
              hence tmp: "a1+a4 \<in> zEven" by (simp only: odd_plus_odd)
              from ev3 ev2 have "a2 \<in> zEven \<and> a3 \<in> zEven"
                by (auto simp add: power_preserves_even)
              hence tmp2: "a2+a3 \<in> zEven" by (simp only: even_plus_even)
              from ass have "sum4sq(a1,a4,a2,a3)=p*x" 
                by (auto simp add: sum4sq_def)
              with tmp tmp2 show ?thesis by blast
            next
              assume "\<not> a3^2 \<in> zEven"
              hence odd3: "a3^2 \<in> zOdd" by (simp add: odd_iff_not_even)
              with odd34 have "a4^2 \<in> zEven" by (rule even_plus_odd_prop1)
              with ev2 have "a2 \<in> zEven \<and> a4 \<in> zEven" 
                by (auto simp add: power_preserves_even)
              hence tmp: "a2+a4 \<in> zEven" by (simp only: even_plus_even)
              from odd1 odd3 have "a1 \<in> zOdd \<and> a3 \<in> zOdd"
                by (auto simp add: power_preserves_odd)
              hence tmp2: "a1+a3 \<in> zEven" by (simp only: odd_plus_odd)
              from ass have "sum4sq(a1,a3,a2,a4)=p*x" 
                by (auto simp add: sum4sq_def)
              with tmp tmp2 show ?thesis by blast
            qed
          qed
        qed
        then obtain b1 b2 b3 b4 where b: "sum4sq(b1,b2,b3,b4)=p*x \<and> 
          b1+b2 \<in> zEven \<and> b3+b4 \<in> zEven" by auto
        then obtain c1 c3 where c13: "b1+b2 = 2*c1 \<and> b3+b4 = 2*c3"
          by (auto simp add: zEven_def)
        have "2*b2 \<in> zEven \<and> 2*b4 \<in> zEven" by (auto simp add: zEven_def)
        with b have "b1+b2 - 2*b2 \<in> zEven \<and> b3+b4 - 2*b4 \<in> zEven"
          by (auto simp only: even_minus_even)
        moreover have "b1+b2 - 2*b2 = b1-b2 \<and> b3+b4 - 2*b4 = b3-b4" by auto
        ultimately have "b1-b2 \<in> zEven \<and> b3-b4 \<in> zEven" by simp
        then obtain c2 c4 where c24: "b1-b2 = 2*c2 \<and> b3-b4 = 2*c4"
          by (auto simp add: zEven_def)
        from evx obtain y where y: "x = 2*y" by (auto simp add: zEven_def)
        hence "4*(p*y) = 2*(p*x)" by (simp add: ac_simps)
        also from b have "\<dots> = 2*b1^2 + 2*b2^2 + 2*b3^2 + 2*b4^2"
          by (auto simp only: sum4sq_def)
        also have "\<dots> = (b1 + b2)^2 + (b1 - b2)^2 + (b3 + b4)^2 + (b3 - b4)^2"
          by (auto simp add: zadd_power2 zdiff_power2)
        also with c13 c24 have "\<dots> = 4*(c1^2 + c2^2 + c3^2 + c4^2)"
          by (auto simp add: power_mult_distrib)
        finally have "sum4sq(c1,c2,c3,c4) = p*y" by (auto simp add: sum4sq_def)
        moreover from y ass have "0 < y \<and> y < p \<and> (nat y) - 1 < (nat x) - 1" by arith
        ultimately show ?thesis by blast
      next
        assume "\<not> x \<in> zEven" 
        hence xodd: "x \<in> zOdd" by (simp add: odd_iff_not_even)
        with ass have "\<exists> c1 c2 c3 c4. 2*\<bar>a1-c1*x\<bar><x \<and> 2*\<bar>a2-c2*x\<bar><x
          \<and> 2*\<bar>a3-c3*x\<bar><x \<and> 2*\<bar>a4-c4*x\<bar><x"
          by (simp add: best_odd_division_abs)
        then obtain b1 c1 b2 c2 b3 c3 b4 c4 where 
          bc_def: "b1 = a1-c1*x \<and> b2 = a2-c2*x \<and> b3 = a3-c3*x \<and> b4 = a4-c4*x"
          and bc_abs: "2*\<bar>b1\<bar><x \<and> 2*\<bar>b2\<bar><x \<and> 2*\<bar>b3\<bar><x \<and> 2*\<bar>b4\<bar><x"
          by blast
        let ?B = "b1^2 + b2^2 + b3^2 + b4^2"
        let ?C = "c1^2 + c2^2 + c3^2 + c4^2"
        have "x dvd ?B"
        proof
          from bc_def ass have 
            "?B = p*x - 2*(a1*c1+a2*c2+a3*c3+a4*c4)*x + ?C*x^2"
            by (auto simp add: zdiff_power2 sum4sq_def 
              distrib_right power_mult_distrib)
          thus "?B = x*(p - 2*(a1*c1+a2*c2+a3*c3+a4*c4) + ?C*x)"
            by (auto simp add: ac_simps power2_eq_square
              distrib_left right_diff_distrib)
        qed
        then obtain y where y: "?B = x * y" by (auto simp add: dvd_def)
        let ?A1 = "a1*b1 + a2*b2 + a3*b3 + a4*b4"
        let ?A2 = "a1*b2 - a2*b1 - a3*b4 + a4*b3"
        let ?A3 = "a1*b3 + a2*b4 - a3*b1 - a4*b2"
        let ?A4 = "a1*b4 - a2*b3 + a3*b2 - a4*b1"
        let ?A = "sum4sq(?A1,?A2,?A3,?A4)"
        have "x dvd ?A1 \<and> x dvd ?A2 \<and> x dvd ?A3 \<and> x dvd ?A4"
        proof (safe)
          from bc_def have 
            "?A1 = (b1+c1*x)*b1 + (b2+c2*x)*b2 + (b3+c3*x)*b3 + (b4+c4*x)*b4"
            by simp
          also with y have "\<dots> = x*(y + c1*b1 + c2*b2 + c3*b3 + c4*b4)"
            by (auto simp add: distrib_left power2_eq_square ac_simps)
          finally show "x dvd ?A1" by auto
          from bc_def have 
            "?A2 = (b1+c1*x)*b2 - (b2+c2*x)*b1 - (b3+c3*x)*b4 + (b4+c4*x)*b3"
            by simp
          also have "\<dots> = x*(c1*b2 - c2*b1 - c3*b4 + c4*b3)"
            by (auto simp add: distrib_left right_diff_distrib ac_simps)
          finally show "x dvd ?A2" by auto
          from bc_def have 
            "?A3 = (b1+c1*x)*b3 + (b2+c2*x)*b4 - (b3+c3*x)*b1 - (b4+c4*x)*b2"
            by simp
          also have "\<dots> = x*(c1*b3 + c2*b4 - c3*b1 - c4*b2)"
            by (auto simp add: distrib_left right_diff_distrib ac_simps)
          finally show "x dvd ?A3" by auto
          from bc_def have 
            "?A4 = (b1+c1*x)*b4 - (b2+c2*x)*b3 + (b3+c3*x)*b2 - (b4+c4*x)*b1"
            by simp
          also have "\<dots> = x*(c1*b4 - c2*b3 + c3*b2 - c4*b1)"
            by (auto simp add: distrib_left right_diff_distrib ac_simps)
          finally show "x dvd ?A4" by auto
        qed
        then obtain d1 d2 d3 d4 where d: 
          "?A1=x*d1 \<and> ?A2=x*d2 \<and> ?A3=x*d3 \<and> ?A4=x*d4"
          by (auto simp add: dvd_def)
        let ?D = "sum4sq(d1,d2,d3,d4)"
        from d have "x^2*?D = ?A" 
          by (auto simp only: sum4sq_def power_mult_distrib distrib_left) 
        also have "\<dots> = sum4sq(a1,a2,a3,a4)*sum4sq(b1,b2,b3,b4)"
          by (simp only: mult_sum4sq)
        also with y ass have "\<dots> = (p*x)*(x*y)" by (auto simp add: sum4sq_def)
        also have "\<dots> = x^2*(p*y)" by (simp only: power2_eq_square ac_simps)
        finally have "x^2*(?D - p*y) = 0" by (auto simp add: right_diff_distrib)
        with ass have "?D = p*y" by auto
        moreover have y_l_x: "y < x"
        proof -
          have "4*b1^2 = (2*\<bar>b1\<bar>)^2 \<and> 4*b2^2 = (2*\<bar>b2\<bar>)^2 \<and> 
            4*b3^2 = (2*\<bar>b3\<bar>)^2 \<and> 4*b4^2 = (2*\<bar>b4\<bar>)^2" 
            by (auto simp add: power_mult_distrib abs_mult power2_abs)
          with bc_abs have "4*b1^2<x^2 \<and> 4*b2^2<x^2 \<and> 4*b3^2<x^2 \<and> 4*b4^2<x^2" 
            using power_strict_mono [of "2*\<bar>b\<bar>" x 2 for b]
            by auto
          hence "?B < x^2" by auto
          with y have "x*(x-y) > 0"
            by (auto simp add: power2_eq_square right_diff_distrib)
          moreover from ass have "x > 0" by simp
          ultimately show ?thesis by (auto dest: pos_zmult_pos)
        qed
        moreover have "y > 0"
        proof -
          have b2pos: "b1^2 \<ge> 0 \<and> b2^2 \<ge> 0 \<and> b3^2 \<ge> 0 \<and> b4^2 \<ge> 0" 
            by (auto simp add: zero_le_power2)
          hence "?B = 0 \<or> ?B > 0" by arith
          moreover
          { assume "?B = 0"
            moreover from b2pos have 
              "?B-b1^2 \<ge> 0 \<and> ?B-b2^2 \<ge> 0 \<and> ?B-b3^2 \<ge> 0 \<and> ?B-b4^2 \<ge> 0" by arith
            ultimately have "b1^2 \<le> 0 \<and> b2^2 \<le> 0 \<and> b3^2 \<le> 0 \<and> b4^2 \<le> 0" by auto
            with b2pos have  "b1^2 = 0 \<and> b2^2 = 0 \<and> b3^2 = 0 \<and> b4^2 = 0" by arith
            hence "b1 = 0 \<and> b2 = 0 \<and> b3 = 0 \<and> b4 = 0" by auto
            with bc_def have "x dvd a1 \<and> x dvd a2 \<and> x dvd a3 \<and> x dvd a4" 
              by auto
            hence "x^2 dvd a1^2 \<and> x^2 dvd a2^2 \<and> x^2 dvd a3^2 \<and> x^2 dvd a4^2" 
              by (auto simp only: zpower_zdvd_mono)
            hence "x^2 dvd a1^2+a2^2+a3^2+a4^2" by (simp only: dvd_add)
            with ass have "x^2 dvd p*x" by (auto simp only: sum4sq_def)
            hence "x*x dvd x*p" by (simp only: power2_eq_square ac_simps)
            with ass have "x dvd p" by (auto dest: zdvd_mult_cancel)
            moreover from ass prp have "x \<ge> 0 \<and> x \<noteq> 1 \<and> x \<noteq> p \<and> zprime p" by simp
            ultimately have "False" by (unfold zprime_def, auto) }
          moreover
          { assume "?B > 0"
            with y have "x*y > 0" by simp
            moreover from ass have "x > 0" by simp
            ultimately have ?thesis by (auto dest: pos_zmult_pos) }
          ultimately show ?thesis by auto
        qed
        moreover with y_l_x have "(nat y) - 1 < (nat x) - 1" by arith
        moreover from y_l_x ass have "y < p" by auto
        ultimately show ?thesis by blast
      qed
      thus "\<exists> y. nat y - 1 < nat x - 1 \<and> \<not> \<not> ?Q y" by blast
    qed
    with Qt show "False" by simp
  qed
  thus "is_sum4sq p" by (auto simp add: is_sum4sq_def)
qed

theorem four_squares: "(n::int) \<ge> 0 \<Longrightarrow> \<exists> a b c d. a^2 + b^2 + c^2 + d^2 = n"
proof -
  assume "n \<ge> 0"
  hence "n = 0 \<or> n > 0" by auto
  moreover
  { assume "n = 0"
    hence "n = sum4sq(0,0,0,0)" by (auto simp add: sum4sq_def) 
    hence "is_sum4sq n" by (auto simp add: is_sum4sq_def) }
  moreover
  { assume npos: "n > 0"
    hence "nat n \<noteq> 0" by simp
    then obtain ps where ps: "primel ps \<and> prod ps = nat n" 
      by (frule_tac a="nat n" in factor_exists_general, auto)
    have "primel ps \<Longrightarrow> is_sum4sq (int (prod ps))"
    proof (induct ps, auto)
      have "sum4sq(1,0,0,0) = 1" by (auto simp add: sum4sq_def)
      thus "is_sum4sq 1" by (auto simp add: is_sum4sq_def)
    next
      fix p ps
      let ?X = "int (prod ps)"
      assume "primel ps \<Longrightarrow> is_sum4sq ?X" and "primel (p#ps)"
      hence "prime p" and x: "is_sum4sq ?X" by (auto simp add: primel_hd_tl)
      hence "zprime (int p)" by (simp only: prime_impl_zprime_int)
      hence "is_sum4sq (int p)" by (rule zprime_is_sum4sq)
      with x have "is_sum4sq((int p)*?X)" by (simp add: is_mult_sum4sq)
      thus "is_sum4sq (int p * int (prod ps))" by (auto simp only: int_mult)
    qed
    with ps npos have "is_sum4sq n" by auto }
  ultimately have "is_sum4sq n" by auto
  thus ?thesis by (auto simp only: is_sum4sq_def sum4sq_def)
qed

end
