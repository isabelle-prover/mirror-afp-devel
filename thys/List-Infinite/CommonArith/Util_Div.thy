(*  Title:      Util_Div.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

header {* Results for division and modulo operators on integers *}

theory Util_Div
imports Util_Nat
begin



subsection {* Additional (in-)equalities with @{text div} and @{text mod} *}

thm Divides.mod_less_divisor
corollary Suc_mod_le_divisor: "0 < m \<Longrightarrow> Suc (n mod m) \<le> m" 
by (rule Suc_leI, rule mod_less_divisor)

thm Divides.mod_less
thm Divides.mod_less_divisor
lemma mod_less_dividend: "\<lbrakk> 0 < m; m \<le> n \<rbrakk> \<Longrightarrow> n mod m < (n::nat)" 
thm mod_less_divisor[of m n]
thm less_le_trans[OF mod_less_divisor[of m n]]
by (rule less_le_trans[OF mod_less_divisor])
thm Divides.mod_le_divisor
(*lemma mod_le_dividend: "n mod m \<le> (n::nat)"*)
lemmas mod_le_dividend = mod_less_eq_dividend



lemma diff_mod_le: "(t - r) mod m \<le> (t::nat)"
thm le_trans[OF mod_le_dividend, OF diff_le_self]
by (rule le_trans[OF mod_le_dividend, OF diff_le_self])


thm Divides.mult_div_cancel
(*corollary div_mult_cancel: "m div n * n = m - m mod (n::nat)"*)
lemmas div_mult_cancel = div_mod_equality'

lemma mod_0_div_mult_cancel: "(n mod (m::nat) = 0) = (n div m * m = n)"
apply (insert eq_diff_left_iff[OF mod_le_dividend le0, of n m])
apply (simp add: mult_commute mult_div_cancel)
done

thm Divides.mult_div_cancel
lemma div_mult_le: "(n::nat) div m * m \<le> n" 
by (simp add: mult_commute mult_div_cancel)
lemma less_div_Suc_mult: "0 < (m::nat) \<Longrightarrow> n < Suc (n div m) * m"
apply (simp add: mult_commute mult_div_cancel)
apply (rule less_add_diff)
by (rule mod_less_divisor)

lemma nat_ge2_conv: "((2::nat) \<le> n) = (n \<noteq> 0 \<and> n \<noteq> 1)"
by fastforce

lemma Suc0_mod: "m \<noteq> Suc 0 \<Longrightarrow> Suc 0 mod m = Suc 0"
by (case_tac m, simp_all)
corollary Suc0_mod_subst: "
  \<lbrakk> m \<noteq> Suc 0; P (Suc 0) \<rbrakk> \<Longrightarrow> P (Suc 0 mod m)"
thm subst[OF Suc0_mod[symmetric]]
by (blast intro: subst[OF Suc0_mod[symmetric]])
corollary Suc0_mod_cong: "
  m \<noteq> Suc 0 \<Longrightarrow> f (Suc 0 mod m) = f (Suc 0)"
thm arg_cong[OF Suc0_mod]
by (blast intro: arg_cong[OF Suc0_mod])

subsection {* Additional results for addition and subtraction with @{text mod} *}

thm Divides.mod_Suc
lemma mod_Suc_conv: "
  ((Suc a) mod m = (Suc b) mod m) = (a mod m = b mod m)"
by (simp add: mod_Suc)
thm mod_Suc_conv

thm mod_Suc
lemma mod_Suc': "
  0 < n \<Longrightarrow> Suc m mod n = (if m mod n < n - Suc 0 then Suc (m mod n) else 0)"
apply (simp add: mod_Suc)
apply (intro conjI impI)
 apply simp
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
done

lemma mod_add:"
  ((a + k) mod m = (b + k) mod m) = 
  ((a::nat) mod m = b mod m)"
by (induct "k", simp_all add: mod_Suc_conv)

corollary mod_sub_add: "
  k \<le> (a::nat) \<Longrightarrow>
  ((a - k) mod m = b mod m) = (a mod m = (b + k) mod m)"
thm mod_add[where m=m and a="a-k" and b=b and k=k, symmetric]
by (simp add: mod_add[where m=m and a="a-k" and b=b and k=k, symmetric])

thm
  mod_Suc_conv
  mod_add
  mod_sub_add


lemma mod_sub_eq_mod_0_conv: "
  a + b \<le> (n::nat) \<Longrightarrow> 
  ((n - a) mod m = b mod m) = ((n - (a + b)) mod m = 0)"
thm mod_add[of "n-(a+b)" b m 0]
by (insert mod_add[of "n-(a+b)" b m 0], simp)
lemma mod_sub_eq_mod_swap: "
  \<lbrakk> a \<le> (n::nat); b \<le> n \<rbrakk> \<Longrightarrow> 
  ((n - a) mod m = b mod m) = ((n - b) mod m = a mod m)"
thm mod_sub_add
by (simp add: mod_sub_add add_commute)

lemma le_mod_greater_imp_div_less: "
  \<lbrakk> a \<le> (b::nat); a mod m > b mod m \<rbrakk> \<Longrightarrow> a div m < b div m"
apply (rule ccontr, simp add: linorder_not_less)
thm mult_le_mono1[of "b div m" "a div m" m]
apply (drule mult_le_mono1[of "b div m" _ m])
thm add_less_le_mono[of "b mod m" "a mod m" "b div m * m" "a div m * m"]
apply (drule add_less_le_mono[of "b mod m" "a mod m" "b div m * m" "a div m * m"])
apply simp_all
done

lemma less_mod_ge_imp_div_less: "\<lbrakk> a < (b::nat); a mod m \<ge> b mod m \<rbrakk> \<Longrightarrow> a div m < b div m"
apply (case_tac "m = 0", simp)
thm mult_less_cancel2[THEN iffD1, THEN conjunct2]
apply (rule mult_less_cancel1[of m, THEN iffD1, THEN conjunct2])
apply (simp add: mult_div_cancel)
apply (rule order_less_le_trans[of _ "b - a mod m"])
apply (rule diff_less_mono)
apply simp+
done
corollary less_mod_0_imp_div_less: "\<lbrakk> a < (b::nat); b mod m = 0 \<rbrakk> \<Longrightarrow> a div m < b div m"
by (simp add: less_mod_ge_imp_div_less)

lemma mod_diff_right_eq: "
  (a::nat) \<le> b \<Longrightarrow> (b - a) mod m = (b - a mod m) mod m"
proof -
  assume a_as:"a \<le> b"
  have "(b - a) mod m = (b - a + a div m * m) mod m" by simp
  also have "\<dots> = (b + a div m * m - a) mod m" using a_as by simp
  also have "\<dots> = (b + a div m * m - (a div m * m + a mod m)) mod m" by simp
  also have "\<dots> = (b + a div m * m - a div m * m - a mod m) mod m" 
    thm diff_diff_left[symmetric]
    by (simp only: diff_diff_left[symmetric])
  also have "\<dots> = (b - a mod m) mod m" by simp
  finally show ?thesis .
qed
corollary mod_eq_imp_diff_mod_eq: "
  \<lbrakk> x mod m = y mod m; x \<le> (t::nat); y \<le> t \<rbrakk> \<Longrightarrow> 
  (t - x) mod m = (t - y) mod m"
thm mod_diff_right_eq
by (simp only: mod_diff_right_eq)
lemma mod_eq_imp_diff_mod_eq2: "
  \<lbrakk> x mod m = y mod m; (t::nat) \<le> x; t \<le> y \<rbrakk> \<Longrightarrow> 
  (x - t) mod m = (y - t) mod m"
apply (case_tac "m = 0", simp+)
thm mod_mult_self2[of "x - t" m t]
apply (subst mod_mult_self2[of "x - t" m t, symmetric])
apply (subst mod_mult_self2[of "y - t" m t, symmetric])
apply (simp only: add_diff_assoc2 diff_add_assoc gr0_imp_self_le_mult2)
apply (simp only: mod_add)
done
thm 
  mod_diff_right_eq
  mod_eq_imp_diff_mod_eq
  mod_eq_imp_diff_mod_eq2


lemma divisor_add_diff_mod_if: "
  (m + b mod m - a mod m) mod (m::nat)= (
  if a mod m \<le> b mod m 
  then (b mod m - a mod m) 
  else (m + b mod m - a mod m))"
apply (case_tac "m = 0", simp)
apply clarsimp
apply (subst diff_add_assoc, assumption)
apply (simp only: mod_add_self1)
apply (rule mod_less)
thm less_imp_diff_less
apply (simp add: less_imp_diff_less)
done
corollary divisor_add_diff_mod_eq1: "
  a mod m \<le> b mod m \<Longrightarrow> 
  (m + b mod m - a mod m) mod (m::nat) = b mod m - a mod m"
by (simp add: divisor_add_diff_mod_if)
corollary divisor_add_diff_mod_eq2: "
  b mod m < a mod m \<Longrightarrow> 
  (m + b mod m - a mod m) mod (m::nat) = m + b mod m - a mod m"
by (simp add: divisor_add_diff_mod_if)

lemma mod_add_mod_if: "
  (a mod m + b mod m) mod (m::nat)= (
  if a mod m + b mod m < m
  then a mod m + b mod m 
  else a mod m + b mod m - m)"
apply (case_tac "m = 0", simp_all)
apply (clarsimp simp: linorder_not_less)
apply (simp add: mod_if[of "a mod m + b mod m"])
apply (rule mod_less)
thm diff_less_conv[THEN iffD2]
apply (rule diff_less_conv[THEN iffD2], assumption)
apply (simp add: add_less_mono)
done
corollary mod_add_mod_eq1: "
  a mod m + b mod m < m \<Longrightarrow> 
  (a mod m + b mod m) mod (m::nat) = a mod m + b mod m"
by (simp add: mod_add_mod_if)
corollary mod_add_mod_eq2: "
  m \<le> a mod m + b mod m\<Longrightarrow> 
  (a mod m + b mod m) mod (m::nat) = a mod m + b mod m - m"
by (simp add: mod_add_mod_if)

thm Divides.mod_add_eq
lemma mod_add1_eq_if: "
  (a + b) mod (m::nat) = (
  if (a mod m + b mod m < m) then a mod m + b mod m
  else a mod m + b mod m - m)"
by (simp add: mod_add_eq[of a b] mod_add_mod_if)

lemma mod_add_eq_mod_conv: "0 < (m::nat) \<Longrightarrow> 
  ((x + a) mod m = b mod m ) =
  (x mod m = (m + b mod m - a mod m) mod m)"
apply (simp only: mod_add_eq[of x a])
apply (rule iffI)
 apply (drule sym)
 thm mod_add_mod_if[of x m a]
 apply (simp add: mod_add_mod_if)
thm mod_add_left_eq[symmetric]
thm le_add_diff_inverse2[OF trans_le_add1[OF mod_le_divisor], of m]
apply (simp add: mod_add_left_eq[symmetric] le_add_diff_inverse2[OF trans_le_add1[OF mod_le_divisor]])
done




lemma mod_diff1_eq: "
  (a::nat) \<le> b \<Longrightarrow> (b - a) mod m = (m + b mod m - a mod m) mod m"
apply (case_tac "m = 0", simp)
apply simp
proof -
  assume a_as:"a \<le> b"
    and m_as: "0 < m"
  have a_mod_le_b_s: "a mod m \<le> b"
    by (rule le_trans[of _ a], simp only: mod_le_dividend, simp only: a_as)
  have "(b - a) mod m = (b - a mod m) mod m"
    using a_as by (simp only: mod_diff_right_eq)
  also have "\<dots> = (b - a mod m + m) mod m"
    by simp
  thm diff_add_assoc2[of "a mod m" b m, symmetric ]
  also have "\<dots> = (b + m - a mod m) mod m"
    using a_mod_le_b_s by simp
  thm mod_div_equality
  also have "\<dots> = (b div m * m + b mod m + m - a mod m) mod m"
    by simp
  thm diff_add_assoc[of "a mod m" "b mod m + m"]
  also have "\<dots> = (b div m * m + (b mod m + m - a mod m)) mod m"
    thm diff_add_assoc[OF mod_le_divisor, OF m_as]
    by (simp add: diff_add_assoc[OF mod_le_divisor, OF m_as])
  also have "\<dots> = ((b mod m + m - a mod m) + b div m * m) mod m"
    by simp
  also have "\<dots> = (b mod m + m - a mod m) mod m"
    by simp
  also have "\<dots> = (m + b mod m - a mod m) mod m"
    by (simp only: add_commute)
  finally show ?thesis .
qed
thm divisor_add_diff_mod_if
corollary mod_diff1_eq_if: "
  (a::nat) \<le> b \<Longrightarrow> (b - a) mod m = (
    if a mod m \<le> b mod m then b mod m - a mod m
    else m + b mod m - a mod m)"
by (simp only: mod_diff1_eq divisor_add_diff_mod_if)
corollary mod_diff1_eq1: "
  \<lbrakk> (a::nat) \<le> b; a mod m \<le> b mod m \<rbrakk> 
  \<Longrightarrow> (b - a) mod m = b mod m - a mod m"
by (simp add: mod_diff1_eq_if)
corollary mod_diff1_eq2: "
  \<lbrakk> (a::nat) \<le> b; b mod m < a mod m\<rbrakk> 
  \<Longrightarrow> (b - a) mod m = m + b mod m - a mod m"
by (simp add: mod_diff1_eq_if)






subsubsection {* Divisor subtraction with @{text div} and @{text mod} *}

thm 
  Divides.mod_add_self1
  Divides.mod_add_self2
  Divides.mod_mult_self1
  Divides.mod_mult_self2
thm mod_diff1_eq2
lemma mod_diff_self1: "
  0 < (n::nat) \<Longrightarrow> (m - n) mod m = m - n"
by (case_tac "m = 0", simp_all)
lemma mod_diff_self2: "
  m \<le> (n::nat) \<Longrightarrow> (n - m) mod m = n mod m"
thm mod_diff_right_eq[of m n m]
by (simp add: mod_diff_right_eq)
lemma mod_diff_mult_self1: "
  k * m \<le> (n::nat) \<Longrightarrow> (n - k * m) mod m = n mod m"
thm mod_diff_right_eq[of m n m]
by (simp add: mod_diff_right_eq)
lemma mod_diff_mult_self2: "
  m * k \<le> (n::nat) \<Longrightarrow> (n - m * k) mod m = n mod m"
by (simp only: mult_commute[of m k] mod_diff_mult_self1)

thm 
  Divides.div_add_self1
  Divides.div_add_self2
  Divides.div_mult_self1
  Divides.div_mult_self2
thm div_0
lemma div_diff_self1: "0 < (n::nat) \<Longrightarrow> (m - n) div m = 0"
by (case_tac "m = 0", simp_all)
lemma div_diff_self2: "(n - m) div m = n div m - Suc 0"
apply (case_tac "m = 0", simp)
apply (case_tac "n < m", simp)
apply (case_tac "n = m", simp)
thm div_if
apply (simp add: div_if)
done

lemma div_diff_mult_self1: "
  (n - k * m) div m = n div m - (k::nat)"
apply (case_tac "m = 0", simp)
apply (case_tac "n < k * m")
 apply simp
 thm div_le_mono[OF less_imp_le]
 apply (drule div_le_mono[OF less_imp_le, of n _ m])
 apply simp
apply (simp add: linorder_not_less)
thm iffD1[OF mult_cancel1_gr0[where k=m]]
apply (rule iffD1[OF mult_cancel1_gr0[where k=m]], assumption)
thm diff_mult_distrib2
apply (subst diff_mult_distrib2)
thm mult_div_cancel[of m "n - k * m"]
apply (simp only: mult_div_cancel)
apply (simp only: diff_commute[of _ "k*m"])
apply (simp only: mult_commute[of m])
thm mod_diff_mult_self1
apply (simp only: mod_diff_mult_self1)
done
lemma div_diff_mult_self2: "
  (n - m * k) div m = n div m - (k::nat)"
by (simp only: mult_commute div_diff_mult_self1)



subsubsection {* Modulo equality and modulo of difference*}

lemma mod_eq_imp_diff_mod_0:"
  (a::nat) mod m = b mod m \<Longrightarrow> (b - a) mod m = 0"
  (is "?P \<Longrightarrow> ?Q")
proof -
  assume as1: ?P
  thm mod_div_equality
  have "b - a = b div m * m + b mod m - (a div m * m + a mod m)"
    by simp
  also have "\<dots> = b div m * m + b mod m - (a mod m + a div m * m)" 
    by simp
  also have "\<dots> = b div m * m + b mod m - a mod m - a div m * m"
    by simp
  also have "\<dots> = b div m * m + b mod m - b mod m - a div m * m"
    using as1 by simp
  also have "\<dots> = b div m * m - a div m * m"
    by (simp only: diff_add_inverse2)
  also have "\<dots> = (b div m - a div m) * m" 
    by (simp only: diff_mult_distrib)
  finally have "b - a = (b div m - a div m) * m" .
  hence "(b - a) mod m = (b div m - a div m) * m mod m"
    by (rule arg_cong)
  thus ?thesis by (simp only: mod_mult_self2_is_0)
qed
corollary mod_eq_imp_diff_dvd: "
  (a::nat) mod m = b mod m \<Longrightarrow> m dvd b - a"
by (rule dvd_eq_mod_eq_0[THEN iffD2, OF mod_eq_imp_diff_mod_0])

thm mod_diff1_eq
lemma mod_neq_imp_diff_mod_neq0:"
  \<lbrakk> (a::nat) mod m \<noteq> b mod m; a \<le> b \<rbrakk> \<Longrightarrow> 0 < (b - a) mod m"
apply (case_tac "m = 0", simp)
apply (drule le_imp_less_or_eq, erule disjE)
 prefer 2 
 apply simp
apply (drule neq_iff[THEN iffD1], erule disjE)
 thm mod_diff1_eq1
 apply (simp add: mod_diff1_eq1)
thm mod_diff1_eq2[OF less_imp_le]
thm trans_less_add1[OF mod_less_divisor]
apply (simp add: mod_diff1_eq2[OF less_imp_le] trans_less_add1[OF mod_less_divisor])
done
corollary mod_neq_imp_diff_not_dvd:"
  \<lbrakk> (a::nat) mod m \<noteq> b mod m; a \<le> b \<rbrakk> \<Longrightarrow> \<not> m dvd b - a"
thm dvd_eq_mod_eq_0
by (simp add: dvd_eq_mod_eq_0 mod_neq_imp_diff_mod_neq0)

lemma diff_mod_0_imp_mod_eq:"
  \<lbrakk> (b - a) mod m = 0; a \<le> b \<rbrakk> \<Longrightarrow> (a::nat) mod m = b mod m"
apply (rule ccontr)
thm mod_neq_imp_diff_mod_neq0
apply (drule mod_neq_imp_diff_mod_neq0)
apply simp_all
done
corollary diff_dvd_imp_mod_eq:"
  \<lbrakk> m dvd b - a; a \<le> b \<rbrakk> \<Longrightarrow> (a::nat) mod m = b mod m"
thm dvd_eq_mod_eq_0[THEN iffD1, THEN diff_mod_0_imp_mod_eq]
by (rule dvd_eq_mod_eq_0[THEN iffD1, THEN diff_mod_0_imp_mod_eq])



thm 
  mod_eq_imp_diff_mod_0
  diff_mod_0_imp_mod_eq
lemma mod_eq_diff_mod_0_conv: "
  a \<le> (b::nat) \<Longrightarrow> (a mod m = b mod m) = ((b - a) mod m = 0)"
apply (rule iffI)
apply (rule mod_eq_imp_diff_mod_0, assumption)
apply (rule diff_mod_0_imp_mod_eq, assumption+)
done
corollary mod_eq_diff_dvd_conv: "
  a \<le> (b::nat) \<Longrightarrow> (a mod m = b mod m) = (m dvd b - a)"
thm dvd_eq_mod_eq_0[symmetric, THEN subst]
by (rule dvd_eq_mod_eq_0[symmetric, THEN subst], rule mod_eq_diff_mod_0_conv)



subsection {* Some additional lemmata about integer @{text div} and @{text mod} *}

lemma zmod_eq_imp_diff_mod_0:"
  (a::int) mod m = b mod m \<Longrightarrow> (b - a) mod m = 0"
apply (simp only: diff_minus)
thm mod_add_eq[of b "-a" m]
apply (simp only: mod_add_eq[of b "-a" m])
thm zmod_zminus1_eq_if
apply (simp add: zmod_zminus1_eq_if)
done

thm 
  zmod_eq_imp_diff_mod_0[of "a::int" m b]
  mod_eq_imp_diff_mod_0[of "a::nat" m b]

thm Divides.nat_mod_distrib
lemma "\<lbrakk> 0 \<le> (n::int); 0 \<le> m \<rbrakk> \<Longrightarrow> nat (n mod m) = nat n mod nat m"
by (blast intro: nat_mod_distrib)

(*lemma int_mod_distrib: "int (n mod m) = int n mod int m"*)
lemmas int_mod_distrib = zmod_int

lemma zdiff_mod_0_imp_mod_eq__pos:"
  \<lbrakk> (b - a) mod m = 0; 0 < (m::int) \<rbrakk> \<Longrightarrow> a mod m = b mod m"
  (is "\<lbrakk> ?P; ?Pm \<rbrakk> \<Longrightarrow> ?Q")
proof -
  assume as1: ?P
    and as2: "0 < m"

  obtain r1 where a_r1:"r1 = a mod m" by blast
  obtain r2 where b_r2:"r2 = b mod m" by blast

  obtain q1 where a_q1: "q1 = a div m" by blast
  obtain q2 where b_q2: "q2 = b div m" by blast

  have a_r1_q1: "a = m * q1 + r1" 
    using a_r1 a_q1 by simp
  have b_r2_q2: "b = m * q2 + r2"
    using b_r2 b_q2 by simp

  thm divmod_int_rel_div_mod[of m a]
  thm Divides.divmod_int_rel_def

  have "b - a = m * q2 + r2 - (m * q1 + r1)"
    using a_r1_q1 b_r2_q2 by simp
  also have "\<dots> = m * q2 + r2 - m * q1 - r1"
    by simp
  also have "\<dots> = m * q2 - m * q1 + r2 - r1"
    by simp
  finally have "b - a = m * (q2 - q1) + (r2 - r1)"
    by (simp add: zdiff_zmult_distrib2)
  hence "(b - a) mod m = (r2 - r1) mod m"
    by (simp add: mod_add_eq)
  hence r2_r1_mod_m_0:"(r2 - r1) mod m = 0" (is "?R1")
    by (simp only: as1)

  have "r1 = r2"
    thm notI[of "r1 \<noteq> r2", simplified]
  proof (rule notI[of "r1 \<noteq> r2", simplified])
    assume as1': "r1 \<noteq> r2"
    have diff_le_s: "\<And>a b (m::int). \<lbrakk> 0 \<le> a; b < m \<rbrakk> \<Longrightarrow> b - a < m"
      by simp
    have s_r1:"0 \<le> r1 \<and> r1 < m" and s_r2:"0 \<le> r2 \<and> r2 < m"
      thm pos_mod_conj
      by (simp add: as2 a_r1 b_r2 pos_mod_conj)+
    have mr2r1:"-m < r2 - r1" and r2r1m:"r2 - r1 < m"
      thm minus_less_iff[of m]
      thm diff_le_s
      by (simp add: minus_less_iff[of m] s_r1 s_r2 diff_le_s)+
    have "0 \<le> r2 - r1 \<Longrightarrow> (r2 - r1) mod m = (r2 - r1)"
      thm mod_pos_pos_trivial[of "r2-r1" m]
      using r2r1m by (blast intro: mod_pos_pos_trivial)
    hence s1_pos: "0 \<le> r2 - r1 \<Longrightarrow> r2 - r1 = 0"
      using r2_r1_mod_m_0 by simp
    
    have "(r2-r1) mod -m = 0"
      thm zmod_zminus2_eq_if[of "r2-r1" m, simplified]
      by (simp add: zmod_zminus2_eq_if[of "r2-r1" m, simplified] r2_r1_mod_m_0)
    moreover
    have "r2 - r1 \<le> 0 \<Longrightarrow> (r2 - r1) mod -m = r2 - r1"
      using mr2r1
      thm mod_neg_neg_trivial[of "r2-r1" "-m"]
      by (simp add: mod_neg_neg_trivial)
    ultimately have s1_neg:"r2 - r1 \<le> 0 \<Longrightarrow> r2 - r1 = 0"
      by simp
    
    have "r2 - r1 = 0"
      using s1_pos s1_neg zle_linear by blast
    hence "r1 = r2" by simp
    thus False
      using as1' by blast
  qed
  thus ?thesis
    using a_r1 b_r2 by blast
qed

lemma zmod_zminus_eq_conv_pos: "
  0 < (m::int) \<Longrightarrow> (a mod - m = b mod - m) = (a mod m = b mod m)"
apply (simp only: zmod_zminus2 neg_equal_iff_equal)
thm zmod_zminus1_eq_if[of _ m]
apply (simp only: zmod_zminus1_eq_if)
apply (split split_if)+
apply (safe, simp_all)
thm pos_mod_bound[of m]
apply (insert pos_mod_bound[of m a] pos_mod_bound[of m b], simp_all)
done
lemma zmod_zminus_eq_conv: "
  ((a::int) mod - m = b mod - m) = (a mod m = b mod m)"
apply (insert zless_linear[of 0 m], elim disjE)
apply (blast dest: zmod_zminus_eq_conv_pos)
apply simp
thm zmod_zminus_eq_conv_pos[of "-m", symmetric]
apply (simp add: zmod_zminus_eq_conv_pos[of "-m", symmetric])
done

lemma zdiff_mod_0_imp_mod_eq:"
  (b - a) mod m = 0 \<Longrightarrow> (a::int) mod m = b mod m"
by (metis dvd_eq_mod_eq_0 zmod_eq_dvd_iff)
thm zdiff_mod_0_imp_mod_eq

thm 
  zmod_eq_imp_diff_mod_0
  zdiff_mod_0_imp_mod_eq
lemma zmod_eq_diff_mod_0_conv: "
  ((a::int) mod m = b mod m) = ((b - a) mod m = 0)"
apply (rule iffI)
apply (rule zmod_eq_imp_diff_mod_0, assumption)
apply (rule zdiff_mod_0_imp_mod_eq, assumption)
done

lemma "\<not>(\<exists>(a::int) b m. (b - a) mod m = 0 \<and> a mod m \<noteq> b mod m)"
by (simp add: zmod_eq_diff_mod_0_conv)
lemma "\<exists>(a::nat) b m. (b - a) mod m = 0 \<and> a mod m \<noteq> b mod m"
apply (rule_tac x=1 in exI)
apply (rule_tac x=0 in exI)
apply (rule_tac x=2 in exI)
apply simp
done

thm
  zdiff_mod_0_imp_mod_eq[of "b::int" a m]
  diff_mod_0_imp_mod_eq[of "b::nat" a m]




lemma zmult_div_leq_mono:"
  \<lbrakk> (0::int) \<le> x; a \<le> b; 0 < d \<rbrakk> \<Longrightarrow> x * a div d \<le> x * b div d"
by (metis mult_right_mono zdiv_mono1 zmult_commute)

lemma zmult_div_leq_mono_neg:"
  \<lbrakk> x \<le> (0::int); a \<le> b; 0 < d \<rbrakk> \<Longrightarrow> x * b div d \<le> x * a div d"
by (metis mult_left_mono_neg zdiv_mono1)

lemma zmult_div_pos_le:"
  \<lbrakk> (0::int) \<le> a; 0 \<le> b; b \<le> c \<rbrakk> \<Longrightarrow> a * b div c \<le> a"
apply (case_tac "b = 0", simp)
apply (subgoal_tac "b * a \<le> c * a")
 prefer 2 
 apply (simp only: mult_right_mono)
apply (simp only: zmult_commute)
apply (subgoal_tac "a * b div c \<le> a * c div c")
 prefer 2 
 thm zdiv_mono1
 apply (simp only: zdiv_mono1)
apply simp
done

lemma zmult_div_neg_le:"
  \<lbrakk> a \<le> (0::int); 0 < c; c \<le> b \<rbrakk> \<Longrightarrow> a * b div c \<le> a"
apply (subgoal_tac "b * a \<le> c * a")
 prefer 2 
 apply (simp only: mult_right_mono_neg)
apply (simp only:zmult_commute)
apply (subgoal_tac "a * b div c \<le> a * c div c")
 prefer 2 
 thm zdiv_mono1 
 apply (simp only: zdiv_mono1)
apply simp
done

lemma zmult_div_ge_0:"\<lbrakk> (0::int) \<le> x; 0 \<le> a; 0 < c \<rbrakk> \<Longrightarrow> 0 \<le> a * x div c"
by (metis pos_imp_zdiv_nonneg_iff split_mult_pos_le)

corollary zmult_div_plus_ge_0: "
  \<lbrakk> (0::int) \<le> x; 0 \<le> a; 0 \<le> b; 0 < c\<rbrakk> \<Longrightarrow> 0 \<le> a * x div c + b"
by (insert zmult_div_ge_0[of x a c], simp)




lemma zmult_div_abs_ge: "
  \<lbrakk> (0::int) \<le> b; b \<le> b'; 0 \<le> a; 0 < c\<rbrakk> \<Longrightarrow>
  \<bar>a * b div c\<bar> \<le> \<bar>a * b' div c\<bar>"
thm zmult_div_ge_0[of b a c]
apply (insert zmult_div_ge_0[of b a c] zmult_div_ge_0[of "b'" a c], simp)
by (metis zmult_div_leq_mono)

lemma zmult_div_plus_abs_ge: " 
  \<lbrakk> (0::int) \<le> b; b \<le> b'; 0 \<le> a; 0 < c \<rbrakk> \<Longrightarrow>
  \<bar>a * b div c + a\<bar> \<le> \<bar>a * b' div c + a\<bar>"
thm zmult_div_plus_ge_0
apply (insert zmult_div_plus_ge_0[of b a a c] zmult_div_plus_ge_0[of "b'" a a c], simp)
by (metis zmult_div_leq_mono)
thm zmult_div_plus_abs_ge

subsection {* Some further (in-)equality results for @{text div} and @{text mod} *}

lemma less_mod_eq_imp_add_divisor_le: "
  \<lbrakk> (x::nat) < y; x mod m = y mod m \<rbrakk> \<Longrightarrow> x + m \<le> y"
apply (case_tac "m = 0")
 apply simp
thm contrapos_pp[of "x mod m = y mod m"]
apply (rule contrapos_pp[of "x mod m = y mod m"])
 apply blast
apply (rule ccontr, simp only: not_not, clarify)
proof -
  assume m_greater_0: "0 < m"
  assume x_less_y:"x < y"
  hence y_x_greater_0:"0 < y - x"
    by simp
  assume "x mod m = y mod m"
  hence y_x_mod_m: "(y - x) mod m = 0"
    thm mod_eq_imp_diff_mod_0
    by (simp only: mod_eq_imp_diff_mod_0)
  assume "\<not> x + m \<le> y"
  hence "y < x + m" by simp
  hence "y - x < x + m - x"
    by (simp add: diff_add_inverse diff_less_conv m_greater_0)
  hence y_x_less_m: "y - x < m"
    by simp
  thm y_x_greater_0 y_x_less_m
  thm mod_less[of "y - x" m]
  have "(y - x) mod m = y - x" 
    using y_x_less_m by simp
  hence "y - x = 0"
    using y_x_mod_m by simp
  thus False
    using y_x_greater_0 by simp
qed


lemma less_div_imp_mult_add_divisor_le: "
  (x::nat) < n div m \<Longrightarrow> x * m + m \<le> n"
apply (case_tac "m = 0", simp)
apply (case_tac "n < m", simp)
apply (simp add: linorder_not_less)
apply (subgoal_tac "m \<le> n - n mod m")
 prefer 2
 apply (drule div_le_mono[of m _ m])
 apply (simp only: div_self)
 apply (drule mult_le_mono2[of 1 _ m])
 apply (simp only: mult_1_right mult_div_cancel)
apply (drule less_imp_le_pred[of x])
apply (drule mult_le_mono2[of x _ m])
apply (simp add: diff_mult_distrib2 mult_div_cancel del: diff_diff_left)
thm le_diff_conv2[of m]
apply (simp only: le_diff_conv2[of m])
thm le_diff_imp_le[of "m * x + m"]
apply (drule le_diff_imp_le[of "m * x + m"])
apply (simp only: mult_commute[of _ m])
done

lemma mod_add_eq_imp_mod_0: "
  ((n + k) mod (m::nat) = n mod m) = (k mod m = 0)"
by (metis add_eq_if mod_add mod_add_self1 mod_self nat_add_commute)

lemma between_imp_mod_between: "
  \<lbrakk> b < (m::nat); m * k + a \<le> n; n \<le> m * k + b \<rbrakk> \<Longrightarrow>
  a \<le> n mod m \<and> n mod m \<le> b"
apply (case_tac "m = 0", simp_all)
apply (frule gr_implies_gr0)
apply (subgoal_tac "k = n div m")
 prefer 2
 apply (rule split_div_lemma[THEN iffD1], assumption)
 apply simp
apply clarify
apply (rule conjI)
apply (rule add_le_imp_le_left[where c="m * (n div m)"], simp)+
done

corollary between_imp_mod_le: "
  \<lbrakk> b < (m::nat); m * k \<le> n; n \<le> m * k + b \<rbrakk> \<Longrightarrow> n mod m \<le> b"
by (insert between_imp_mod_between[of b m k 0 n], simp)
corollary between_imp_mod_gr0: "
  \<lbrakk> (m::nat) * k < n; n < m * k + m \<rbrakk> \<Longrightarrow> 0 < n mod m"
apply (case_tac "m = 0", simp_all)
apply (rule Suc_le_lessD)
apply (rule between_imp_mod_between[THEN conjunct1, of "m - Suc 0" m k "Suc 0" n])
apply simp_all
done

text {* Some variations of @{term split_div_lemma} *}
corollary le_less_div_conv: "
  0 < m \<Longrightarrow> (k * m \<le> n \<and> n < Suc k * m) = (n div m = k)"
by (metis div_mult_le nat_mult_commute split_div_lemma)
lemma le_less_imp_div: "
  \<lbrakk> k * m \<le> n; n < Suc k * m \<rbrakk> \<Longrightarrow> n div m = k"
by (metis gr_implies_not0 mult_eq_if nat_mult_commute neq0_conv split_div_lemma)
lemma div_imp_le_less: "
  \<lbrakk> n div m = k; 0 < m \<rbrakk> \<Longrightarrow> k * m \<le> n \<and> n < Suc k * m"
thm le_less_div_conv[THEN iffD2]
by (rule le_less_div_conv[THEN iffD2])




lemma div_le_mod_le_imp_le: "
  \<lbrakk> (a::nat) div m \<le> b div m; a mod m \<le> b mod m \<rbrakk> \<Longrightarrow> a \<le> b"
apply (rule subst[OF mod_div_equality2[of m a]])
apply (rule subst[OF mod_div_equality2[of m b]])
apply (rule add_le_mono)
apply (rule mult_le_mono2)
apply assumption+
done

lemma le_mod_add_eq_imp_add_mod_le: "
  \<lbrakk> a \<le> b; (a + k) mod m = (b::nat) mod m \<rbrakk> \<Longrightarrow> a + k mod m \<le> b"
by (metis add_le_mono2 diff_add_inverse le_add1 le_add_diff_inverse mod_diff1_eq mod_less_eq_dividend)

corollary mult_divisor_le_mod_ge_imp_ge: "
  \<lbrakk> (m::nat) * k \<le> n; r \<le> n mod m \<rbrakk> \<Longrightarrow> m * k + r \<le> n"
apply (insert le_mod_add_eq_imp_add_mod_le[of "m * k" n "n mod m" m])
apply (simp add: add_commute[of "m * k"])
done




subsection {* Additional multiplication results for @{text mod} and @{text div} *}

lemma mod_0_imp_mod_mult_right_0: "
  n mod m = (0::nat) \<Longrightarrow> n * k mod m = 0"
by fastforce
lemma mod_0_imp_mod_mult_left_0: "
  n mod m = (0::nat) \<Longrightarrow> k * n mod m = 0"
by fastforce

lemma mod_0_imp_div_mult_left_eq: "
  n mod m = (0::nat) \<Longrightarrow> k * n div m = k * (n div m)"
by fastforce
lemma mod_0_imp_div_mult_right_eq: "
  n mod m = (0::nat) \<Longrightarrow> n * k div m = k * (n div m)"
by fastforce


thm Rings.dvd_mult_left
lemma mod_0_imp_mod_factor_0_left: "
  n mod (m * m') = (0::nat) \<Longrightarrow> n mod m = 0"
by fastforce
lemma mod_0_imp_mod_factor_0_right: "
  n mod (m * m') = (0::nat) \<Longrightarrow> n mod m' = 0"
by fastforce




subsection {* Some factor distribution facts for @{text mod}*}

lemma mod_eq_mult_distrib: "
  (a::nat) mod m = b mod m \<Longrightarrow> 
  a * k mod (m * k) = b * k mod (m * k)"
by simp

lemma mod_mult_eq_imp_mod_eq: "
  (a::nat) mod (m * k) = b mod (m * k) \<Longrightarrow> a mod m = b mod m"
thm mod_mult2_eq[of a m k]
apply (simp only: mod_mult2_eq)
thm arg_cong[where f="\<lambda>x. x mod m"]
apply (drule_tac arg_cong[where f="\<lambda>x. x mod m"])
apply (simp add: add_commute)
done
corollary mod_eq_mod_0_imp_mod_eq: "
  \<lbrakk> (a::nat) mod m' = b mod m'; m' mod m = 0 \<rbrakk> 
  \<Longrightarrow> a mod m = b mod m"
by (clarify, drule mod_mult_eq_imp_mod_eq)

lemma mod_factor_imp_mod_0: "
  \<lbrakk>(x::nat) mod (m * k) = y * k mod (m * k)\<rbrakk> \<Longrightarrow> x mod k = 0"
  (is "\<lbrakk> ?P1 \<rbrakk> \<Longrightarrow> ?Q")
proof -
  assume as1: ?P1
  thm mod_mult_distrib[where m=y and n=m and k=k]
  have "y * k mod (m * k) = y mod m * k"
    by simp
  hence "x mod (m * k) = y mod m * k"
    using as1 by simp
  hence "y mod m * k = k * (x div k mod m) + x mod k" (is "?l1 = ?r1")
    by (simp only: mult_ac mod_mult2_eq)
  hence "(y mod m * k) mod k = ?r1 mod k"
    by simp
  hence "0 = ?r1 mod k"
    by simp
  thus "x mod k = 0"
    thm mod_add_eq
    by (simp add: mod_add_eq)
qed
corollary mod_factor_div: "
  \<lbrakk>(x::nat) mod (m * k) = y * k mod (m * k)\<rbrakk> \<Longrightarrow> x div k * k = x"
thm mod_factor_imp_mod_0[THEN mod_0_div_mult_cancel[THEN iffD1]]
by (blast intro: mod_factor_imp_mod_0[THEN mod_0_div_mult_cancel[THEN iffD1]])

lemma mod_factor_div_mod:"
  \<lbrakk> (x::nat) mod (m * k) = y * k mod (m * k); 0 < k \<rbrakk>
  \<Longrightarrow> x div k mod m = y mod m"
  (is "\<lbrakk> ?P1; ?P2 \<rbrakk> \<Longrightarrow> ?L = ?R")
proof -
  assume as1: ?P1
  assume as2: ?P2
  have x_mod_k_0: "x mod k = 0"
    using as1 by (blast intro: mod_factor_imp_mod_0)
  thm mod_mult2_eq[where a=x and b=k and c=m]
  have "?L * k + x mod k = x mod (k * m)"
    by (simp only: mod_mult2_eq mult_commute[of _ k])
  hence "?L * k = x mod (k * m)"
    using x_mod_k_0 by simp
  hence "?L * k = y * k mod (m * k)"
    using as1 by (simp only: mult_ac)
  hence "?L * k = y mod m * k"
    thm mod_mult_distrib
    by (simp only: mod_mult_distrib)
  thus ?thesis
    using as2 by simp
qed

thm
  Divides.mod_mult_distrib
  Divides.mod_mult_distrib2
thm 
  mod_eq_mult_distrib
thm
  mod_factor_imp_mod_0
  mod_factor_div
  mod_factor_div_mod




subsection {* More results about quotient @{text div} with addition and subtraction *}

thm Divides.div_add1_eq
thm mod_add1_eq_if
lemma div_add1_eq_if: "0 < m \<Longrightarrow> 
  (a + b) div (m::nat) = a div m + b div m + (
    if a mod m + b mod m < m then 0 else Suc 0)"
apply (simp only: div_add1_eq[of a b])
thm arg_cong[of "(a mod m + b mod m) div m"]
apply (rule arg_cong[of "(a mod m + b mod m) div m"])
apply (clarsimp simp: linorder_not_less)
thm le_less_imp_div[of "Suc 0" m "a mod m + b mod m"]
apply (rule le_less_imp_div[of "Suc 0" m "a mod m + b mod m"], simp)
apply simp
apply (simp only: add_less_mono[OF mod_less_divisor mod_less_divisor]) 
done
corollary div_add1_eq1: "
  a mod m + b mod m < (m::nat) \<Longrightarrow>
  (a + b) div (m::nat) = a div m + b div m"
apply (case_tac "m = 0", simp)
apply (simp add: div_add1_eq_if)
done
corollary div_add1_eq1_mod_0_left: "
  a mod m = 0 \<Longrightarrow> (a + b) div (m::nat) = a div m + b div m"
apply (case_tac "m = 0", simp)
apply (simp add: div_add1_eq1)
done
corollary div_add1_eq1_mod_0_right: "
  b mod m = 0 \<Longrightarrow> (a + b) div (m::nat) = a div m + b div m"
by (fastforce simp: div_add1_eq1_mod_0_left)
corollary div_add1_eq2: "
  \<lbrakk> 0 < m; (m::nat) \<le> a mod m + b mod m \<rbrakk> \<Longrightarrow>
  (a + b) div (m::nat) = Suc (a div m + b div m)"
by (simp add: div_add1_eq_if)

lemma div_Suc: "
  0 < n \<Longrightarrow> Suc m div n = (if Suc (m mod n) = n then Suc (m div n) else m div n)"
apply (drule Suc_leI, drule le_imp_less_or_eq)
apply (case_tac "n = Suc 0", simp)
apply (split split_if, intro conjI impI)
 apply (rule_tac t="Suc m" and s="m + 1" in subst, simp)
 apply (subst div_add1_eq2, simp+)
thm le_neq_trans[OF mod_less_divisor[THEN Suc_leI]]
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
apply (rule_tac t="Suc m" and s="m + 1" in subst, simp)
apply (subst div_add1_eq1, simp+)
done
lemma div_Suc': "
  0 < n \<Longrightarrow> Suc m div n = (if m mod n < n - Suc 0 then m div n else Suc (m div n))"
apply (simp add: div_Suc)
apply (intro conjI impI)
 apply simp
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
done

lemma div_diff1_eq_if: "
  (b - a) div (m::nat) = 
  b div m - a div m - (if a mod m \<le> b mod m then 0 else Suc 0)"
apply (case_tac "m = 0", simp)
apply (case_tac "b < a")
 apply (frule less_imp_le[of b])
 apply (frule div_le_mono[of _ _ m])
 apply simp
apply (simp only: linorder_not_less neq0_conv) 
proof -
  assume le_as: "a \<le> b"
    and m_as: "0 < m"
  have div_le:"a div m \<le> b div m"
    using le_as by (simp only: div_le_mono)
  thm mod_div_equality[of b m]
  have "b - a = b div m * m + b mod m - (a div m * m + a mod m)"
    by simp
  also have "\<dots> = b div m * m + b mod m - a div m * m - a mod m"
    by simp
  also have "\<dots> = b div m * m - a div m * m + b mod m - a mod m"
    thm mult_le_mono1[OF div_le]
    thm diff_add_assoc2[OF mult_le_mono1[OF div_le]]
    by (simp only: diff_add_assoc2[OF mult_le_mono1[OF div_le]])
  finally have b_a_s1: "b - a = (b div m - a div m) * m + b mod m - a mod m"
    (is "?b_a = ?b_a1")
    by (simp only: diff_mult_distrib)
  thm b_a_s1
  hence b_a_div_s: "(b - a) div m = 
    ((b div m - a div m) * m + b mod m - a mod m) div m"
    by (rule arg_cong)
  
  show ?thesis
  proof (cases "a mod m \<le> b mod m")
    case True
    hence as': "a mod m \<le> b mod m" .
    
    have "(b - a) div m = ?b_a1 div m" 
      using b_a_div_s .
    also have "\<dots> = ((b div m - a div m) * m + (b mod m - a mod m)) div m"
      using as' by simp
    thm div_add1_eq
    also have "\<dots> = b div m - a div m + (b mod m - a mod m) div m"
      thm div_mult_self1
      apply (simp only: add_commute)
      thm less_imp_neq[OF m_as, THEN not_sym]
      thm div_mult_self1[OF less_imp_neq[OF m_as, THEN not_sym]]
      by (simp only: div_mult_self1[OF less_imp_neq[OF m_as, THEN not_sym]])
    finally have b_a_div_s': "(b - a) div m = \<dots>" .
    have "(b mod m - a mod m) div m = 0"
      by (rule div_less, rule less_imp_diff_less, 
          rule mod_less_divisor, rule m_as)
    thus ?thesis
      using b_a_div_s' as'
      by simp
  next
    case False
    hence as1': "\<not> a mod m \<le> b mod m" .
    hence as': "b mod m < a mod m" by simp

    have a_div_less: "a div m < b div m"
      using le_as as'
      thm le_mod_greater_imp_div_less
      by (blast intro: le_mod_greater_imp_div_less)
    
    have "b div m - a div m = b div m - a div m - (Suc 0 - Suc 0)"
      by simp
    also have "\<dots> = b div m - a div m + Suc 0 - Suc 0"
      by simp
    also have "\<dots> = b div m - a div m - Suc 0 + Suc 0"
      thm a_div_less
      thm a_div_less[THEN zero_less_diff[THEN iffD2]]
      thm a_div_less[THEN zero_less_diff[THEN iffD2],
        THEN Suc_le_eq[THEN iffD2]]
      thm diff_add_assoc2
      by (simp only: diff_add_assoc2
        a_div_less[THEN zero_less_diff[THEN iffD2], THEN Suc_le_eq[THEN iffD2]])
    finally have b_a_div_s': "b div m - a div m = \<dots>" .
    
    have "(b - a) div m = ?b_a1 div m" 
      using b_a_div_s .
    also have "\<dots> = ((b div m - a div m - Suc 0 + Suc 0) * m
      + b mod m - a mod m ) div m"
      using b_a_div_s' by (rule arg_cong)
    also have "\<dots> = ((b div m - a div m - Suc 0) * m
      + Suc 0 * m + b mod m - a mod m ) div m"
      by (simp only: add_mult_distrib)
    also have "\<dots> = ((b div m - a div m - Suc 0) * m
      + m + b mod m - a mod m ) div m"
      by simp
    also have "\<dots> = ((b div m - a div m - Suc 0) * m
      + (m + b mod m - a mod m) ) div m"
      thm diff_add_assoc[of "a mod m" "m + b mod m"]
      thm trans_le_add1[of "a mod m" m, OF mod_le_divisor]
      by (simp only: add_assoc m_as
        diff_add_assoc[of "a mod m" "m + b mod m"]
        trans_le_add1[of "a mod m" m, OF mod_le_divisor])
    also have "\<dots> = b div m - a div m - Suc 0
      + (m + b mod m - a mod m) div m"
      thm div_mult_self1
      thm div_mult_self1[OF less_imp_neq[OF m_as, THEN not_sym]]
      by (simp only: add_commute div_mult_self1[OF less_imp_neq[OF m_as, THEN not_sym]])
    finally have b_a_div_s': "(b - a) div m = \<dots>" .
    
    have div_0_s: "(m + b mod m - a mod m) div m = 0"
      thm add_diff_less
      by (rule div_less, simp only: add_diff_less m_as as') 
    show ?thesis
      by (simp add: as1' b_a_div_s' div_0_s)
  qed
qed

thm div_diff1_eq_if
corollary div_diff1_eq: "
  (b - a) div (m::nat) = 
  b div m - a div m - (m + a mod m - Suc (b mod m)) div m"
apply (case_tac "m = 0", simp)
apply (simp only: neq0_conv)
thm div_diff1_eq_if
thm subst[of 
  "if a mod m \<le> b mod m then 0 else Suc 0"
  "(m + a mod m - Suc(b mod m)) div m"]
apply (rule subst[of 
  "if a mod m \<le> b mod m then 0 else Suc 0"
  "(m + a mod m - Suc(b mod m)) div m"])
 prefer 2 apply (rule div_diff1_eq_if)
apply (split split_if, rule conjI)
 apply simp
apply (clarsimp simp: linorder_not_le)
apply (rule sym)

thm Suc_le_eq[of "b mod m", THEN iffD2]
apply (drule Suc_le_eq[of "b mod m", THEN iffD2])
apply (simp only: diff_add_assoc)
apply (simp only: div_add_self1)
apply (simp add: less_imp_diff_less)
done

corollary div_diff1_eq1: "
  a mod m \<le> b mod m \<Longrightarrow> 
  (b - a) div (m::nat) = b div m - a div m"
by (simp add: div_diff1_eq_if)
corollary div_diff1_eq1_mod_0: "
  a mod m = 0 \<Longrightarrow>
  (b - a) div (m::nat) = b div m - a div m"
by (simp add: div_diff1_eq1)
corollary div_diff1_eq2: "
  b mod m < a mod m \<Longrightarrow> 
  (b - a) div (m::nat) = b div m - Suc (a div m)"
by (simp add: div_diff1_eq_if)



subsection {* Further results about @{text div} and @{text mod}*}

subsubsection {* Some auxiliary facts about @{text mod} *}



lemma diff_less_divisor_imp_sub_mod_eq: "
  \<lbrakk> (x::nat) \<le> y; y - x < m \<rbrakk> \<Longrightarrow> x = y - (y - x) mod m"
by simp
lemma diff_ge_divisor_imp_sub_mod_less: "
  \<lbrakk> (x::nat) \<le> y; m \<le> y - x; 0 < m \<rbrakk> \<Longrightarrow> x < y - (y - x) mod m"
apply (simp only: less_diff_conv)
apply (simp only: le_diff_conv2 add_commute[of m])
apply (rule less_le_trans[of _ "x + m"])
apply simp_all
done
thm
  diff_less_divisor_imp_sub_mod_eq
  diff_ge_divisor_imp_sub_mod_less

lemma le_imp_sub_mod_le: "
  (x::nat) \<le> y \<Longrightarrow> x \<le> y - (y - x) mod m"
apply (case_tac "m = 0", simp_all)
thm
  diff_less_divisor_imp_sub_mod_eq
  diff_ge_divisor_imp_sub_mod_less
apply (case_tac "m \<le> y - x")
thm diff_ge_divisor_imp_sub_mod_less
apply (drule diff_ge_divisor_imp_sub_mod_less[of x y m])
apply simp_all
done

thm mod_diff1_eq
lemma mod_less_diff_mod: "
  \<lbrakk> n mod m < r; r \<le> m; r \<le> (n::nat) \<rbrakk> \<Longrightarrow> 
  (n - r) mod m = m + n mod m - r"
apply (case_tac "r = m")
 thm mod_diff_self2
 apply (simp add: mod_diff_self2)
apply (simp add: mod_diff1_eq[of r n m])
done

lemma mod_0_imp_mod_pred: "
  \<lbrakk> 0 < (n::nat); n mod m = 0 \<rbrakk> \<Longrightarrow> 
  (n - Suc 0) mod m = m - Suc 0"
apply (case_tac "m = 0", simp_all)
thm mod_less_diff_mod[of n m "Suc 0"]
apply (simp only: Suc_le_eq[symmetric])
thm mod_diff1_eq[of "Suc 0" n m]
apply (simp only: mod_diff1_eq)
apply (case_tac "m = Suc 0")
apply simp_all
done

lemma mod_pred: "
  0 < n \<Longrightarrow>
  (n - Suc 0) mod m = (
    if n mod m = 0 then m - Suc 0 else n mod m - Suc 0)"
apply (split split_if, rule conjI)
 apply (simp add: mod_0_imp_mod_pred)
apply clarsimp
apply (case_tac "m = Suc 0", simp)
thm subst[OF Suc0_mod[symmetric], where P="\<lambda>x. x \<le> n mod m"]
apply (frule subst[OF Suc0_mod[symmetric], where P="\<lambda>x. x \<le> n mod m"], simp)
thm mod_diff1_eq1[of "Suc 0" n m]
apply (simp only: mod_diff1_eq1)
thm Suc0_mod
apply (simp add: Suc0_mod)
done
corollary mod_pred_Suc_mod: "
  0 < n \<Longrightarrow> Suc ((n - Suc 0) mod m) mod m = n mod m"
apply (case_tac "m = 0", simp)
apply (simp add: mod_pred)
done
corollary diff_mod_pred: "
  a < b \<Longrightarrow>
  (b - Suc a) mod m = (
    if a mod m = b mod m then m - Suc 0 else (b - a) mod m - Suc 0)"
apply (rule_tac t="b - Suc a" and s="b - a - Suc 0" in subst, simp)
apply (subst mod_pred, simp)
apply (simp add: mod_eq_diff_mod_0_conv)
done
corollary diff_mod_pred_Suc_mod: "
  a < b \<Longrightarrow> Suc ((b - Suc a) mod m) mod m = (b - a) mod m"
apply (case_tac "m = 0", simp)
apply (simp add: diff_mod_pred mod_eq_diff_mod_0_conv)
done

lemma mod_eq_imp_diff_mod_eq_divisor: "
  \<lbrakk> a < b; 0 < m; a mod m = b mod m \<rbrakk> \<Longrightarrow> 
  Suc ((b - Suc a) mod m) = m"
thm mod_eq_imp_diff_mod_0
apply (drule mod_eq_imp_diff_mod_0[of a])
thm iffD2[OF zero_less_diff]
apply (frule iffD2[OF zero_less_diff])
thm mod_0_imp_mod_pred[of "b - a" m]
apply (drule mod_0_imp_mod_pred[of "b-a" m], assumption)
apply simp
done


lemma sub_diff_mod_eq: "
  r \<le> t \<Longrightarrow> (t - (t - r) mod m) mod (m::nat) = r mod m"
by (metis mod_diff_right_eq diff_diff_cancel diff_le_self)

thm diff_mod_le
lemma sub_diff_mod_eq': "
  r \<le> t \<Longrightarrow> (k * m + t - (t - r) mod m) mod (m::nat) = r mod m"
thm diff_mod_le[of t r m]
apply (simp only: diff_mod_le[of t r m, THEN add_diff_assoc, symmetric])
apply (simp add: sub_diff_mod_eq)
done

lemma mod_eq_Suc_0_conv: "Suc 0 < k \<Longrightarrow> ((x + k - Suc 0) mod k = 0) = (x mod k = Suc 0)"
apply (simp only: mod_pred)
apply (case_tac "x mod k = Suc 0")
apply simp_all
done

lemma mod_eq_divisor_minus_Suc_0_conv: "Suc 0 < k \<Longrightarrow> (x mod k = k - Suc 0) = (Suc x mod k = 0)"
by (simp only: mod_Suc, split split_if, fastforce)



subsubsection {* Some auxiliary facts about @{text div} *}

lemma sub_mod_div_eq_div: "((n::nat) - n mod m) div m = n div m"
apply (case_tac "m = 0", simp)
thm mult_div_cancel[of m n, symmetric]
apply (simp add: mult_div_cancel[symmetric])
done

thm split_div_lemma
lemma mod_less_imp_diff_div_conv: "
  \<lbrakk> n mod m < r; r \<le> m + n mod m\<rbrakk> \<Longrightarrow> (n - r) div m = n div m - Suc 0"
apply (case_tac "m = 0", simp)
apply (simp only: neq0_conv)
apply (case_tac "n < m", simp)
apply (simp only: linorder_not_less)
thm split_div_lemma[of m "n div m - Suc 0" "n-r"]
thm iffD1[OF split_div_lemma[of m "n div m - Suc 0" "n-r"], symmetric]
apply (rule iffD1[OF split_div_lemma, symmetric], assumption)
apply (rule conjI)
apply (simp_all add: diff_mult_distrib2 mult_div_cancel)
done

corollary mod_0_le_imp_diff_div_conv: "
  \<lbrakk> n mod m = 0; 0 < r; r \<le> m \<rbrakk> \<Longrightarrow> (n - r) div m = n div m - Suc 0"
thm mod_less_imp_diff_div_conv[of n m r]
by (simp add: mod_less_imp_diff_div_conv)
corollary mod_0_less_imp_diff_Suc_div_conv: "
  \<lbrakk> n mod m = 0; r < m \<rbrakk> \<Longrightarrow> (n - Suc r) div m = n div m - Suc 0"
by (drule mod_0_le_imp_diff_div_conv[where r="Suc r"], simp_all)
corollary mod_0_imp_diff_Suc_div_conv: "
  (n - r) mod m = 0 \<Longrightarrow> (n - Suc r) div m = (n - r) div m - Suc 0"
apply (case_tac "m = 0", simp)
apply (rule_tac t="n - Suc r" and s="n - r - Suc 0" in subst, simp)
apply (rule mod_0_le_imp_diff_div_conv, simp+)
done
corollary mod_0_imp_sub_1_div_conv: "
  n mod m = 0 \<Longrightarrow> (n - Suc 0) div m = n div m - Suc 0"
thm mod_0_less_imp_diff_Suc_div_conv[where r=0]
apply (case_tac "m = 0", simp)
apply (simp add: mod_0_less_imp_diff_Suc_div_conv)
done
corollary sub_Suc_mod_div_conv: "
  (n - Suc (n mod m)) div m = n div m - Suc 0"
apply (case_tac "m = 0", simp)
apply (simp add: mod_less_imp_diff_div_conv)
done





thm Divides.div_le_mono
lemma div_le_conv: "0 < m \<Longrightarrow> n div m \<le> k = (n \<le> Suc k * m - Suc 0)"
apply (rule iffI)
 apply (drule mult_le_mono1[of _ _ m])
 apply (simp only: mult_commute[of _ m] mult_div_cancel)
 apply (drule le_diff_conv[THEN iffD1])
 apply (rule le_trans[of _ "m * k + n mod m"], assumption)
 apply (simp add: add_commute[of m])
 thm diff_add_assoc[OF Suc_leI]
 apply (simp only: diff_add_assoc[OF Suc_leI])
 thm add_le_mono[OF le_refl]
 apply (rule add_le_mono[OF le_refl])
 apply (rule less_imp_le_pred)
 apply (rule mod_less_divisor, assumption)
apply (drule div_le_mono[of _ _ m])
thm mod_0_imp_sub_1_div_conv
apply (simp add: mod_0_imp_sub_1_div_conv)
done

lemma le_div_conv: "0 < (m::nat) \<Longrightarrow> (n \<le> k div m) = (n * m \<le> k)"
apply (rule iffI)
 apply (drule mult_le_mono1[of _ _ m])
 apply (simp add: div_mult_cancel)
apply (drule div_le_mono[of _ _ m])
apply simp
done

lemma less_mult_imp_div_less: "n < k * m \<Longrightarrow> n div m < (k::nat)"
apply (case_tac "k = 0", simp)
apply (case_tac "m = 0", simp)
apply simp
apply (drule less_imp_le_pred[of n])
apply (drule div_le_mono[of _ _ m])
thm mod_0_imp_sub_1_div_conv
apply (simp add: mod_0_imp_sub_1_div_conv)
done

lemma div_less_imp_less_mult: "\<lbrakk> 0 < (m::nat); n div m < k \<rbrakk> \<Longrightarrow> n < k * m"
apply (rule ccontr, simp only: linorder_not_less)
apply (drule div_le_mono[of _ _ m])
apply simp
done

lemma div_less_conv: "0 < (m::nat) \<Longrightarrow> (n div m < k) = (n < k * m)"
apply (rule iffI)
apply (rule div_less_imp_less_mult, assumption+)
apply (rule less_mult_imp_div_less, assumption)
done

lemma div_eq_0_conv: "(n div (m::nat) = 0) = (m = 0 \<or> n < m)"
apply (rule iffI)
 apply (case_tac "m = 0", simp)
 apply (rule ccontr)
 apply (simp add: linorder_not_less)
 apply (drule div_le_mono[of _ _ m])
 apply simp
apply fastforce
done
lemma div_eq_0_conv': "0 < m \<Longrightarrow> (n div (m::nat) = 0) = (n < m)"
by (simp add: div_eq_0_conv)
corollary div_gr_imp_gr_divisor: "x < n div (m::nat) \<Longrightarrow> m \<le> n"
apply (drule gr_implies_gr0, drule neq0_conv[THEN iffD2])
apply (simp add: div_eq_0_conv)
done

lemma mod_0_less_div_conv: "
  n mod (m::nat) = 0 \<Longrightarrow> (k * m < n) = (k < n div m)"
apply (case_tac "m = 0", simp)
apply fastforce
done

lemma add_le_divisor_imp_le_Suc_div: "
  \<lbrakk> x div m \<le> n; y \<le> m \<rbrakk> \<Longrightarrow> (x + y) div m \<le> Suc n"
apply (case_tac "m = 0", simp)
apply (simp only: div_add1_eq_if[of _ x])
apply (drule order_le_less[of y, THEN iffD1], fastforce)
done


text {* List of definitions and lemmas *}

thm
  Divides.mod_less
  Divides.mod_less_divisor
  Divides.mod_le_divisor
  mod_less_dividend
  mod_le_dividend

thm 
  Divides.mult_div_cancel
  mod_0_div_mult_cancel
  div_mult_le
  less_div_Suc_mult
thm
  Suc0_mod
  Suc0_mod_subst
  Suc0_mod_cong
  
thm
  Divides.mod_Suc
thm
  mod_Suc_conv
  
thm
  mod_add
  mod_sub_add
  
thm
  mod_sub_eq_mod_0_conv
  mod_sub_eq_mod_swap
     
thm
  le_mod_greater_imp_div_less  
thm
  mod_diff_right_eq
  mod_eq_imp_diff_mod_eq

thm 
  divisor_add_diff_mod_if
  divisor_add_diff_mod_eq1
  divisor_add_diff_mod_eq2

thm
  mod_add_eq
  mod_add1_eq_if
thm
  mod_diff1_eq_if
  mod_diff1_eq
  mod_diff1_eq1
  mod_diff1_eq2

thm
  Divides.nat_mod_distrib
  int_mod_distrib

thm
  zmod_zminus_eq_conv

thm
  mod_eq_imp_diff_mod_0
  zmod_eq_imp_diff_mod_0

thm
  mod_neq_imp_diff_mod_neq0
  diff_mod_0_imp_mod_eq
  zdiff_mod_0_imp_mod_eq

thm 
  zmod_eq_diff_mod_0_conv
  mod_eq_diff_mod_0_conv
  
thm
  less_mod_eq_imp_add_divisor_le
thm
  mod_add_eq_imp_mod_0
thm 
  mod_eq_mult_distrib
  mod_factor_imp_mod_0
  mod_factor_div
  mod_factor_div_mod
  
  
thm
  Divides.mod_add_self1
  Divides.mod_add_self2
  Divides.mod_mult_self1
  Divides.mod_mult_self2
  
  mod_diff_self1
  mod_diff_self2
  mod_diff_mult_self1
  mod_diff_mult_self2
  
thm
  Divides.div_add_self1
  Divides.div_add_self2
  Divides.div_mult_self1
  Divides.div_mult_self2
  
  div_diff_self1
  div_diff_self2
  div_diff_mult_self1
  div_diff_mult_self2
  
thm
  le_less_imp_div
  div_imp_le_less
thm
  le_less_div_conv
  
thm
  diff_less_divisor_imp_sub_mod_eq
  diff_ge_divisor_imp_sub_mod_less
  le_imp_sub_mod_le

thm
  sub_mod_div_eq_div
  
thm
  mod_less_imp_diff_div_conv
  mod_0_le_imp_diff_div_conv
  mod_0_less_imp_diff_Suc_div_conv
  mod_0_imp_sub_1_div_conv
  
  
thm
  sub_Suc_mod_div_conv
  
thm
  mod_less_diff_mod
  mod_0_imp_mod_pred

thm
  mod_pred
  mod_pred_Suc_mod
  
thm
  mod_eq_imp_diff_mod_eq_divisor
  
thm
  diff_mod_le
  sub_diff_mod_eq
  sub_diff_mod_eq'
  
thm
  Divides.div_add1_eq
  div_add1_eq_if
  div_add1_eq1
  div_add1_eq2
thm  
  div_diff1_eq_if
  div_diff1_eq
  div_diff1_eq1
  div_diff1_eq2
  

thm 
  div_le_conv

end