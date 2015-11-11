theory Table
imports Amor
begin

fun nxt3\<^sub>t\<^sub>b :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*nat \<Rightarrow> nat*nat" where
"nxt3\<^sub>t\<^sub>b Ins (n,l) = (n+1, if l=0 then 2 else if 10*(n+1)\<le>9*l then l else 3*l)" |
"nxt3\<^sub>t\<^sub>b Del (n,l) = (n-1, if n=1 then 0 else if 10*(n-1)<l then l div 3 else l)"

fun t3\<^sub>t\<^sub>b :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*nat \<Rightarrow> real" where
"t3\<^sub>t\<^sub>b Ins (n,l) = (if l=0 then 1 else if 10*(n+1)\<le>9*l then 1 else n+1)" |
"t3\<^sub>t\<^sub>b Del (n,l) = (if n=1 then 1 else if 10*(n-1)<l then n else 1)"

interpretation tb3: amor
where init = "(0,0)" and nxt = nxt3\<^sub>t\<^sub>b
and inv = "\<lambda>(n,l). 10*n \<le> 9 * l"
and t = t3\<^sub>t\<^sub>b and \<Phi> = "\<lambda>(n,l). if n < 0.3 * l then 1/2*(0.3*l - n) else 3/2*(n - 0.3*l)"
and U = "\<lambda>f _. case f of Ins \<Rightarrow> 5/2 | Del \<Rightarrow> 3/2"
proof
  case goal1 show ?case by auto
next
  case goal2 thus ?case by(cases s, cases f) (auto split: if_splits)
next
  case goal3 thus ?case by(cases s)(simp split: if_splits)
next
  case goal4 show ?case by(simp)
next
  case goal5 thus ?case apply(cases s) apply(cases f)
    by (auto simp: field_simps of_nat_Suc)
qed

locale Table =
fixes f1 f2 ai ad :: real and m l0 :: nat
assumes m1[arith]: "m > 1"
assumes f1[arith]: "f1 > 0"
assumes l0f1: "f1*l0 \<le> 1" (* (1,l0) no uflow *)
assumes adai: "ad*(f2*l0/m - 1) \<le> ai" (* \<Longrightarrow> l0 \<ge> m/f2 *)
assumes ai: "ai \<ge> m/(m-1)"
assumes f1f2mm: "f1 \<le> f2/(m*m)"
assumes ad: "ad \<ge> 1/(m-1)"
assumes l0f1m: "l0 \<ge> 1/(f1*(m - 1))"
begin

lemma f2[arith]: "0 < f2"
using f1f2mm zero_less_divide_iff[of f2 "m*m"] by simp

lemma f1f2m: "f1 < f2/m"
using mult_less_le_imp_less[of 1 "real m", OF _ f1f2mm _ f1] by simp

definition [simp]: "f2' == f2/m"

lemma ai0[arith]: "ai \<ge> 0"
using order_trans[OF divide_nonneg_nonneg ai] by simp

lemma ad0[arith]: "ad \<ge> 0"
by(rule order_trans[OF _ ad]) simp

lemma l0f2m: "l0 \<ge> 1/f2 * (m/(m-1))"
proof -
  have "1/(f1*(m - 1)) \<ge> 1/f2 * (m/(m-1))"
  using f1f2m by(simp add: field_simps)
  thus ?thesis using l0f1m by linarith
qed

lemma l0f2: "1 \<le> f2 * l0"
proof-
  have "m/(m-1) \<ge> 1" by(simp)
  from mult_left_mono[OF this, of "1/f2"]
  have "1/f2 \<le> 1/f2 * (m/(m-1))" by(simp)
  with l0f2m have "1/f2 \<le> l0" by linarith
  thus ?thesis by (simp add: field_simps)
qed

lemma l0_gr0[arith]: "l0 > 0"
using l0f2 zero_less_mult_iff[of f2 l0]
by(simp)

fun nxt\<^sub>t\<^sub>b :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*nat \<Rightarrow> nat*nat" where
"nxt\<^sub>t\<^sub>b Ins (n,l) =
 (n+1, if l=0 then l0 else if n+1 \<le> f2*l then l else m*l)" |
"nxt\<^sub>t\<^sub>b Del (n,l) =
 (n-1, if n\<le>1 then 0 else if f1*l \<le> n-1 then l else l div m)"

fun t\<^sub>t\<^sub>b :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*nat \<Rightarrow> real" where
"t\<^sub>t\<^sub>b Ins (n,l) = (if l=0 then 1 else if n+1 \<le> f2*l then 1 else n+1)" |
"t\<^sub>t\<^sub>b Del (n,l) = (if n\<le>1 then 1 else if f1*l \<le> n-1 then 1 else n)"


lemma Ins_no_oflow:
assumes "l \<ge> 1/f2 * (m/(m-1))" "n \<le> f2' * l"
shows "n+1 \<le> f2*l"
proof -
  have "f2' * l + 1 \<le> f2*l" using assms(1)
    by(simp add: field_simps of_nat_diff)
  with assms(2) show ?thesis by arith
qed

lemma Ins_no_oflow2:
assumes "l \<ge> 1/f2 * (m/(m-1))" "n+1 > f2 * l"
shows "n > f2'*l"
proof -
  have "f2' * l + 1 \<le> f2*l" using assms(1)
    by(simp add: field_simps of_nat_diff)
  with assms(2) show ?thesis by arith
qed

lemma Del_no_uflow: assumes "l \<ge> 1/(f2' - f1)" "f2' * l \<le> n" shows "f1*l \<le> n-1"
proof -
  have f1f2': "f1 < f2'" using f1f2m by simp
  thus ?thesis using assms by(simp add: field_simps del: f2'_def)
qed

interpretation tb: amor
where init = "(0,0)" and nxt = nxt\<^sub>t\<^sub>b
and inv = "\<lambda>(n,l). if l=0 then n=0 else (EX k. l = l0 * m^k) \<and> f1*l \<le> n \<and> n \<le> f2*l"
and t = t\<^sub>t\<^sub>b and \<Phi> = "\<lambda>(n,l). if n \<ge> f2'*l then ai*(n - f2'*l) else ad*(f2'*l - n)"
and U = "\<lambda>f _. case f of Ins \<Rightarrow> ai+1 | Del \<Rightarrow> ad+1"
proof
  case goal1 show ?case by auto
next
  case goal2
  obtain n l where [simp]: "s = (n,l)" by fastforce
  show ?case
  proof (cases f)
    case [simp]: Ins
    show ?thesis
    proof cases
      assume "l = 0" with goal2 l0f1 l0f2 show ?thesis
        by(auto simp: field_simps) (metis One_nat_def power_0)
    next
      assume [arith]: "l \<noteq> 0"
      hence "l \<ge> l0" using goal2 by auto
      from goal2 have "n \<le> f2*l" by auto
      show ?thesis
      proof cases
        assume "n+1 \<le> f2*l" thus ?thesis using goal2 by (auto)
      next
        assume 0: "\<not> n+1 \<le> f2*l"
        have "f1*m < f2" using f1f2m by(simp add: field_simps)
        have 1: "\<exists>k. m*l = l0 * m ^ k"
          using goal2 by auto (metis power_add power_one_right)
        have 2: "f1 * (m*l) \<le> n+1"
        proof -
          have "f1 * (m*l) \<le> f2*l" using `f1*m < f2` by simp
          with 0 show ?thesis by linarith
        qed
        have "l \<ge> 1/f2 * (m/(m-1))" using l0f2m `l \<ge> l0` by linarith
        hence "f2*l + 1 \<le> f2 * (m*l)"
          by(simp add: field_simps of_nat_Suc of_nat_diff)
        hence "n+1 \<le> f2 * (m*l)" using `n \<le> f2*l` by linarith
        with 0 1 2 `l \<noteq> 0` show ?thesis by simp
      qed
    qed
  next
    case [simp]: Del
    show ?thesis
    proof cases
      assume "n \<le> 1" with goal2 show ?thesis by(auto)
    next
      assume [arith]: "\<not> n \<le> 1"
      hence "l \<noteq> 0" and "f1*l \<le> n" using goal2 by (auto split: if_splits)
      show ?thesis
      proof cases
        assume "f1*l \<le> real n - 1"
        thus ?thesis using goal2 by(auto split: if_splits)
      next
        assume 0: "\<not> f1*l \<le> real n - 1"
        obtain k where l: "l = l0 * m^k" using goal2 by (auto split: if_splits)
        have "l \<noteq> l0" using goal2 apply auto using 0 l0f1 by auto
        hence "k > 0" using goal2 l by (auto split: if_splits)
        then obtain k0 where k: "k = Suc k0" by(auto simp: gr0_conv_Suc) 
        hence 1: "l div m = l0 * m ^ k0" using goal2 l by (auto)
        have "m dvd l" using k l by simp
        have 2: "f1 * (l div m) \<le> n - 1"
        proof -
          have "l \<ge> l0 * m" using k l by simp
          hence "l/m \<ge> l0"
            by(simp add: field_simps) (metis of_nat_le_iff of_nat_mult)
          hence 3: "1 / (f1 * (m - 1)) \<le> l/m" using l0f1m by linarith
          have "f1 * (l div m) = f1 * l / m"
            by(simp add: real_of_nat_div[OF `m dvd l`])
          also have "\<dots> \<le> f1*l - 1"
            using 3 by(simp add: field_simps of_nat_diff)
          finally show ?thesis using `f1*l \<le> n` by linarith
        qed
        have "n - 1 \<le> f2 * (l div m)"
        proof -
          have "f1*l \<le> f2*l/m" using `l \<noteq> 0` f1f2m by (simp add: field_simps)
          also have "\<dots> = f2*(l div m)" by(simp add: real_of_nat_div[OF `m dvd l`])
          finally show ?thesis using 0 by linarith
        qed
        with 0 1 2 show ?thesis by auto
      qed
    qed
  qed
next
  case goal3 thus ?case by(cases s)(simp split: if_splits)
next
  case goal4 show ?case by(simp)
next
  case goal5
  obtain n l where [simp]: "s = (n,l)" by fastforce
  show ?case
  proof (cases f)
    case [simp]: Ins
    show ?thesis
    proof cases
      assume "l = 0" with goal5 adai show ?thesis
        by(auto simp: field_simps)
    next
      assume [simp]: "l \<noteq> 0"
      hence "l \<ge> l0" using goal5 by auto
      show ?thesis
      proof cases
        assume "n+1 \<le> f2*l" thus ?thesis
          apply (auto simp add: algebra_simps of_nat_Suc not_le)
          apply(rule add_mono)
          apply(drule mult_left_mono[OF less_imp_le ad0])
          apply simp
          apply(drule mult_left_mono[OF less_imp_le ai0])
          by simp
      next
        assume [arith]: "\<not> n+1 \<le> f2*l"
        hence "real n + 1 > f2*l" by linarith
        have 0: "real m * real n \<le> f2 * (real l * real m)"
          using goal5 by(simp)
        have "1 / f2 * (m / (m - 1)) \<le> l" using `l \<ge> l0` l0f2m by linarith
        from Ins_no_oflow2[OF this `real n + 1 > f2*l`]
        have "n > f2'*l" .
        thus ?thesis using ai
apply(simp add: algebra_simps of_nat_Suc of_nat_diff)
apply(simp add: field_simps)
apply(drule mult_left_mono[of _ _ "f2 * real l"])
apply simp
apply(simp add: field_simps)
using 0 by linarith
      qed
    qed
  next
    case [simp]: Del
    show ?thesis
    proof cases
      assume "n \<le> 1" with goal5 ad0 show ?thesis
        apply(auto simp: field_simps not_le split: if_splits)
        apply (metis ad0 ai0 add.commute add_increasing2 mult_left_mono mult_nonneg_nonneg of_nat_0_le_iff)
        by (metis (no_types) distrib_left dual_order.order_iff_strict le_add_same_cancel2 mult_left_mono[OF _ ad0] order_trans of_nat_0_le_iff)
    next
      assume [arith]: "\<not> n \<le> 1"
      hence "l \<ge> l0" and "f1*l \<le> n" using goal5 by (auto split: if_splits)
      hence "l > 0" by linarith
      show ?thesis
      proof cases
        assume "n < f2'*l"
        show ?thesis
        proof cases
          assume "real n - 1 \<ge> f1*l"
          thus ?thesis using `n < f2'*l`
            by(simp add: algebra_simps of_nat_diff)
        next
          assume 0[arith]: "\<not> real n - 1 \<ge> f1*l"
          hence 1: "real n - 1 < f2/(m*m)*l"
            using mult_right_mono[OF f1f2mm of_nat_0_le_iff[of l]] by simp
          have "l \<noteq> l0" using goal5 apply auto using 0 l0f1 by auto
          hence "m dvd l" using goal5 by (auto split: if_splits)
          show ?thesis (is "?l \<le> ?r")
          proof -
            have "?l = n + ad + - ad*(f2'*l*((m-1)/m))" using 1 `n < f2'*l`
              by(simp add: field_simps of_nat_diff real_of_nat_div[OF `m dvd l`])
            also have "\<dots> < 1 + ad + f1*l + - (ad*(f2'*l*((m-1)/m)))" by linarith
            also have "- (ad*(f2'*l*((m-1)/m))) \<le> - ((1/(m-1))*(f2'*l*((m-1)/m)))"
              by(rule le_imp_neg_le[OF mult_right_mono[OF ad]]) simp
            also have "1 + ad + f1*l + \<dots> \<le> ad + 1"
              using `l > 0` f1f2mm by(simp add: field_simps)
            finally show ?thesis by fastforce
          qed
        qed
      next
        assume 0[arith]: "\<not> n < f2'*l"
        have "1/(f1*(m - 1)) \<ge> 1/(f2/m - f1)"
          using f1f2m f1f2mm by(simp add: field_simps of_nat_diff)
        hence "l \<ge> 1/(f2' - f1)" using `l \<ge> l0` l0f1m by simp
        from Del_no_uflow[OF this leI[OF `\<not> n < f2'*l`]]
        have [arith]: "real n - 1 \<ge> f1*l" .
        show ?thesis
        proof cases
          assume "real n - 1 \<ge> f2'*l"
          thus ?thesis by(simp add: algebra_simps of_nat_diff)
        next
          assume 1: "\<not> real n - 1 \<ge> f2'*l"
          have 2: "f2'*l - (n-1) \<le> 1" by linarith
          show ?thesis (is "?l \<le> ?r")
          proof -
            have "?l = 1 + ad*(f2'*l - (n-1)) + - (ai*(n - f2'*l))" using 1 2
              by(simp add: of_nat_diff)
            also have "- (ai*(n - f2'*l)) \<le> 0" using ai0 0 by(simp)
            also have "ad*(f2'*l - (n-1)) \<le> ad"
              by(rule mult_left_le[OF 2 ad0])
            finally show ?thesis by fastforce
          qed
        qed
      qed
    qed
  qed
qed

end

text{* In the context below the constraint l0f1 may not be satisfiable
even if l0 is taken to be as small as l0f1m' allows. Example:
m=2, f2=3/4, l0=6 satisfies l0f1m' but not l0f1. As a result the
state (1,6) has a load factor 1/6 which is below the minimal load factor
f1=f2/(m*m) = (3/4)/4 = 3/16

Valid instances:
m=2, f2=0.8 (f1=0.2), l0=4
m=3, f2=0.9, (f1=0.1), l0=10
m=4, f2=1 (f1=1/16), l0=6
*}

locale Table' =
fixes f2 :: real and m l0 :: nat
assumes m1[arith]: "m > 1"
assumes f1[arith]: "f2 > 0"
assumes l0f1: "f2/(m*m)*l0 \<le> 1" (* (1,l0) no uflow *)
assumes l0f1m': "f2*l0 \<ge> (m*m)/(m - 1)"
begin

definition "f1 = f2/(m*m)"
definition "ai = m/(m-1)"
definition "ad = 1/(m-1)"

lemma l0f1m: "l0 \<ge> 1/(f2/(m*m)*(m - 1))"
using l0f1m' by(simp add: field_simps)

interpretation Table
where f1=f1 and f2=f2 and m=m and l0=l0 and ai=ai and ad=ad
proof
  case goal1 show ?case by(rule m1)
  case goal2 show ?case by(simp add: f1_def field_simps)
  case goal3 show ?case using l0f1 by(simp add: f1_def field_simps)
  case goal4 show ?case
    apply (simp add: ad_def ai_def of_nat_diff divide_le_cancel)
    using mult_left_mono[OF l0f1, of m, simplified]
    by (metis diff_0_right diff_mono zero_le_one)
  case goal5 show ?case by(simp add: ai_def)
  case goal6 show ?case by(simp add: f1_def)
  case goal7 show ?case by(simp add: ad_def)
  case goal8 show ?case unfolding f1_def by(rule l0f1m)
qed

end

interpretation I1: Table' where m=2 and f2=1 and l0=4 (* f1=1/4 *)
proof qed simp_all

interpretation I2: Table' where m=2 and f2="0.8" and l0=5 (* f1=1/5 *)
proof qed simp_all

interpretation I3: Table' where m=3 and f2="0.9" and l0=5 (* f1=1/10 *)
proof qed simp_all

interpretation I4: Table' where m=4 and f2=1 and l0=6 (* f1=1/16 *)
proof qed simp_all

end
