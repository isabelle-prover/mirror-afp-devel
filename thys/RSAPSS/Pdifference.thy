(*  Title:      RSAPSS/Pdifference.thy
    ID:         $Id: Pdifference.thy,v 1.1 2005-05-10 16:13:45 nipkow Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)
header "Positive differences"

theory Pdifference
imports Primes Mod
begin

consts pdifference:: "nat * nat => nat"
recdef pdifference "measure (% (a, b). a)"
  "pdifference (a,b) = (if a < b then (b-a)
                       else (a-b))"

lemma timesdistributesoverpdifference: "m*(pdifference (a,b)) = pdifference ((m*(a::nat)), (m* (b::nat)))"
  apply (auto);
  apply (induct_tac m);
  apply (auto);
  apply (induct_tac m);
  by (auto)

lemma addconst: "a = (b::nat) \<Longrightarrow> c+a = c+b"
  by (auto)

lemma invers: "\<lbrakk>a \<le> x \<rbrakk> \<Longrightarrow> (x::nat) = x - a + a"
  by (auto)

lemma invers2: "\<lbrakk>a \<le> b;(b-a) = p*q\<rbrakk> \<Longrightarrow> (b::nat) = a+p*q"
  apply (subst addconst [THEN sym]);
  apply (assumption);
  by (subst add_commute, rule invers, simp);

lemma modadd: "\<lbrakk>b = a+p*q\<rbrakk> \<Longrightarrow> (a::nat) mod p = b mod p"
  by (auto)

lemma equalmodstrick1: "pdifference (a,b) mod p = 0 \<Longrightarrow> a mod p = b mod p"
  apply (case_tac "a < b");
  apply (auto);
  apply (rule modadd, rule invers2, auto);
  apply (rule sym);
  by (rule modadd, rule invers2, auto);

lemma diff_add_assoc: "\<lbrakk>b \<le> c\<rbrakk> \<Longrightarrow> c - (c - b) = c - c + (b::nat)"
  by (auto)

lemma diff_add_assoc2: "[|a <= c|] ==> c - (c - a + b) = (c - c + (a::nat) - b)"
  apply (subst diff_diff_left [THEN sym])
  apply (subst diff_add_assoc);
  by (auto)

lemma diff_add_diff [rule_format]: "(x \<le> b) \<longrightarrow> (b::nat) - x + y - b = y - x"
  apply (induct_tac b)
  by (auto)

lemma equalmodstrick2: "a mod p = b mod p \<Longrightarrow>  pdifference (a,b) mod p = 0"
  apply (auto);
  apply (drule mod_eqD [simplified], auto)
  apply (subst mod_div_equality' [of b])
  apply (subst diff_add_assoc2);
  apply (subst mult_commute, subst mult_div_cancel);
  apply (simp)+
  apply (subst diff_mult_distrib [THEN sym])
  apply (simp)
  apply (drule mod_eqD [simplified], auto)
  apply (subst mod_div_equality' [of b])
  apply (subst diff_add_diff)
  apply (subst mult_commute, subst mult_div_cancel, auto);
  apply (subst diff_mult_distrib [THEN sym])
  by (simp add: mod_mult_self_is_0)

lemma primekeyrewrite: "\<lbrakk>p:prime;p dvd (a*b);~(p dvd a)\<rbrakk> \<Longrightarrow> p dvd b"
  apply (drule prime_dvd_mult)
  by (auto)

lemma multzero: "\<lbrakk>0 < m mod p; m*a = 0\<rbrakk> \<Longrightarrow> (a::nat) = 0"
  by (auto)

lemma primekeytrick: "\<lbrakk>(M*A) mod P = (M*B) mod P;M mod P \<noteq> 0;P:prime\<rbrakk> \<Longrightarrow> A mod P = (B::nat) mod P"
  apply (drule equalmodstrick2);
  apply (rule equalmodstrick1);
  apply (rule multzero, simp);
  apply (subst mod_mult_distrib2)
  apply (subst timesdistributesoverpdifference);
  apply (simp)
  apply (rule conjI, rule impI, simp)
  apply (subst diff_mult_distrib2 [THEN sym])
  apply (simp add: dvd_eq_mod_eq_0 [THEN sym])
  apply (rule mult_dvd_mono, simp)
  apply (rule primekeyrewrite, simp)
  apply (subst diff_mult_distrib2)
  apply (simp add: dvd_eq_mod_eq_0)+
  apply (rule impI, simp)
  apply (subst diff_mult_distrib2 [THEN sym])
  apply (simp add: dvd_eq_mod_eq_0 [THEN sym])
  apply (rule mult_dvd_mono, simp)
  apply (rule primekeyrewrite);
  by (simp add: dvd_eq_mod_eq_0 diff_mult_distrib2)+

end
