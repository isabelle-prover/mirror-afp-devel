(*  Title:      RSAPSS/Fermat.thy
    ID:         $Id: Fermat.thy,v 1.8 2008-06-12 06:57:26 lsf37 Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Fermats little theorem"

theory Fermat
imports Pigeonholeprinciple
begin

primrec pred:: "nat \<Rightarrow> nat" where
  "pred 0 = 0"
  | "pred (Suc a) = a"

primrec S :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "S 0 M P = []"
  | "S (Suc N) M P = (M * Suc N) mod P # S N M P"

lemma remaindertimeslist: "timeslist (S n M p) mod p = fac n * M ^ n mod p"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n) then show ?case
  apply (auto)
  apply (simp add: add_mult_distrib)
  apply (simp add: mult_assoc [THEN sym])
  apply (subst add_mult_distrib [THEN sym])
  apply (subst mult_assoc)
  apply (subst mult_left_commute)
  apply (subst add_mult_distrib2 [THEN sym])
  apply (simp add: mult_assoc)
  apply (subst mult_left_commute)
  apply (simp add: mult_commute [of M])
  apply (subst mod_mult1_eq' [of "M + n * M"])
  apply (erule remainderexplemma)
  done
qed
lemma sucassoc: "(P + P*w) = P * Suc w"
  by (auto)

lemma modI[rule_format]: "0 < (x::nat) mod p \<longrightarrow> 0 < x"
  by (induct_tac x, auto)

lemma delmulmod: "\<lbrakk>0 < x mod p;a < (b::nat)\<rbrakk> \<Longrightarrow> x*a < x*b"
  by (simp, rule modI, simp)

lemma swaple[rule_format]: "(c < b) \<longrightarrow> ((a::nat) \<le>  b - c) \<longrightarrow> c \<le> b - a"
  by arith

lemma exchgmin: "\<lbrakk>(a::nat) < b;c \<le> a-b\<rbrakk> \<Longrightarrow> c \<le> a - a"
  by (auto)

lemma sucleI: "Suc x \<le> 0 \<Longrightarrow> False"
  by (auto)

lemma diffI: "\<And>b. (0::nat) = b - b"
  by (auto)

lemma alldistincts[rule_format]: "prime p \<longrightarrow> (m mod p \<noteq> 0) \<longrightarrow> (n2 < n1) \<longrightarrow> (n1 < p) --> \<not>(((m*n1) mod p) mem (S n2 m p))"
  apply (induct n2)
  apply (auto)
  apply (drule equalmodstrick2)
  apply (subgoal_tac "m+m*n2 < m*n1")
  apply (auto)
  apply (drule dvdI)
  apply (simp only: sucassoc diff_mult_distrib2[THEN sym])
  apply (drule primekeyrewrite, simp)
  apply (simp add: dvd_eq_mod_eq_0)
  apply (drule_tac n="n1 - Suc n2" in dvd_imp_le, simp)
  apply (rule sucleI, subst diffI [of n1])
  apply (rule exchgmin, simp)
  apply (rule swaple, auto)
  apply (subst sucassoc)
  apply (rule delmulmod)
  by (auto)

lemma alldistincts2[rule_format]: "prime p \<longrightarrow> (m mod p \<noteq> 0) \<longrightarrow> (n < p) \<longrightarrow> alldistinct (S n m p)"
  apply (induct n)
  apply (simp)+
  apply (subst sucassoc)
  apply (rule impI)+
  apply (rule alldistincts)
  by (auto)

lemma notdvdless: "\<not> a dvd b \<Longrightarrow> 0 < (b::nat) mod a"
  apply (rule contrapos_np, simp)
  by (simp add: dvd_eq_mod_eq_0)

lemma allnonzerop[rule_format]: "prime p \<longrightarrow> (m mod p \<noteq> 0) \<longrightarrow> (n < p) \<longrightarrow> allnonzero (S n m p)"
  apply (induct n)
  apply (simp)+
  apply (auto)
  apply (subst sucassoc)
  apply (rule notdvdless)
  apply (clarify)
  apply (drule primekeyrewrite)
  apply (assumption)
  apply (simp add: dvd_eq_mod_eq_0)
  apply (drule_tac n="Suc n" in dvd_imp_le)
  by (auto)

lemma predI[rule_format]: "a < p \<longrightarrow> a \<le> pred p"
  apply (induct_tac p)
  by (auto)

lemma predd: "pred p = p-(1::nat)"
  apply (induct_tac p)
  by (auto)

lemma alllesseqps[rule_format]: "p \<noteq> 0 \<longrightarrow> alllesseq (S n m p) (pred p)"
  apply (induct n)
  apply (auto)
  by (simp add: predI mod_less_divisor)

lemma lengths: "length (S n m p) = n"
  apply (induct n)
  by (auto)

lemma suconeless[rule_format]: "prime p \<longrightarrow> p - 1 < p"
  apply (induct_tac p)
  by (auto simp add:prime_def)

lemma primenotzero: "prime p \<Longrightarrow> p\<noteq>0"
  by (auto simp add:prime_def)

lemma onemodprime[rule_format]: "prime p \<longrightarrow> 1 mod p = (1::nat)"
  apply (induct_tac p)
  by (auto simp add:prime_def)

lemma fermat:"\<lbrakk>prime p; m mod p \<noteq> 0\<rbrakk> \<Longrightarrow> m^(p-(1::nat)) mod p = 1"
  apply (frule onemodprime[THEN sym], simp)
  apply (frule_tac n ="p- Suc 0" in primefact)
  apply (drule suconeless, simp)
  apply (erule ssubst)
  back
  apply (rule_tac M = "fac (p - Suc 0)" in primekeytrick)
  apply (subst remaindertimeslist [of "p - Suc 0" m p, THEN sym])
  apply (frule_tac n = "p-(1::nat)" in alldistincts2, simp)
  apply (rule suconeless, simp)
  apply (frule_tac n = "p-(1::nat)" in allnonzerop, simp)
  apply (rule suconeless, simp)
  apply (frule primenotzero)
  apply (frule_tac n = "p-(1::nat)" and m = m and p = p in alllesseqps)
  apply (frule primenotzero)
  apply (simp add: predd)
  apply (insert lengths[of "p-Suc 0" m p, THEN sym])
  apply (insert pigeonholeprinciple [of "S (p-Suc 0) m p"])
  apply (auto)
  apply (drule permtimeslist)
  by (simp add: timeslistpositives) 

end
