(*  Title:      RSAPSS/Fermat.thy
    ID:         $Id: Fermat.thy,v 1.9 2008-07-10 21:20:00 makarius Exp $
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

header "Fermats little theorem"

theory Fermat
imports Pigeonholeprinciple
begin

primrec pred:: "nat \<Rightarrow> nat"
where
  "pred 0 = 0"
| "pred (Suc a) = a"

primrec S :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list"
where
  "S 0 M P = []"
| "S (Suc N) M P = (M * Suc N) mod P # S N M P"

lemma remaindertimeslist: "timeslist (S n M p) mod p = fac n * M ^ n mod p"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n) then show ?case
    apply auto
    apply (simp add: add_mult_distrib)
    apply (simp add: mult_assoc [symmetric])
    apply (subst add_mult_distrib [symmetric])
    apply (subst mult_assoc)
    apply (subst mult_left_commute)
    apply (subst add_mult_distrib2 [symmetric])
    apply (simp add: mult_assoc)
    apply (subst mult_left_commute)
    apply (simp add: mult_commute [of M])
    apply (subst mod_mult1_eq' [of "M + n * M"])
    apply (erule remainderexplemma)
    done
qed

lemma sucassoc: "(P + P*w) = P * Suc w"
  by auto

lemma modI: "0 < (x::nat) mod p \<Longrightarrow> 0 < x"
  by (induct x) auto

lemma delmulmod: "\<lbrakk>0 < x mod p;a < (b::nat)\<rbrakk> \<Longrightarrow> x*a < x*b"
  apply (simp, rule modI, simp)
  done

lemma swaple: "(c < b) \<Longrightarrow> ((a::nat) \<le>  b - c) \<Longrightarrow> c \<le> b - a"
  by arith

lemma exchgmin: "\<lbrakk>(a::nat) < b;c \<le> a-b\<rbrakk> \<Longrightarrow> c \<le> a - a"
  by auto

lemma sucleI: "Suc x \<le> 0 \<Longrightarrow> False"
  by auto

lemma diffI: "(0::nat) = b - b"
  by auto

lemma alldistincts: "prime p \<Longrightarrow> (m mod p \<noteq> 0) \<Longrightarrow> (n2 < n1) \<Longrightarrow> (n1 < p) \<Longrightarrow>
    \<not>(((m*n1) mod p) mem (S n2 m p))"
  apply (induct n2)
   apply auto
  apply (drule equalmodstrick2)
  apply (subgoal_tac "m+m*n2 < m*n1")
   apply auto
   apply (drule dvdI)
   apply (simp only: sucassoc diff_mult_distrib2[symmetric])
  apply (drule primekeyrewrite, simp)
    apply (simp add: dvd_eq_mod_eq_0)
   apply (drule_tac n = "n1 - Suc n2" in dvd_imp_le, simp)
   apply (rule sucleI, subst diffI [of n1])
   apply (rule exchgmin, simp)
   apply (rule swaple, auto)
  apply (subst sucassoc)
  apply (rule delmulmod)
   apply auto
  done

lemma alldistincts2: "prime p \<Longrightarrow> m mod p \<noteq> 0 \<Longrightarrow> n < p \<Longrightarrow> alldistinct (S n m p)"
  apply (induct n)
   apply (simp)+
  apply (subst sucassoc)
  apply (rule alldistincts)
     apply auto
  done

lemma notdvdless: "\<not> a dvd b \<Longrightarrow> 0 < (b::nat) mod a"
  apply (rule contrapos_np, simp)
  apply (simp add: dvd_eq_mod_eq_0)
  done

lemma allnonzerop: "prime p \<Longrightarrow> m mod p \<noteq> 0 \<Longrightarrow> n < p \<Longrightarrow> allnonzero (S n m p)"
  apply (induct n)
   apply simp+
  apply (subst sucassoc)
  apply (rule notdvdless)
  apply clarify
  apply (drule primekeyrewrite)
    apply assumption
   apply (simp add: dvd_eq_mod_eq_0)
  apply (drule_tac n = "Suc n" in dvd_imp_le)
   apply auto
  done

lemma predI: "a < p \<Longrightarrow> a \<le> pred p"
  by (induct p) auto

lemma predd: "pred p = p - (1::nat)"
  by (induct p) auto

lemma alllesseqps: "p \<noteq> 0 \<Longrightarrow> alllesseq (S n m p) (pred p)"
  by (induct n) (auto simp add: predI mod_less_divisor)

lemma lengths: "length (S n m p) = n"
  by (induct n) auto

lemma suconeless: "prime p \<Longrightarrow> p - 1 < p"
  by (induct p) (auto simp add: prime_def)

lemma primenotzero: "prime p \<Longrightarrow> p \<noteq> 0"
  by (auto simp add: prime_def)

lemma onemodprime: "prime p \<Longrightarrow> 1 mod p = (1::nat)"
  by (induct p) (auto simp add: prime_def)

lemma fermat: "\<lbrakk>prime p; m mod p \<noteq> 0\<rbrakk> \<Longrightarrow> m^(p-(1::nat)) mod p = 1"
  apply (frule onemodprime[symmetric], simp)
  apply (frule_tac n ="p- Suc 0" in primefact)
  apply (drule suconeless, simp)
  apply (erule ssubst)
  back
  apply (rule_tac M = "fac (p - Suc 0)" in primekeytrick)
  apply (subst remaindertimeslist [of "p - Suc 0" m p, symmetric])
  apply (frule_tac n = "p-(1::nat)" in alldistincts2, simp)
  apply (rule suconeless, simp)
  apply (frule_tac n = "p-(1::nat)" in allnonzerop, simp)
  apply (rule suconeless, simp)
  apply (frule primenotzero)
  apply (frule_tac n = "p-(1::nat)" and m = m and p = p in alllesseqps)
  apply (frule primenotzero)
  apply (simp add: predd)
  apply (insert lengths[of "p-Suc 0" m p, symmetric])
  apply (insert pigeonholeprinciple [of "S (p-Suc 0) m p"])
  apply (auto)
  apply (drule permtimeslist)
  apply (simp add: timeslistpositives) 
  done

end
